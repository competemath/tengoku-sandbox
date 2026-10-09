"""sandbox_selftest.py (docs/agent-security.md): each probe finds what it must deny, and the battery refuses an unsealed step.

The real seal (`unshare --net --pid --fork --mount-proc runuser -u … env -i …`) needs root and a Linux runner: pr-tests.yml runs the
battery inside it on a hosted runner. Here every probe is exercised against a fixture that has what it looks for."""

from __future__ import annotations

import errno
import os
import re
import socket
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from unittest import mock

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))

import sandbox_selftest as st  # noqa: E402


def fake_proc(pids=(1, 2, 3), comm="runuser", environ=b""):
    d = Path(tempfile.mkdtemp())
    for pid in pids:
        (d / str(pid)).mkdir()
    (d / "1" / "comm").write_text(comm + "\n")
    (d / "1" / "environ").write_bytes(environ)
    return str(d)


class Pure(unittest.TestCase):
    def test_status_lines(self):
        s = st.parse_status("Name:\tpython3\nCapEff:\t0000000000000000\nUid:\t1001\t1001\t1001\t1001\n")
        self.assertEqual((s["Name"], int(s["CapEff"], 16)), ("python3", 0))

    def test_environment_names(self):
        self.assertEqual(st.environment_problems(["HOME", "PATH", "LANG"], []), [])
        self.assertEqual(
            st.environment_problems(["HOME", "GITHUB_TOKEN", "ACTIONS_RUNTIME_TOKEN", "RUNNER_TEMP", "BODY"], []),
            ["ACTIONS_RUNTIME_TOKEN", "BODY", "GITHUB_TOKEN", "RUNNER_TEMP"],
        )
        self.assertEqual(st.environment_problems(["HOME", "TENGOKU_CI_ROOT"], ["TENGOKU_CI_ROOT"]), [])
        self.assertEqual(st.environment_problems(["MY_API_KEY"], []), ["MY_API_KEY"])  # not on the list, and named like a credential
        self.assertEqual(st.environ_names(b"A=1\0B=x=y\0\0"), ["A", "B"])


class Network(unittest.TestCase):
    def test_a_reachable_address_is_not_a_seal(self):
        srv = socket.socket()
        srv.bind(("127.0.0.1", 0))
        srv.listen(1)
        threading.Thread(target=lambda: srv.accept()[0].close(), daemon=True).start()
        self.assertIn("connected", st.route_state(srv.getsockname()))
        self.addCleanup(srv.close)
        closed = socket.socket()
        closed.bind(("127.0.0.1", 0))
        port = closed.getsockname()[1]
        closed.close()
        self.assertIn("a route exists", st.route_state(("127.0.0.1", port)))

    def test_only_a_missing_route_counts(self):
        with mock.patch.object(socket.socket, "connect", side_effect=OSError(errno.ENETUNREACH, "Network is unreachable")):
            self.assertEqual(st.route_state(("192.0.2.1", 80)), "none")
            self.assertTrue(st.probe_testnet().ok)
            self.assertTrue(st.probe_metadata().ok)
        with mock.patch.object(socket.socket, "connect", side_effect=socket.timeout()):
            self.assertIn("timed out", st.route_state(("192.0.2.1", 80)))
            probe = st.probe_testnet()
            self.assertFalse(probe.ok)
            self.assertIn("a route exists", probe.detail)
        with mock.patch.object(socket.socket, "connect", side_effect=OSError(errno.EHOSTUNREACH, "No route to host")):
            self.assertFalse(st.probe_testnet().ok)

    def test_a_named_host_that_resolves_and_answers_fails_the_probe(self):
        with mock.patch.object(socket, "getaddrinfo", return_value=[(2, 1, 6, "", ("203.0.113.9", 443))]):
            with mock.patch.object(socket.socket, "connect", return_value=None):
                self.assertFalse(st.probe_named_hosts().ok)
            with mock.patch.object(socket.socket, "connect", side_effect=OSError(errno.ENETUNREACH, "x")):
                self.assertTrue(st.probe_named_hosts().ok)
        with mock.patch.object(socket, "getaddrinfo", side_effect=socket.gaierror()):
            with mock.patch.object(socket.socket, "connect", side_effect=OSError(errno.ENETUNREACH, "x")):
                self.assertTrue(st.probe_named_hosts().ok)


class Processes(unittest.TestCase):
    def test_pid_namespace(self):
        self.assertTrue(st.probe_pid_namespace(fake_proc()).ok)
        self.assertFalse(st.probe_pid_namespace(fake_proc(comm="systemd")).ok)
        self.assertIn("pid 1 is Runner.Worker", st.probe_pid_namespace(fake_proc(comm="Runner.Worker")).detail)
        self.assertIn("40 processes", st.probe_pid_namespace(fake_proc(pids=range(1, 41))).detail)

    def test_pid1_environment(self):
        self.assertTrue(st.probe_pid1_environment([], fake_proc(environ=b"")).ok)
        self.assertTrue(st.probe_pid1_environment([], fake_proc(environ=b"HOME=/h\0PATH=/bin\0")).ok)
        leak = st.probe_pid1_environment([], fake_proc(environ=b"HOME=/h\0GITHUB_TOKEN=ghs_shouldnotbeprinted\0"))
        self.assertFalse(leak.ok)
        self.assertIn("GITHUB_TOKEN", leak.detail)
        self.assertNotIn("shouldnotbeprinted", leak.detail)
        self.assertTrue(st.probe_pid1_environment([], str(Path(tempfile.mkdtemp()))).ok)  # no /proc/1/environ at all: unreadable


class Files(unittest.TestCase):
    def test_writable_system_directories(self):
        d = tempfile.mkdtemp()
        probe = st.probe_write_system((d,))
        self.assertFalse(probe.ok)
        self.assertIn(d, probe.detail)
        self.assertEqual(os.listdir(d), [])  # the probe cleans up
        os.chmod(d, 0o555)
        try:
            if os.geteuid() != 0:
                self.assertTrue(st.probe_write_system((d,)).ok)
        finally:
            os.chmod(d, 0o755)

    def test_runner_command_files(self):
        d = Path(tempfile.mkdtemp()) / "_runner_file_commands"
        d.mkdir()
        self.assertFalse(st.probe_runner_channels((str(d),)).ok)
        self.assertTrue(st.probe_runner_channels((str(d) + "-absent",)).ok)

    def test_a_docker_config_is_a_leak_only_when_it_holds_a_registry_credential(self):
        d = Path(tempfile.mkdtemp())
        cfg = d / "config.json"
        for text, leaks in (
            ('{"auths": {"ghcr.io": {"auth": "dXNlcjpwYXNz"}}}', True),
            ('{"auths": {"ghcr.io": {"identitytoken": "x"}}}', True),
            ('{"auths": {}}', False),
            ('{"auths": {"ghcr.io": {}}, "credsStore": "desktop"}', False),
            ("not json", False),
            ("[]", False),
        ):
            cfg.write_text(text)
            self.assertEqual(st.docker_credentials(str(cfg)), leaks, text)
            self.assertEqual(st.probe_credentials((), str(cfg)).ok, not leaks, text)
        self.assertFalse(st.docker_credentials(str(d / "absent.json")))

    def test_credential_files(self):
        d = Path(tempfile.mkdtemp())
        (d / ".credentials").write_text("x")
        probe = st.probe_credentials((str(d / ".cred*"),), str(d / "no-docker-config.json"))
        self.assertFalse(probe.ok)
        self.assertIn(".credentials", probe.detail)
        self.assertTrue(st.probe_credentials((str(d / "nothing*"),), str(d / "no-docker-config.json")).ok)
        if os.geteuid() != 0:
            (d / ".credentials").chmod(0)
            self.assertTrue(st.probe_credentials((str(d / ".cred*"),), str(d / "no-docker-config.json")).ok)

    def test_a_container_socket_that_accepts_a_connection(self):
        d = tempfile.mkdtemp(dir="/tmp")
        path = os.path.join(d, "docker.sock")
        srv = socket.socket(socket.AF_UNIX)
        srv.bind(path)
        srv.listen(1)
        self.assertFalse(st.probe_container_sockets((path,)).ok)
        srv.close()
        self.assertTrue(st.probe_container_sockets((path,)).ok)  # a stale socket file refuses
        self.assertTrue(st.probe_container_sockets((os.path.join(d, "absent.sock"),)).ok)


class TheSealOfTheGate(unittest.TestCase):
    """pr-tests.yml proves the self-test inside the command pr-gate.yml runs; the two must be the same command."""

    WORKFLOWS = CI.parents[1] / ".github" / "workflows"

    def sealed_line(self, name):
        text = (self.WORKFLOWS / name).read_text(encoding="utf-8")
        m = re.search(
            r"(sudo unshare --net --pid --fork --mount-proc runuser -u \"\$\(id -un\)\" -- \\\n\s+env -i [^\n]*\\\n\s+TENGOKU_CI_ROOT=[^\n]*\\\n\s+python3 scripts/ci/sandbox_selftest\.py[^\n]*\\\n(?:\s+--advisory[^\n]*\\\n)?)",
            text,
        )
        self.assertIsNotNone(m, f"{name} has no sealed self-test command")
        return re.sub(r"\s+", " ", m.group(1))

    def test_pr_tests_runs_the_command_of_the_gate(self):
        self.assertEqual(self.sealed_line("pr-gate.yml"), self.sealed_line("pr-tests.yml"))

    def test_the_gates_advisories_are_the_four_the_hardening_closes(self):
        text = (self.WORKFLOWS / "pr-gate.yml").read_text(encoding="utf-8")
        named = sorted(re.findall(r"--advisory (\w+)", text))
        self.assertEqual(
            named, ["cannot_read_runner_credentials", "cannot_write_runner_channels", "cannot_write_system", "no_container_socket"]
        )
        harden = (CI / "seal_harden.sh").read_text(encoding="utf-8")
        for needle in ("docker.sock", "_runner_file_commands", "_actions", "/usr/local/bin", "/opt", ".docker/config.json"):
            self.assertIn(needle, harden)

    def test_the_hardening_script_is_executable_shell_that_refuses_to_run_unprivileged(self):
        self.assertTrue(os.access(CI / "seal_harden.sh", os.X_OK))
        done = subprocess.run(["sh", str(CI / "seal_harden.sh"), "u", "--", "true"], capture_output=True, text=True)
        self.assertEqual(done.returncode, 2 if os.geteuid() != 0 else done.returncode)
        if os.geteuid() != 0:
            self.assertIn("as root", done.stderr)
        self.assertEqual(subprocess.run(["sh", "-n", str(CI / "seal_harden.sh")]).returncode, 0)


class Battery(unittest.TestCase):
    NAMES = [
        "unprivileged", "no_network_testnet", "no_network_named_host", "no_metadata_service", "own_pid_namespace", "pid1_environment",
        "environment_empty", "cannot_write_system", "cannot_write_runner_channels", "cannot_read_runner_credentials", "no_container_socket",
        "scratch_writable",
    ]  # fmt: skip

    def test_a_probe_that_cannot_run_is_a_failed_probe(self):
        with mock.patch.object(st, "probe_credentials", side_effect=RuntimeError("boom")):
            probes = {p.name: p for p in st.battery([])}
        self.assertFalse(probes["cannot_read_runner_credentials"].ok)
        self.assertIn("could not run", probes["cannot_read_runner_credentials"].detail)

    def test_judge(self):
        probes = [st.Probe("a", True), st.Probe("b", False), st.Probe("c", False)]
        self.assertEqual(st.judge(probes, ["c"]), (["b"], ["c"]))

    def run_cli(self, *args, env=None):
        return subprocess.run(
            [sys.executable, str(CI / "sandbox_selftest.py"), *args],
            capture_output=True,
            text=True,
            env=env or {"PATH": os.environ["PATH"], "HOME": os.environ.get("HOME", "/")},
        )

    def test_an_unsealed_step_stops_before_its_command_runs(self):
        marker = Path(tempfile.mkdtemp()) / "ran"
        env = {
            "PATH": os.environ["PATH"],
            "HOME": "/",
            "GITHUB_TOKEN": "ghs_NEVERPRINTTHIS",
            "ACTIONS_RUNTIME_TOKEN": "x",
            "TENGOKU_SELFTEST_TIMEOUT": "0.3",
        }
        done = self.run_cli("--", sys.executable, "-c", f"open({str(marker)!r}, 'w')", env=env)
        self.assertEqual(done.returncode, 1, done.stdout)
        self.assertFalse(marker.exists())
        self.assertIn("FAIL environment_empty", done.stdout)
        self.assertIn("GITHUB_TOKEN", done.stdout)
        self.assertNotIn("NEVERPRINTTHIS", done.stdout + done.stderr)
        self.assertIn("::error::", done.stdout)

    def test_known_gaps_run_the_command_and_warn(self):
        args = [a for n in self.NAMES for a in ("--advisory", n)]
        done = self.run_cli(*args, "--", sys.executable, "-c", "print('the command ran')")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("the command ran", done.stdout)
        self.assertNotIn("FAIL", done.stdout)

    def test_every_documented_probe_exists(self):
        doc = (CI / "sandbox_selftest.py").read_text(encoding="utf-8").split('"""')[1]
        out = self.run_cli("--advisory", "unprivileged").stdout
        for name in self.NAMES:
            self.assertIn(name, doc)
            self.assertRegex(out, rf"(?m)^(ok  |FAIL|warn) {name}\b")

    def test_an_unknown_option_is_refused(self):
        self.assertEqual(self.run_cli("--bogus").returncode, 2)


if __name__ == "__main__":
    unittest.main()
