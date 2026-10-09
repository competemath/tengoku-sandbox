#!/usr/bin/env python3
"""sandbox_selftest.py [--allow-env NAME]... [--advisory PROBE]... [--] [COMMAND ARGS...] — prove that a sealed step is sealed.

The gate runs code it did not write in a "sealed" step: `unshare --net --pid --fork --mount-proc runuser -u <user> -- env -i ...`
(the vacuity job of pr-gate.yml; jinshi-pr.yml). That line is only as good as the runner it runs on: a missing flag, a runner image that
changes, or an edit that drops `env -i` leaves a step that looks sealed and is not. This is the first command inside the seal. It
probes, from inside, what must be denied; if any probe says it is not, it exits 1 and the job stops before the PR's code starts. With a
COMMAND it then replaces itself with that command (so the step's exit status is the command's).

Probes (each prints `ok` or `FAIL` and what it saw; never a value of an environment variable):
  unprivileged                  not root, and no effective capability
  no_network_testnet            a connection to a TEST-NET-1 address (192.0.2.1) fails for want of a route (a timeout is not enough: nothing answers there)
  no_network_named_host         api.github.com and a public resolver cannot be reached
  no_metadata_service           the cloud metadata address (169.254.169.254) cannot be reached
  own_pid_namespace             few processes are visible, and pid 1 is not the runner's init or a runner process
  pid1_environment              /proc/1/environ is unreadable or carries no variable that is not on the allow-list
  environment_empty             this process's environment holds only the allowed names and nothing that looks like a credential
  cannot_write_system           nothing can be created under /, /etc, /usr, /bin, /opt, /var/lib
  cannot_write_runner_channels  the files a step appends to for GITHUB_ENV, GITHUB_PATH and GITHUB_OUTPUT, and the code of the downloaded actions (whose
                                post steps run after this one, with the job's token), are not writable
  cannot_read_runner_credentials  the runner's credential files, and the usual token files of a home directory (a Docker config only if it holds a
                                  registry credential), are not readable
  no_container_socket           the Docker, containerd and Podman sockets cannot be connected to (a unix socket is addressed by path,
                                so a network namespace does not stop it, and a container started through it is outside the seal)
  scratch_writable              /tmp and the working directory are writable (the command can still do its work)

`--advisory PROBE` turns a known gap into a warning that is printed on every run, so that it is not forgotten and does not stop the job;
use it only with a reason written next to the workflow line. `--allow-env NAME` names a variable the step passes on purpose.

Credit: Tau Ceti Project, the nine-probe bubblewrap self-test of TauCeti's pr-build.yml (PR 5800, 2026-09-06) and scripts/sandbox-build.sh,
which aborts the job when a probe says the sandbox is not enforcing: no write to / or /etc, no read of a host canary, no network, no nested
user namespace, a different user namespace, an empty PID-1 environment; and the `/proc/1/environ` leak that taught them `env -i`. We
read the behaviour described in their reports; this is independent code for a different seal (namespaces plus runuser, not bubblewrap).
What we do differently: it checks the things that bypass a network and PID namespace on a hosted runner (the Docker socket, the runner's
own credential files and command files, a leaked environment in /proc), and it prints what it saw. Standard library only."""

from __future__ import annotations

import errno
import glob
import json
import os
import re
import socket
import sys
import tempfile
from dataclasses import dataclass

DEFAULT_ENV = frozenset({"HOME", "PATH", "LANG", "LC_ALL", "PWD", "OLDPWD", "SHLVL", "_", "TMPDIR"})
# a name that holds, or points at, a credential or the runner's own state
CREDENTIAL_NAME = re.compile(
    r"(?i)^(?:GH_|GITHUB_|ACTIONS_|RUNNER_|CI$|AWS_|AZURE_|GOOGLE_|ANTHROPIC_|OPENAI_|CLAUDE_|SSH_|NPM_|PIP_)|TOKEN|SECRET|PASSWORD|PASSWD|CREDENTIAL|API_?KEY|PRIVATE"
)
INIT_NAMES = frozenset(
    {
        "systemd",
        "init",
        "launchd",
        "containerd-shim",
        "containerd",
        "dockerd",
        "runc",
        "tini",
        "Runner.Listener",
        "Runner.Worker",
        "provjobd",
    }
)
MAX_PROCESSES = 12
TIMEOUT = float(
    os.environ.get("TENGOKU_SELFTEST_TIMEOUT", "3")
)  # seconds to wait for a connection that neither fails nor completes (tests shorten it)
SYSTEM_DIRS = ("/", "/etc", "/usr", "/usr/local/bin", "/bin", "/opt", "/var/lib")
CREDENTIAL_FILES = (
    "/home/*/runners/*/.credentials*",
    "/home/*/runners/*/.runner",
    "/home/*/actions-runner/.credentials*",
    "/opt/actions-runner/.credentials*",
    "/opt/runner/.credentials*",
    "~/.config/gh/hosts.yml",
    "~/.netrc",
    "~/.git-credentials",
    "~/.aws/credentials",
    "~/.npmrc",
    "~/.ssh/id_*",
    "/run/secrets/*",
)
# the files a step appends to for GITHUB_ENV, GITHUB_PATH and GITHUB_OUTPUT, and the code of the actions whose post steps run after this one
CHANNEL_DIRS = (
    "/home/*/work/_temp/_runner_file_commands",
    "/home/*/work/_actions",
    "/home/*/actions-runner/_work/_temp/_runner_file_commands",
    "/home/*/actions-runner/_work/_actions",
    "/opt/actions-runner/_work/_temp/_runner_file_commands",
    "/opt/actions-runner/_work/_actions",
    "/runner/_work/_temp/_runner_file_commands",
    "/runner/_work/_actions",
)
DOCKER_CONFIG = "~/.docker/config.json"
SOCKETS = (
    "/var/run/docker.sock",
    "/run/docker.sock",
    "/run/containerd/containerd.sock",
    "/var/run/podman/podman.sock",
    "/run/podman/podman.sock",
)


@dataclass
class Probe:
    name: str
    ok: bool
    detail: str = ""


# ------------------------------------------------------------------------------------------------------------- pure helpers


def parse_status(text: str) -> dict:
    """/proc/<pid>/status as a dict of its `Name:\tvalue` lines."""
    out = {}
    for line in text.splitlines():
        key, sep, value = line.partition(":")
        if sep:
            out[key.strip()] = value.strip()
    return out


def environment_problems(names, allow) -> list:
    """The variables a sealed step should not have: names off the allow-list, and (even on it) names that look like credentials."""
    allowed = set(DEFAULT_ENV) | set(allow)
    bad = sorted(n for n in names if n not in allowed or (CREDENTIAL_NAME.search(n) and n not in allow))
    return bad


def environ_names(raw: bytes) -> list:
    return [kv.split(b"=", 1)[0].decode("utf-8", "replace") for kv in raw.split(b"\0") if kv]


# ------------------------------------------------------------------------------------------------------------------ probes


def route_state(addr: tuple, timeout: float | None = None) -> str:
    """What a connection attempt says about the network: 'none' when there is no route at all (ENETUNREACH: what a network namespace
    without interfaces answers at once), else a description of what happened. A TEST-NET address answers nothing anywhere, so a
    timeout is not a seal: only the missing route is."""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(TIMEOUT if timeout is None else timeout)
    try:
        s.connect(addr)
    except socket.timeout:
        return f"{addr[0]}:{addr[1]} timed out (a route exists)"
    except OSError as exc:
        if exc.errno == errno.ENETUNREACH:
            return "none"
        return f"{addr[0]}:{addr[1]} {exc.strerror or exc.errno} (a route exists)"
    finally:
        s.close()
    return f"connected to {addr[0]}:{addr[1]}"


def probe_unprivileged() -> Probe:
    st = parse_status(open("/proc/self/status", encoding="utf-8").read())
    cap = int(st.get("CapEff", "1"), 16)
    problems = [p for p in (f"uid {os.geteuid()}" if os.geteuid() == 0 else "", f"CapEff {cap:x}" if cap else "") if p]
    return Probe("unprivileged", not problems, ", ".join(problems))


def probe_testnet() -> Probe:
    state = route_state(("192.0.2.1", 80))
    return Probe("no_network_testnet", state == "none", "" if state == "none" else state)


def probe_named_hosts() -> Probe:
    try:
        ips = {a[4][0] for a in socket.getaddrinfo("api.github.com", 443, socket.AF_INET)}  # no resolver is as good as no route
    except OSError:
        ips = set()
    seen = [r for r in (route_state((ip, 443)) for ip in [*sorted(ips)[:2], "1.1.1.1"]) if r != "none"]
    return Probe("no_network_named_host", not seen, "; ".join(seen))


def probe_metadata() -> Probe:
    state = route_state(("169.254.169.254", 80))
    return Probe("no_metadata_service", state == "none", "" if state == "none" else state)


def probe_pid_namespace(proc: str = "/proc") -> Probe:
    pids = sorted(int(d) for d in os.listdir(proc) if d.isdigit())
    problems = []
    if len(pids) > MAX_PROCESSES:
        problems.append(f"{len(pids)} processes visible")
    try:
        with open(f"{proc}/1/comm", encoding="utf-8") as fh:
            comm = fh.read().strip()
        if comm in INIT_NAMES:
            problems.append(f"pid 1 is {comm}")
    except OSError:
        problems.append("pid 1 cannot be named")
    return Probe("own_pid_namespace", not problems, ", ".join(problems))


def probe_pid1_environment(allow, proc: str = "/proc") -> Probe:
    try:
        with open(f"{proc}/1/environ", "rb") as fh:
            names = environ_names(fh.read())
    except OSError:
        return Probe("pid1_environment", True, "unreadable")
    bad = environment_problems(names, allow)
    return Probe("pid1_environment", not bad, "readable, holds " + ", ".join(bad) if bad else "")


def probe_environment(allow, environ=None) -> Probe:
    bad = environment_problems(list(os.environ if environ is None else environ), allow)
    return Probe("environment_empty", not bad, "variables present: " + ", ".join(bad) if bad else "")


def writable(directory: str) -> bool:
    path = os.path.join(directory, f".tengoku-selftest-{os.getpid()}")
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except OSError:
        return False
    os.close(fd)
    os.unlink(path)
    return True


def probe_write_system(dirs=SYSTEM_DIRS) -> Probe:
    open_ = [d for d in dirs if os.path.isdir(d) and writable(d)]
    return Probe("cannot_write_system", not open_, "writable: " + ", ".join(open_) if open_ else "")


def probe_runner_channels(patterns=CHANNEL_DIRS) -> Probe:
    open_ = [d for pat in patterns for d in glob.glob(pat) if os.access(d, os.W_OK)]
    return Probe("cannot_write_runner_channels", not open_, "writable: " + ", ".join(open_) if open_ else "")


def docker_credentials(path: str) -> bool:
    """Does the Docker client's config hold a registry credential (an `auths` entry with `auth` or `identitytoken`)? A config without one is not a leak."""
    try:
        with open(path, encoding="utf-8") as fh:
            auths = json.load(fh).get("auths", {})
    except (OSError, ValueError, AttributeError):
        return False
    return isinstance(auths, dict) and any(isinstance(v, dict) and (v.get("auth") or v.get("identitytoken")) for v in auths.values())


def probe_credentials(patterns=CREDENTIAL_FILES, docker_config=DOCKER_CONFIG) -> Probe:
    readable = [p for pat in patterns for p in glob.glob(os.path.expanduser(pat)) if os.path.isfile(p) and os.access(p, os.R_OK)]
    cfg = os.path.expanduser(docker_config)
    if os.path.isfile(cfg) and os.access(cfg, os.R_OK) and docker_credentials(cfg):
        readable.append(cfg)
    return Probe("cannot_read_runner_credentials", not readable, "readable: " + ", ".join(sorted(set(readable))) if readable else "")


def probe_container_sockets(paths=SOCKETS) -> Probe:
    reached = []
    for p in paths:
        if not os.path.exists(p):
            continue
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(2)
        try:
            s.connect(p)
            reached.append(p)
        except OSError as exc:
            if exc.errno not in (errno.EACCES, errno.EPERM, errno.ECONNREFUSED, errno.ENOENT, errno.ENOTSOCK):
                reached.append(f"{p} ({exc.strerror})")
        finally:
            s.close()
    return Probe("no_container_socket", not reached, "connectable: " + ", ".join(reached) if reached else "")


def probe_scratch() -> Probe:
    bad = [d for d in (tempfile.gettempdir(), os.getcwd()) if not writable(d)]
    return Probe("scratch_writable", not bad, "not writable: " + ", ".join(bad) if bad else "")


def battery(allow) -> list:
    """Every probe, in order. A probe that raises is a failed probe: what cannot be checked is not known to be sealed."""
    runs = [
        ("unprivileged", probe_unprivileged),
        ("no_network_testnet", probe_testnet),
        ("no_network_named_host", probe_named_hosts),
        ("no_metadata_service", probe_metadata),
        ("own_pid_namespace", probe_pid_namespace),
        ("pid1_environment", lambda: probe_pid1_environment(allow)),
        ("environment_empty", lambda: probe_environment(allow)),
        ("cannot_write_system", probe_write_system),
        ("cannot_write_runner_channels", probe_runner_channels),
        ("cannot_read_runner_credentials", probe_credentials),
        ("no_container_socket", probe_container_sockets),
        ("scratch_writable", probe_scratch),
    ]
    out = []
    for name, run in runs:
        try:
            out.append(run())
        except Exception as exc:  # noqa: BLE001 — see above
            out.append(Probe(name, False, f"could not run: {type(exc).__name__}: {exc}"))
    return out


def judge(probes: list, advisory) -> tuple:
    """(failed probe names, warned probe names)."""
    failed = [p.name for p in probes if not p.ok and p.name not in advisory]
    warned = [p.name for p in probes if not p.ok and p.name in advisory]
    return failed, warned


def main(argv: list) -> int:
    allow, advisory, command = [], [], []
    i = 0
    while i < len(argv):
        if argv[i] == "--allow-env" and i + 1 < len(argv):
            allow.append(argv[i + 1])
            i += 2
        elif argv[i] == "--advisory" and i + 1 < len(argv):
            advisory.append(argv[i + 1])
            i += 2
        elif argv[i] == "--":
            command = argv[i + 1 :]
            break
        elif argv[i].startswith("--"):
            print(f"sandbox_selftest: unknown option {argv[i]}", file=sys.stderr)
            return 2
        else:
            command = argv[i:]
            break
    probes = battery(allow)
    for p in probes:
        tag = "ok  " if p.ok else ("warn" if p.name in advisory else "FAIL")
        print(f"{tag} {p.name}" + (f": {p.detail}" if p.detail else ""))
    failed, warned = judge(probes, advisory)
    if warned:
        print(f"::warning::sealed step: known gaps still open: {', '.join(warned)}")
    if failed:
        print(f"::error::this step is not sealed, so the code it was going to run does not run: {', '.join(failed)}")
        return 1
    print(f"sealed: {len(probes) - len(warned)} probes denied what they must" + (f", {len(warned)} known gaps" if warned else ""))
    if command:
        sys.stdout.flush()
        os.execvp(command[0], command)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
