"""The canary (scripts/ci/canary): `import Tengoku.All` must stay usable. The client talks MCP over SSE to a Leak space; here against a fake one, and the files that run it are pinned
(the 2026-10-17 bug: lean-pool's global `prefix:80 "-"` made `-(3 * x)` on a real number "Ambiguous term", and its notations reserved `v`, `na`, `ω` as words, on Leak IV for days)."""

import contextlib
import http.server
import json
import queue
import re
import sys
import threading
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
CI = HERE.parent
ROOT = CI.parents[1]
sys.path.insert(0, str(CI / "canary"))
import leak_canary as lc  # noqa: E402

OK = "✅ Compilation Successful! The proof is 100% verified.\n[[LEAK_NORMALIZED_SCRIPT_B64:aW1wb3J0]]"
BAD = "❌ Compilation Failed:\nLine 3 (Error): Ambiguous term -(3 * x) Possible interpretations: a b\nLine 5 (Warning): unused\nLine 5 (Error): unexpected token 'v'; expected ')'\n"


def fake_space(reply, drop_stream=False, endpoint=None):
    """a Leak space that answers verify_full_script with `reply(script)`; returns (server, base url, a function that ends the open streams)"""
    sessions: dict[str, queue.Queue] = {}
    counter = [0]

    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            if self.path == "/refresh":
                body = b'{"status":"current","pinned":"abc"}'
                self.send_response(200)
                self.send_header("content-length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            counter[0] += 1
            sid = f"{counter[0]:032x}"  # a Leak space names a 32-digit hex session
            sessions[sid] = q = queue.Queue()
            self.send_response(200)
            self.send_header("content-type", "text/event-stream")
            self.end_headers()
            self.wfile.write(f"event: endpoint\r\ndata: {endpoint or '/messages/'}?session_id={sid}\r\n\r\n".encode())
            self.wfile.flush()
            if drop_stream:
                return
            while True:
                item = q.get()
                if item is None:
                    return
                self.wfile.write(f"event: message\r\ndata: {json.dumps(item)}\r\n\r\n".encode())
                self.wfile.flush()

        def do_POST(self):
            msg = json.loads(self.rfile.read(int(self.headers["content-length"])))
            q = sessions[self.path.rsplit("=", 1)[1]]
            self.send_response(202)
            self.send_header("content-length", "0")
            self.end_headers()
            if msg.get("method") == "initialize":
                q.put({"jsonrpc": "2.0", "id": msg["id"], "result": {}})
            elif msg.get("method") == "tools/call":
                text = reply(msg["params"]["arguments"]["script"])
                q.put(
                    {
                        "jsonrpc": "2.0",
                        "id": msg["id"],
                        "result": {"content": [{"type": "text", "text": text}]},
                    }
                )

    srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), H)
    srv.daemon_threads = True
    threading.Thread(target=srv.serve_forever, daemon=True).start()

    def close():
        for q in list(sessions.values()):
            q.put(None)

    return srv, f"http://127.0.0.1:{srv.server_address[1]}", close


class Client(unittest.TestCase):
    def run_main(self, space, tmp, **kw):
        c, k = Path(tmp) / "C.lean", Path(tmp) / "K.lean"
        c.write_text(
            "import Tengoku.All\nexample : True := trivial\nexample (x : ℝ) : -(3 * x) = -3 * x := by ring\nexample : True := trivial\nexample (v : ℕ) : True := trivial\n"
        )
        k.write_text("import Tengoku.All\nexample (resolve : ℕ) : True := trivial\n")
        args = lc.parse(
            [
                "--retries",
                str(kw.get("retries", 0)),
                "--timeout",
                str(kw.get("timeout", 20)),
                *(["--budget", str(kw["budget"])] if "budget" in kw else []),
            ]
        )
        args.file, args.known = str(c), str(k)
        return lc.run(space, args)

    def test_a_script_that_compiles_exits_zero_and_one_that_does_not_exits_one(self):
        import tempfile

        for reply, want in ((lambda s: OK, 0), (lambda s: BAD, 1)):
            srv, base, close = fake_space(reply)
            try:
                with tempfile.TemporaryDirectory() as d:
                    self.assertEqual(self.run_main(base, d), want)
            finally:
                close()
                srv.shutdown()

    def test_the_known_open_file_is_reported_and_never_decides(self):
        import tempfile

        seen = []
        srv, base, close = fake_space(lambda s: (seen.append(s), BAD if "resolve" in s else OK)[1])
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d), 0)
            self.assertEqual(len(seen), 2)  # the known-open file was asked as well, and its failure did not decide
        finally:
            close()
            srv.shutdown()

    def test_only_the_canary_is_asked_again_when_the_space_cannot_be_asked(self):
        """CodeRabbit on #599: a slow known-open file turned a run whose canary compiled into a cancelled one. The known-open file gets one attempt."""
        import tempfile

        seen = []
        slow = "❌ Verification Error: verify exceeded 180s"
        srv, base, close = fake_space(lambda s: (seen.append("known" if "resolve" in s else "canary"), slow)[1])
        lc.RETRY_PAUSE = 0
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d, retries=2), 2)
            self.assertEqual(seen, ["canary", "canary", "canary", "known"])
        finally:
            close()
            srv.shutdown()
            lc.RETRY_PAUSE = 30

    def test_a_run_never_starts_an_attempt_after_its_budget_is_used_up(self):
        import tempfile

        seen = []
        srv, base, close = fake_space(lambda s: (seen.append(s), OK)[1])
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d, retries=2, budget=lc.MIN_CALL - 1), 2)  # no verdict, and no call at all
            self.assertEqual(seen, [])
        finally:
            close()
            srv.shutdown()

    def test_the_space_is_a_name_and_its_address_is_the_programs_constant(self):
        """Sonar S8703 / Snyk on tengoku#599: a command-line string must not become the address the client sends a script to"""
        self.assertEqual(lc.SPACES["leak-iv"], "https://barkingtree-leak-iv.hf.space")
        for bad in ("file:///etc/passwd", "https://example.com", "leak-iv/../x", ""):
            with self.assertRaises(SystemExit, msg=bad):
                lc.main(["--space", bad])

    def test_the_address_checks_that_remain_are_for_what_the_client_builds(self):
        self.assertEqual(lc.checked_space("https://barkingtree-leak-iv.hf.space/"), "https://barkingtree-leak-iv.hf.space")
        self.assertEqual(lc.checked_space("http://127.0.0.1:7861"), "http://127.0.0.1:7861")
        for bad in (
            "file:///etc/passwd",
            "ftp://host",
            "http://example.com",  # plain http to another machine
            "https://"
            + "u:p"
            + "@example.com",  # credentials in the address (written in pieces: a literal one reads as a secret to detect-secrets)
            "https://example.com/some/path",
            "https://example.com?x=1",
            "https://",
            "example.com",
        ):
            with self.assertRaises(ValueError, msg=bad):
                lc.checked_space(bad)
        with self.assertRaises(ValueError):
            lc.read_status("file:///etc/passwd")

    def test_an_endpoint_the_stream_names_on_another_host_is_not_followed(self):
        import tempfile

        seen = []
        srv, base, close = fake_space(lambda s: (seen.append(s), OK)[1], endpoint="http://127.0.0.2:9/messages/")
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d, timeout=5), 2)  # unreachable: nothing was sent anywhere
            self.assertEqual(seen, [])
        finally:
            close()
            srv.shutdown()

    def test_a_space_that_cannot_be_asked_exits_two_not_one(self):
        import tempfile

        srv, base, close = fake_space(lambda s: "", drop_stream=True)
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d, timeout=5), 2)
        finally:
            srv.shutdown()
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(self.run_main("http://127.0.0.1:9", d, timeout=5), 2)

    def test_the_verdict_reads_the_replies_of_verify_full_script(self):
        self.assertEqual(lc.verdict(OK), ("ok", []))
        kind, errors = lc.verdict(BAD)
        self.assertEqual(kind, "failed")
        self.assertEqual([n for n, _ in errors], [3, 5])  # the warning is not an error
        self.assertEqual(lc.verdict("❌ Verification Error: verify exceeded 180s")[0], "infra")
        self.assertEqual(lc.verdict("")[0], "infra")

    def test_the_report_names_the_line_of_the_canary(self):
        out = "\n".join(
            lc.report(
                "canary",
                "a\nb\nexample (v : ℕ) : True := trivial\n",
                [(3, "unexpected token 'v'")],
            )
        )
        self.assertIn("line 3: example (v : ℕ)", out)


class Readiness(unittest.TestCase):
    """After a promotion the canary must judge the tree the space has moved to, not the one it had (CodeRabbit on tengoku#599)."""

    POINTER = {"commit": "a" * 40, "topup": {"commit": "b" * 40}}

    def test_ready_means_idle_current_and_pinned_to_the_pointers_base(self):
        good = {"refreshing": False, "status": "current", "pinned": "a" * 40}
        self.assertEqual(lc.ready(good, self.POINTER), (True, ""))
        for status, pointer, why in (
            ({**good, "refreshing": True}, self.POINTER, "refreshing"),
            ({**good, "status": "newer"}, self.POINTER, "'newer'"),
            ({**good, "pinned": "c" * 40}, self.POINTER, "pinned"),
            ({k: v for k, v in good.items() if k != "refreshing"}, self.POINTER, "refreshing"),  # a reply that does not say is not idle
            (good, None, "could not be read"),
            (good, {"topup": {}}, "names no commit"),
        ):
            ok, reason = lc.ready(status, pointer)
            self.assertFalse(ok, status)
            self.assertIn(why, reason)

    @contextlib.contextmanager
    def pointer_at(self, base):
        """the published pointer is the module's constant URL: the tests point it at their fake"""
        saved, lc.POINTER = lc.POINTER, f"{base}/pointer"
        try:
            yield
        finally:
            lc.POINTER = saved

    def serve(self, states, pointer):
        """a server whose /refresh answers the given states in turn (the last one for ever) and whose /pointer answers `pointer` (None: 404)"""
        seen = [0]

        class H(http.server.BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def do_GET(self):
                if self.path == "/refresh":
                    body = json.dumps(states[min(seen[0], len(states) - 1)]).encode()
                    seen[0] += 1
                elif self.path == "/pointer" and pointer is not None:
                    body = json.dumps(pointer).encode()
                else:
                    self.send_response(404)
                    self.end_headers()
                    return
                self.send_response(200)
                self.send_header("content-length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), H)
        srv.daemon_threads = True
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        return srv, f"http://127.0.0.1:{srv.server_address[1]}"

    def test_it_waits_through_a_refresh_until_the_space_follows_the_pointer(self):
        idle = {"refreshing": False, "status": "current", "pinned": "a" * 40}
        srv, base = self.serve([{**idle, "refreshing": True, "status": "newer"}, {**idle, "pinned": "old"}, idle], self.POINTER)
        try:
            with self.pointer_at(base):
                self.assertTrue(lc.wait_ready(base, 0.0, 5.0, poll=0.01))
        finally:
            srv.shutdown()

    def test_a_space_that_never_follows_is_not_ready(self):
        srv, base = self.serve([{"refreshing": False, "status": "current", "pinned": "old"}], self.POINTER)
        try:
            with self.pointer_at(base):
                self.assertFalse(lc.wait_ready(base, 0.0, 0.3, poll=0.05))
        finally:
            srv.shutdown()

    def test_an_unreadable_pointer_is_not_ready(self):
        srv, base = self.serve([{"refreshing": False, "status": "current", "pinned": "a" * 40}], None)
        try:
            with self.pointer_at(base):
                self.assertFalse(lc.wait_ready(base, 0.0, 0.3, poll=0.05))
        finally:
            srv.shutdown()

    def test_main_does_not_compile_against_a_tree_the_space_has_not_moved_to(self):
        import tempfile

        seen = []
        srv, base, close = fake_space(lambda s: (seen.append(s), OK)[1])  # its /refresh says: not refreshing, current, pinned "abc"
        try:
            with tempfile.TemporaryDirectory() as d:
                canary = Path(d) / "C.lean"
                canary.write_text("import Tengoku.All\n")
                psrv, pbase = self.serve([{}], self.POINTER)  # the published pointer names "aaaa…", the space has pinned "abc"
                saved, lc.POINTER = lc.POINTER, f"{pbase}/pointer"
                try:
                    args = lc.parse(["--wait-refresh", "0.2"])
                    args.file, args.known = str(canary), str(Path(d) / "none")
                    rc = lc.run(base, args)
                finally:
                    lc.POINTER = saved
                    psrv.shutdown()
            self.assertEqual(rc, 2)  # the space is not shown to follow the pointer: nothing was compiled
            self.assertEqual(seen, [])
        finally:
            close()
            srv.shutdown()


class QueueStep(unittest.TestCase):
    """the shell of the queue's canary step, run against a fake `lake` and a fake `git`: every mode and every outcome"""

    @staticmethod
    def step():
        import yaml

        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "queue-gate.yml").read_text(encoding="utf-8"))
        return next(s for s in wf["jobs"]["queue-build"]["steps"] if str(s.get("name", "")).startswith("Canary"))

    def run_step(self, lake_rc, var="", base_mode="report\n", base_has_file=True, probes="base"):
        import os
        import subprocess
        import tempfile

        with tempfile.TemporaryDirectory() as d:
            bin_ = Path(d) / "bin"
            bin_.mkdir()
            # the fake lake records which file it was asked to compile, and what that file said
            (bin_ / "lake").write_text(
                f'#!/bin/bash\necho "${{@: -1}}" > lake_file.txt; cat "${{@: -1}}" > lake_saw.txt 2>/dev/null\necho \'Line 3 (Error): ambiguous\' >&2; exit {lake_rc}\n'
            )
            (bin_ / "git").write_text(
                '#!/bin/bash\ncase "$*" in\n'
                + (f"  *canary/mode*) printf '%s' '{base_mode}' ;;\n" if base_has_file else "  *canary/mode*) exit 128 ;;\n")
                + "  ls-tree*) "
                + {
                    "base": "echo '100644 blob abc\tscripts/ci/canary/Canary.lean'",
                    "none": "true",
                    "broken": "exit 128",
                    "unreadable": "echo '100644 blob abc\tscripts/ci/canary/Canary.lean'",
                }[probes]
                + " ;;\n"
                + ("  *Canary.lean*) exit 128 ;;\n" if probes == "unreadable" else "  *Canary.lean*) printf '%s' 'BASE PROBES' ;;\n")
                + "esac\n"
            )
            (bin_ / "timeout").write_text('#!/bin/bash\nshift 2; shift; "$@"\n')  # timeout -k 30 3m CMD...
            for f in bin_.iterdir():
                f.chmod(0o755)
            env = {
                **os.environ,
                "PATH": f"{bin_}:{os.environ['PATH']}",
                "CANARY_MODE_VAR": var,
                "BASE_SHA": "a" * 40,
                "RUNNER_TEMP": d,
                "GITHUB_STEP_SUMMARY": str(Path(d) / "summary.md"),
            }
            (Path(d) / "step.sh").write_text(self.step()["run"])  # the step as the workflow has it, run as a script file
            r = subprocess.run(["bash", "-e", "-o", "pipefail", "step.sh"], cwd=d, env=env, capture_output=True, text=True)
            self.lake_file = (
                (Path(d) / "lake_file.txt").read_text().strip() if (Path(d) / "lake_file.txt").exists() else None
            )  # the step may stop before lake
            self.lake_saw = (Path(d) / "lake_saw.txt").read_text() if (Path(d) / "lake_saw.txt").exists() else None
            return r.returncode, r.stdout + r.stderr

    def test_report_mode_warns_and_lets_the_group_through(self):
        rc, out = self.run_step(1)
        self.assertEqual(rc, 0, out)
        self.assertIn("::warning::the canary does not compile", out)

    def test_enforce_mode_from_the_variable_or_from_the_base_fails_the_group(self):
        for kw in ({"var": "enforce"}, {"base_mode": "enforce\n"}):
            rc, out = self.run_step(1, **kw)
            self.assertEqual(rc, 1, (kw, out))
            self.assertIn("the tree is no longer usable", out)

    def test_a_canary_that_compiles_passes_in_every_mode(self):
        for kw in ({}, {"var": "enforce"}, {"base_mode": "enforce\n"}):
            self.assertEqual(self.run_step(0, **kw)[0], 0, kw)

    def test_the_probes_are_the_bases_copy_so_a_group_cannot_delete_the_probe_that_catches_it(self):
        """CodeRabbit on #599: the mode was read from the base, the probes from the group's own checkout."""
        rc, out = self.run_step(0)
        self.assertEqual(rc, 0, out)
        self.assertTrue(self.lake_file.endswith("Canary.base.lean"), self.lake_file)
        self.assertEqual(self.lake_saw, "BASE PROBES")

    def test_the_groups_own_probes_are_used_only_when_the_base_has_none(self):
        rc, out = self.run_step(0, probes="none")
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.lake_file, "scripts/ci/canary/Canary.lean")

    def test_probes_that_cannot_be_read_are_no_verdict_and_never_the_groups_own_copy(self):
        """Gitar on tengoku#599: the base's blob is fetched lazily in the partial clone; a failed fetch must not make the step compile the probes the group edited"""
        for probes in ("unreadable", "broken"):
            for kw in ({}, {"var": "enforce"}):
                rc, out = self.run_step(1, probes=probes, **kw)
                self.assertEqual(rc, 0, f"{probes} {kw}: {out}")  # not even in enforce mode is it the group's fault
                self.assertIn("no verdict on this group", out)
                self.assertIsNone(self.lake_file, "the canary was compiled although its probes could not be read")

    def test_the_variable_wins_over_the_base_file(self):
        self.assertEqual(self.run_step(1, var="report", base_mode="enforce\n")[0], 0)

    def test_a_missing_mode_file_is_report_and_an_unknown_word_is_an_error(self):
        self.assertEqual(self.run_step(1, base_has_file=False)[0], 0)
        rc, out = self.run_step(1, base_mode="Enforce\n")
        self.assertEqual(rc, 1)
        self.assertIn("unknown canary mode", out)

    def test_no_verdict_in_time_is_a_warning_even_when_enforcing(self):
        for rc_lake in (124, 137):
            rc, out = self.run_step(rc_lake, var="enforce")
            self.assertEqual(rc, 0, out)
            self.assertIn("did not finish in 3 minutes", out)

    def test_it_runs_whenever_the_library_built_and_not_when_it_did_not(self):
        s = self.step()
        self.assertIn("steps.delta.outputs.built == 'yes'", s["if"])
        self.assertNotIn("needs-nightly", s["if"])  # a delta too big to publish has nothing to do with whether the tree is usable
        wf = (ROOT / ".github" / "workflows" / "queue-gate.yml").read_text(encoding="utf-8")
        self.assertIn('echo "built=$([ "$rc" = 0 ] && echo yes || echo no)" >> "$GITHUB_OUTPUT"', wf)


class Files(unittest.TestCase):
    """What the canary must keep catching: one probe per kind of failure that has happened."""

    def setUp(self):
        self.canary = (CI / "canary" / "Canary.lean").read_text(encoding="utf-8")

    def test_it_imports_the_whole_tree_and_sets_the_options_that_keep_it_honest(self):
        self.assertTrue(self.canary.startswith("import Tengoku.All\n"))
        self.assertIn("set_option Elab.async false", self.canary)  # errors come back on the line that has them

    def test_notation_words_and_tactics_are_all_probed(self):
        for probe in (
            "-(3 * x) = -3 * x",  # lean-pool Modal: prefix:80 "-"
            "(f ∘ g) 0",
            "x⁻¹ * x = 1",
            "Real.sqrt 4 = 2",
            "3 ∈ insert 5 s",
            "l[0] = l[0]",
            "a ≃ b",
            "X ⟶ Y",
            "X ≅ X",
            "a b c d e f g h i j k l m n o p q r s t u v w x y z",  # `v` was a reserved word
            "(na ih hx",
            "Δ ω",
            "(resolve : ℕ)",  # equational-theories: a global `elab`
            "(superpose : ℕ)",
            "(Facts : ℕ)",
            "(memoFinOp : ℕ)",
            "(finOpTable : ℕ)",
            "(mod_symm : ℕ)",
            "by omega",
            "by positivity",
            "by linarith",
            "by nlinarith",
            "by ring",
            "by field_simp",
            "by norm_num",
            "by gcongr",
            "by fun_prop",
            "by interval_cases",
            "by decide",
            "by simp",
        ):
            self.assertIn(probe, self.canary, probe)

    def test_the_known_open_file_holds_no_fixed_probe_and_the_gate_has_what_was_fixed(self):
        known = (CI / "canary" / "CanaryKnown.lean").read_text(encoding="utf-8")
        for word in ("resolve", "superpose", "Facts", "memoFinOp", "finOpTable", "mod_symm"):
            self.assertIn(f"({word} : ℕ)", self.canary)  # compiled on Leak IV on 2026-10-18 and moved into the gate
            self.assertNotIn(f"({word} : ℕ)", known)
        self.assertTrue(known.startswith("import Tengoku.All\n"))

    def test_the_queue_runs_it_after_the_library_is_built_and_it_can_be_made_to_fail_the_group(
        self,
    ):
        wf = (ROOT / ".github" / "workflows" / "queue-gate.yml").read_text(encoding="utf-8")
        i = wf.index("name: Canary")
        step = wf[i : wf.index("\n      - ", i + 10)]
        self.assertIn("merge_group", step)
        self.assertIn("scripts/ci/canary/Canary.lean", step)
        self.assertIn("enforce", step)
        self.assertLess(
            wf.index("name: Build the library as main will have it"),
            i,
            "the tree is built before the canary imports it",
        )

    def test_the_job_outlasts_the_refresh_wait_and_the_clients_budget(self):
        import yaml

        text = (ROOT / ".github" / "workflows" / "leak-canary.yml").read_text(encoding="utf-8")
        job = yaml.safe_load(text)["jobs"]["canary"]
        run = next(s for s in job["steps"] if str(s.get("name", "")).startswith("The canary ("))["run"]
        settle = int(re.search(r"--settle (\d+)", run).group(1))
        wait = int(re.search(r"--wait-refresh (\d+)", run).group(1))
        budget = int(re.search(r"--budget (\d+)", run).group(1))
        self.assertLessEqual(
            settle + wait + budget + 5 * 60, job["timeout-minutes"] * 60
        )  # the client exits 2 by itself when the space never follows: the job is not cancelled first

    def test_a_scheduled_run_cannot_cancel_the_check_that_follows_a_promotion(self):
        import yaml

        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "leak-canary.yml").read_text(encoding="utf-8"))
        self.assertIn("github.event_name", wf["concurrency"]["group"])  # CodeRabbit: one group per kind of run
        self.assertTrue(wf["concurrency"]["cancel-in-progress"])

    def test_the_space_is_chosen_by_name_and_nothing_is_checked_out_in_a_workflow_run(self):
        import yaml

        text = (ROOT / ".github" / "workflows" / "leak-canary.yml").read_text(encoding="utf-8")
        wf = yaml.safe_load(text)
        space = wf[True]["workflow_dispatch"]["inputs"]["space"]
        self.assertEqual(
            (space["type"], sorted(space["options"])), ("choice", sorted(lc.SPACES))
        )  # Sonar S8703: an address typed into a workflow input
        self.assertNotIn("actions/checkout", text)  # Sonar S7631: workflow_run + checkout; the files are read from main through the API
        self.assertIn("ref=main", text)

    def test_the_leak_space_is_asked_on_a_schedule_and_after_every_promotion(self):
        wf = (ROOT / ".github" / "workflows" / "leak-canary.yml").read_text(encoding="utf-8")
        self.assertIn("schedule:", wf)
        self.assertIn("topup-promote", wf)
        self.assertIn("leak_canary.py", wf)
        self.assertNotIn("secrets.", wf)  # the space is public; nothing here needs a token
        self.assertTrue(re.search(r"permissions:\s*\{\s*\}", wf) or "permissions: {}" in wf)


if __name__ == "__main__":
    unittest.main()
