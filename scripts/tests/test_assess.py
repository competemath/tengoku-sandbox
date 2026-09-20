"""The blind re-proof test: the runner against a fake `claude`, the gate against synthetic claims.

No network, no Lean, no real agent. The fake CLI speaks the same stream format as the real one
(scripted by FAKE_PLAN); a tiny local HTTP server stands in for the services' /refresh. The gate
is run as CI runs it (a throwaway git repository with a base and a head commit)."""

import base64
import http.server
import json
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts" / "assess"))
import common as C  # noqa: E402

FAKE_CLAUDE = r"""#!/usr/bin/env python3
import json, os, sys, time
plan = json.loads(os.environ["FAKE_PLAN"])           # {"connected": bool, "turns": [[step, ...], ...]}
servers = ["search", "states", "verify"]
tools = json.loads(os.environ["FAKE_TOOLS"])
turn = 0
for line in sys.stdin:
    status = "connected" if plan.get("connected", True) else "pending"
    print(json.dumps({"type": "system", "subtype": "init", "session_id": "s", "cwd": os.getcwd(), "model": "fake-model", "tools": tools if plan.get("connected", True) else [], "mcp_servers": [{"name": s, "status": status} for s in servers]}), flush=True)
    for n, step in enumerate(plan["turns"][min(turn, len(plan["turns"]) - 1)]):
        time.sleep(step.get("sleep", 0.05))
        content = [{"type": "text", "text": step["say"]}]
        if step.get("tool"):
            content.append({"type": "tool_use", "id": f"t{turn}_{n}", "name": step["tool"], "input": step.get("input", {})})
        print(json.dumps({"type": "assistant", "message": {"model": "fake-model", "content": content, "usage": {"output_tokens": 5}}}), flush=True)
        if step.get("tool"):
            print(json.dumps({"type": "user", "message": {"content": [{"type": "tool_result", "tool_use_id": f"t{turn}_{n}", "content": json.dumps({"result": step.get("result", "")})}]}}), flush=True)
    print(json.dumps({"type": "result", "subtype": "success", "duration_ms": 1, "num_turns": 1}), flush=True)
    turn += 1
"""
RECORD = {"name": "Demo.sum_comm", "statement": "import Mathlib\n\ntheorem Demo.sum_comm (a b : Nat) : a + b = b + a", "proof": ":= Nat.add_comm a b", "status": "staging",
          "library": "originals", "source_url": "https://example.org/originals/1", "toolchain": "leanprover/lean4:v4.34.0-rc2"}  # fmt: skip
TRANSLATED = {
    **RECORD,
    "name": "Demo.translated",
    "statement": "theorem Demo.translated : True",
    "source_url": "https://github.com/upstream/lib/blob/abc/F.lean",
}
MAIN_COMMIT = None


def verified(script: str) -> str:
    return (
        "✅ Compilation Successful! The proof is 100% verified.\n[[LEAK_NORMALIZED_SCRIPT_B64:"
        + base64.b64encode(("import Tengoku.All\n\n" + script).encode()).decode()
        + "]]"
    )


def git(cwd, *args):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


class Refresh(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        body = json.dumps({"pinned": MAIN_COMMIT}).encode()
        self.send_response(200)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *a):
        pass


class Assess(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.httpd = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Refresh)
        threading.Thread(target=cls.httpd.serve_forever, daemon=True).start()
        url = f"http://127.0.0.1:{cls.httpd.server_address[1]}"
        cls.services = {"search": url, "states": url, "verify": url}

    @classmethod
    def tearDownClass(cls):
        cls.httpd.shutdown()

    def setUp(self):
        global MAIN_COMMIT
        self.d = Path(tempfile.mkdtemp())
        git(self.d, "init", "-q", "-b", "main")
        git(self.d, "config", "user.email", "c@example.com")
        git(self.d, "config", "user.name", "Contributor")
        for sub in ("scripts", "schemas"):
            shutil.copytree(REPO / sub, self.d / sub, ignore=shutil.ignore_patterns("__pycache__"))
        sources = json.loads((self.d / "schemas/sources.json").read_text())
        sources["translations"] = ["https://github.com/upstream/lib"]
        (self.d / "schemas/sources.json").write_text(json.dumps(sources))
        git(self.d, "add", "-A")
        git(self.d, "commit", "-q", "-m", "base")
        self.base = MAIN_COMMIT = git(self.d, "rev-parse", "HEAD")
        fake = self.d.parent / (self.d.name + "-claude")
        fake.write_text(FAKE_CLAUDE)
        fake.chmod(0o755)
        self.env = {**os.environ, "TENGOKU_CI_ROOT": str(self.d), "TENGOKU_ASSESS_CLAUDE": str(fake), "TENGOKU_ASSESS_SERVICES": json.dumps(self.services),
                    "FAKE_TOOLS": json.dumps(C.ALLOWED_TOOLS + ["mcp__verify__tengoku_sync"])}  # fmt: skip
        self.env.pop("GITHUB_ACTIONS", None)
        self.env.pop("GITHUB_STEP_SUMMARY", None)

    # ---- helpers
    def stage(self, records):
        p = self.d / "data/staging/originals/mine.jsonl"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in records))
        return p

    def run_runner(self, plan, *extra):
        env = {**self.env, "FAKE_PLAN": json.dumps(plan)}
        return subprocess.run(
            [sys.executable, "scripts/assess/run.py", "data/staging/originals/mine.jsonl", "--warmup", "0.2", "--idle", "0.2", *extra],
            cwd=self.d,
            env=env,
            capture_output=True,
            text=True,
        )

    def synthetic(self, records, outcomes, *, mutate=None):
        """Write a claim as the runner would for full-length runs, without waiting five minutes."""
        out = self.d / "claims/mine"
        out.mkdir(parents=True, exist_ok=True)
        headlines = []
        for i, (rec, closed) in enumerate(zip(records, outcomes), 1):
            lines = [{"t": 0.0, "kind": "runner", "version": C.VERSION, "headline": rec["name"], "statement_sha256": C.sha256(C.theorem_text(rec)), "prompt": C.prompt_for(rec),
                      "budget": {"soft_s": C.SOFT_S, "hard_s": C.HARD_S}, "services": self.services, "pinned": {k: self.base for k in self.services}, "started_at": "2026-01-01T00:00:00Z"}]  # fmt: skip
            lines.append(
                {
                    "t": 0.5,
                    "kind": "event",
                    "event": {
                        "type": "system",
                        "subtype": "init",
                        "model": "fake-model",
                        "tools": C.ALLOWED_TOOLS,
                        "mcp_servers": [{"name": s, "status": "connected"} for s in self.services],
                    },
                }
            )
            t = 1.0
            for n in range(12 if not closed else 2):
                last = closed and n == 1
                tool = "mcp__verify__verify_full_script" if n % 3 == 0 or last else "mcp__search__loogle_search"
                script = C.theorem_text(rec) + " := by simp"
                lines.append(
                    {
                        "t": t,
                        "kind": "event",
                        "event": {
                            "type": "assistant",
                            "message": {
                                "model": "fake-model",
                                "content": [
                                    {"type": "text", "text": f"Trying idea {n}."},
                                    {
                                        "type": "tool_use",
                                        "id": f"c{n}",
                                        "name": tool,
                                        "input": {"script": script} if "verify" in tool else {"query": "Nat.add"},
                                    },
                                ],
                                "usage": {},
                            },
                        },
                    }
                )
                lines.append(
                    {
                        "t": t + 2,
                        "kind": "event",
                        "event": {
                            "type": "user",
                            "message": {
                                "content": [
                                    {
                                        "type": "tool_result",
                                        "tool_use_id": f"c{n}",
                                        "content": json.dumps(
                                            {"result": verified(script) if last else "❌ Compilation Failed: unsolved goals"}
                                        ),
                                    }
                                ]
                            },
                        },
                    }
                )
                t += 25 if not closed else 3
            lines.append({"t": t, "kind": "runner", "end": "closed" if closed else "soft-budget", "seconds": t})
            if mutate:
                mutate(lines, rec)
            m = C.measure(lines, rec)
            stem = f"{i}-{C.slug(rec['name'])}"
            C.write_transcript(out / f"{stem}.transcript.jsonl.gz", lines)
            (out / f"{stem}.working.md").write_text(C.render_working(lines, rec))
            headlines.append({"name": rec["name"], "statement_sha256": C.sha256(C.theorem_text(rec)), "outcome": m["outcome"], "seconds": m["seconds"], "calls": m["calls"], "models": m["models"],
                              "working": f"{stem}.working.md", "working_sha256": C.sha256((out / f"{stem}.working.md").read_bytes()),
                              "transcript": f"{stem}.transcript.jsonl.gz", "transcript_sha256": C.sha256((out / f"{stem}.transcript.jsonl.gz").read_bytes())})  # fmt: skip
        claim = {"version": C.VERSION, "records": "data/staging/originals/mine.jsonl", "headlines": headlines, "others": [], "budget": {"soft_s": C.SOFT_S, "hard_s": C.HARD_S}, "services": self.services,
                 "pinned_start": {k: self.base for k in self.services}, "pinned_end": {k: self.base for k in self.services}, "attested_by": "Contributor <c@example.com>", "made_at": "2026-01-01T00:10:00Z"}  # fmt: skip
        claim["digest"] = C.digest(claim)
        (out / "claim.json").write_text(json.dumps(claim, indent=2) + "\n")
        return out

    def gate(self, *flags):
        git(self.d, "add", "-A")
        git(self.d, "commit", "-q", "-s", "-m", "contribution")
        r = subprocess.run(
            [sys.executable, "scripts/ci/assess.py", self.base, "HEAD", *flags], cwd=self.d, env=self.env, capture_output=True, text=True
        )
        return r.returncode, r.stdout + r.stderr

    # ---- the runner
    def test_runner_closes_an_easy_theorem_and_says_the_pr_would_be_rejected(self):
        self.stage([RECORD])
        script = "theorem Demo.sum_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b"
        r = self.run_runner(
            {
                "turns": [
                    [
                        {
                            "say": "Commutativity is in the library.",
                            "tool": "mcp__verify__verify_full_script",
                            "input": {"script": script},
                            "result": verified(script),
                        }
                    ]
                ]
            }
        )
        self.assertEqual(r.returncode, 3, r.stdout + r.stderr)
        claim = json.loads((self.d / "claims/mine/claim.json").read_text())
        self.assertEqual(claim["headlines"][0]["outcome"], "closed")
        self.assertIn("this closed it", (self.d / "claims/mine/1-Demo.sum_comm.working.md").read_text())

    def test_runner_keeps_the_agent_going_until_the_budget_and_records_resisted(self):
        self.stage([RECORD])
        fail_step = {
            "say": "Try simp.",
            "tool": "mcp__verify__verify_full_script",
            "input": {"script": "x"},
            "result": "❌ Compilation Failed",
            "sleep": 0.3,
        }
        r = self.run_runner({"turns": [[fail_step], [fail_step]]}, "--soft", "18", "--hard", "25")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        lines = C.read_transcript(self.d / "claims/mine/1-Demo.sum_comm.transcript.jsonl.gz")
        self.assertTrue(any("continue" in x for x in lines), "the agent stopped early and was not told to keep going")
        self.assertEqual(lines[-1]["end"], "soft-budget")
        self.assertNotIn(str(Path.home()), json.dumps(lines))  # nothing of the contributor's machine in the record

    def test_a_proof_of_another_statement_or_by_native_decide_does_not_count_as_closing(self):
        self.stage([RECORD])
        other = "theorem Demo.sum_comm (a b : Nat) : a + 0 = a := by simp"
        cheat = "theorem Demo.sum_comm (a b : Nat) : a + b = b + a := by native_decide"
        steps = [
            {"say": "weaker", "tool": "mcp__verify__verify_full_script", "input": {"script": other}, "result": verified(other)},
            {"say": "native", "tool": "mcp__verify__verify_full_script", "input": {"script": cheat}, "result": verified(cheat)},
        ]
        r = self.run_runner({"turns": [steps]}, "--soft", "16", "--hard", "20")
        self.assertEqual(
            json.loads((self.d / "claims/mine/claim.json").read_text())["headlines"][0]["outcome"], "resisted", r.stdout + r.stderr
        )

    def test_runner_refuses_to_count_an_attempt_made_without_its_tools(self):
        self.stage([RECORD])
        r = self.run_runner({"connected": False, "turns": [[{"say": "I have no tools."}]]})
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("could not all be reached", r.stdout + r.stderr)
        self.assertFalse((self.d / "claims/mine/claim.json").exists())

    def test_more_than_ten_headlines_is_refused_by_the_runner(self):
        self.stage([{**RECORD, "name": f"Demo.t{i}", "statement": f"theorem Demo.t{i} : {i} = {i}"} for i in range(11)])
        r = self.run_runner({"turns": [[]]})
        self.assertIn("between 1 and 10", r.stdout + r.stderr)

    # ---- the gate
    def test_translations_and_promotions_are_exempt(self):
        self.stage([TRANSLATED])
        rc, out = self.gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("exempt", out)
        self.stage([TRANSLATED, RECORD])
        rc, out = self.gate("--promotion")
        self.assertEqual(rc, 0, out)

    def test_original_theorems_without_a_claim_are_refused(self):
        self.stage([RECORD])
        rc, out = self.gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("carries no blind re-proof claim", out)

    def test_all_headlines_closed_is_rejected_and_one_resisting_passes(self):
        second = {**RECORD, "name": "Demo.hard", "statement": "theorem Demo.hard : (2 : Nat) ^ 10 = 1024"}
        self.stage([RECORD, second])
        self.synthetic([RECORD, second], [True, True])
        rc, out = self.gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("every headline (2) was re-proved", out)
        self.synthetic([RECORD, second], [True, False])
        rc, out = self.gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("1 of 2 headline(s) resisted", out)

    def test_what_the_gate_will_not_believe(self):
        def thin(lines, rec):  # a "resisted" run that barely tried
            del lines[4:-1]
            lines[-1].update(t=40.0, seconds=40.0)

        def quiet(lines, rec):  # a gap: the laptop slept
            for x in lines[6:]:
                x["t"] += 400

        def peeked(lines, rec):  # a built-in tool was available: not blind
            lines[1]["event"]["tools"] = C.ALLOWED_TOOLS + ["Read"]

        def reworded(lines, rec):  # the agent was told something else
            lines[0]["prompt"] += "\nDo not try very hard."

        def leaked(lines, rec):
            lines[2]["event"]["message"]["content"][0]["text"] = "my token is ghp_" + "a" * 36

        for mutate, expect in (
            (thin, "needs a full attempt"),
            (quiet, "not one continuous attempt"),
            (peeked, "not blind"),
            (reworded, "not the test's"),
            (leaked, "looks like a credential"),
        ):
            with self.subTest(mutate.__name__):
                self.setUp()
                self.stage([RECORD])
                self.synthetic([RECORD], [False], mutate=mutate)
                rc, out = self.gate()
                self.assertEqual(rc, 1, out)
                self.assertIn(expect, out)

    def test_edited_files_are_caught(self):
        self.stage([RECORD])
        out = self.synthetic([RECORD], [False])
        w = out / "1-Demo.sum_comm.working.md"
        w.write_text(w.read_text().replace("RESISTED", "RESISTED (honest!)"))
        rc, text = self.gate()
        self.assertEqual(rc, 1, text)
        self.assertIn("does not match the digest", text)
        # digests fixed up by hand too: the log still is not what the transcript renders to
        claim = json.loads((out / "claim.json").read_text())
        claim["headlines"][0]["working_sha256"] = C.sha256(w.read_bytes())
        claim["digest"] = C.digest(claim)
        (out / "claim.json").write_text(json.dumps(claim))
        rc, text = self.gate()
        self.assertEqual(rc, 1, text)
        self.assertIn("not what the transcript renders to", text)

    def test_claim_must_be_about_this_pr_by_its_author_against_main(self):
        self.stage([RECORD])
        out = self.synthetic([RECORD], [False])
        claim = json.loads((out / "claim.json").read_text())
        claim["attested_by"] = "Somebody Else <else@example.com>"
        claim["pinned_start"] = {k: "f" * 40 for k in claim["pinned_start"]}
        claim["digest"] = C.digest(claim)
        (out / "claim.json").write_text(json.dumps(claim))
        rc, text = self.gate()
        self.assertEqual(rc, 1, text)
        self.assertIn("signed off no commit", text)
        self.assertIn("not a commit of main", text)

    def test_a_headline_that_is_not_in_the_pr_is_refused(self):
        self.stage([RECORD])
        self.synthetic([{**RECORD, "name": "Demo.elsewhere"}], [False])
        rc, text = self.gate()
        self.assertEqual(rc, 1, text)
        self.assertIn("is not an original theorem added by this PR", text)


if __name__ == "__main__":
    unittest.main()
