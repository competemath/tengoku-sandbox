"""ledger_guard.py (docs/ci-records.md): the records branches only grow. Synthetic branches; every rule has a hostile commit that must be found and an honest one that must pass."""

from __future__ import annotations

import datetime as dt
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))

import ledger_guard as lg  # noqa: E402
from warden import audit, caps  # noqa: E402


def ledger_text(n, start=0, prev=caps.GENESIS, kind="verdict"):
    """`n` valid juridicator-style entries (seq/kind/body/prev/hash), and the hash of the last."""
    out = b""
    for i in range(start, start + n):
        e = caps.make_entry(i, kind, {"head_sha": "a" * 40, "n": i}, prev)
        out += caps.entry_line(e)
        prev = e["hash"]
    return out, prev


def audit_record(i):
    return {
        "schema": audit.SCHEMA_ID,
        "ts": "2026-10-09T10:00:00Z",
        "actor": "tengoku-bot",
        "action": "ci.run",
        "target": f"o/r {i}:1",
        "outcome": "info",
    }


class Branch:
    def __init__(self):
        self.dir = Path(tempfile.mkdtemp())
        self.git("init", "-q", "-b", "records")

    def git(self, *a):
        env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
        return subprocess.run(["git", *a], cwd=self.dir, capture_output=True, text=True, check=True, env=env).stdout.strip()

    def put(self, rel, data):
        p = self.dir / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data if isinstance(data, bytes) else data.encode())

    def commit(self, msg="c"):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg)
        return self.git("rev-parse", "HEAD")

    def chain_files(self, per_file, files=2):
        """chain/ci-*.ndjson written by warden.audit.Chain, the chain running across the files."""
        work = Path(tempfile.mkdtemp())
        chain = audit.Chain(str(work), "ci")
        i = 0
        for day in range(files):
            for _ in range(per_file):
                chain.append(audit_record(i), f"2026-10-0{day + 1}")
                i += 1
        for p in sorted(work.glob("ci-*.ndjson")):
            self.put(f"chain/{p.name}", p.read_bytes())

    def problems(self, base, head):
        return lg.problems_of_range(str(self.dir), base, head), lg.problems_of_chain(str(self.dir), head)


class TrustLedger(unittest.TestCase):
    def setUp(self):
        self.b = Branch()
        text, self.tip = ledger_text(3)
        self.b.put("README.md", "ledger\n")
        self.b.put("ledger.jsonl", text)
        self.base = self.b.commit("base")

    def test_an_appended_entry_passes(self):
        more, _ = ledger_text(1, start=3, prev=self.tip)
        self.b.put("ledger.jsonl", (self.b.dir / "ledger.jsonl").read_bytes() + more)
        head = self.b.commit("append")
        range_problems, (chain_problems, notes) = self.b.problems(self.base, head)
        self.assertEqual((range_problems, chain_problems), ([], []))
        self.assertIn("4 entries", notes[0])

    def test_an_edited_entry_is_found_by_the_range_and_by_the_chain(self):
        data = (self.b.dir / "ledger.jsonl").read_bytes().replace(b'"n": 1', b'"n": 9', 1)
        self.b.put("ledger.jsonl", data + ledger_text(1, 3, self.tip)[0])
        head = self.b.commit("edit")
        range_problems, (chain_problems, _) = self.b.problems(self.base, head)
        self.assertTrue(any(p.startswith("append_only_violated ledger.jsonl") for p in range_problems), range_problems)
        self.assertTrue(any(p.startswith("chain_broken ledger.jsonl") for p in chain_problems), chain_problems)

    def test_a_removed_tail_is_found(self):
        lines = (self.b.dir / "ledger.jsonl").read_bytes().splitlines(keepends=True)
        self.b.put("ledger.jsonl", b"".join(lines[:2]))
        head = self.b.commit("drop the last verdict")
        range_problems, _ = self.b.problems(self.base, head)
        self.assertTrue(any("append_only_violated" in p for p in range_problems), range_problems)

    def test_a_deleted_ledger_is_found(self):
        self.b.git("rm", "-q", "ledger.jsonl")
        head = self.b.commit("delete")
        range_problems, _ = self.b.problems(self.base, head)
        self.assertTrue(any(p.startswith("delete_forbidden ledger.jsonl") for p in range_problems), range_problems)

    def test_a_ledger_that_became_a_symlink_is_found(self):
        os.remove(self.b.dir / "ledger.jsonl")
        os.symlink("/etc/passwd", self.b.dir / "ledger.jsonl")
        head = self.b.commit("link")
        range_problems, _ = self.b.problems(self.base, head)
        self.assertTrue(range_problems)

    def test_a_history_that_was_rewritten_is_not_a_pass(self):
        self.b.git("checkout", "-q", "--orphan", "other")
        self.b.put("ledger.jsonl", ledger_text(3)[0])
        head = self.b.commit("rewritten")
        range_problems, _ = self.b.problems(self.base, head)
        self.assertTrue(any("guard_error" in p for p in range_problems), range_problems)

    def test_the_readme_may_change(self):
        self.b.put("README.md", "ledger, with a better readme\n")
        head = self.b.commit("readme")
        self.assertEqual(self.b.problems(self.base, head)[0], [])


class CiRecords(unittest.TestCase):
    def setUp(self):
        self.b = Branch()
        self.b.chain_files(2)
        self.b.put("runs/2026-10-01/a.ndjson", '{"run_id": 1}\n')
        self.b.put("runs/README.md", "records\n")
        self.base = self.b.commit("base")

    def test_new_files_and_an_extended_chain_pass(self):
        work = Path(tempfile.mkdtemp())
        for p in (self.b.dir / "chain").glob("ci-*.ndjson"):
            (work / p.name).write_bytes(p.read_bytes())
        audit.Chain(str(work), "ci").append(audit_record(99), "2026-10-02")
        for p in work.glob("ci-*.ndjson"):
            self.b.put(f"chain/{p.name}", p.read_bytes())
        self.b.put("runs/2026-10-02/b.ndjson", '{"run_id": 2}\n')
        head = self.b.commit("hourly")
        range_problems, (chain_problems, notes) = self.b.problems(self.base, head)
        self.assertEqual((range_problems, chain_problems), ([], []))
        self.assertIn("5 entries", notes[0])

    def test_a_record_edited_after_the_fact_is_found(self):
        self.b.put("runs/2026-10-01/a.ndjson", '{"run_id": 1, "conclusion": "success"}\n')
        head = self.b.commit("shade the numbers")
        range_problems, _ = self.b.problems(self.base, head)
        self.assertTrue(any(p.startswith("record_changed runs/2026-10-01/a.ndjson (M") for p in range_problems), range_problems)

    def test_a_record_deleted_is_found_even_if_a_later_commit_adds_it_back(self):
        self.b.git("rm", "-q", "runs/2026-10-01/a.ndjson")
        self.b.commit("delete")
        self.b.put("runs/2026-10-01/a.ndjson", '{"run_id": 1}\n')
        head = self.b.commit("restore it")
        range_problems, _ = self.b.problems(self.base, head)
        self.assertTrue(any(p.startswith("record_changed runs/2026-10-01/a.ndjson (D in ") for p in range_problems), range_problems)

    def test_an_edited_chain_record_breaks_the_chain(self):
        p = self.b.dir / "chain" / "ci-2026-10-01.ndjson"
        self.b.put("chain/ci-2026-10-01.ndjson", p.read_bytes().replace(b'"outcome": "info"', b'"outcome": "deny"', 1))
        head = self.b.commit("edit")
        range_problems, (chain_problems, _) = self.b.problems(self.base, head)
        self.assertTrue(chain_problems and range_problems)

    def test_a_deleted_chain_file_is_found(self):
        self.b.git("rm", "-q", "chain/ci-2026-10-01.ndjson")
        head = self.b.commit("delete a day")
        range_problems, (chain_problems, _) = self.b.problems(self.base, head)
        self.assertTrue(any("delete_forbidden" in p for p in range_problems), range_problems)
        self.assertTrue(chain_problems)  # and the chain that is left starts in the middle

    def test_an_unchanged_head_has_nothing_to_report(self):
        self.assertEqual(
            self.b.problems(self.base, self.base),
            ([], ([], ["chain/: 4 entries in 2 files, head " + lg.audit.verify_dir(str(self.b.dir / "chain"), prefix="ci").head])),
        )


class Activity(unittest.TestCase):
    SINCE = dt.datetime(2026, 10, 7, tzinfo=dt.timezone.utc)

    def ev(self, kind, who="github-actions[bot]", when="2026-10-09T10:00:00Z"):
        return {"activity_type": kind, "timestamp": when, "actor": {"login": who}}

    def test_a_force_push_or_a_deletion_is_a_violation(self):
        v, n = lg.judge_activity([self.ev("force_push", "mikael-bashir"), self.ev("branch_deletion")], self.SINCE)
        self.assertEqual(len(v), 2)
        self.assertIn("force_push by mikael-bashir", v[0])
        self.assertEqual(n, [])

    def test_a_push_by_the_actions_identity_is_normal_and_by_anyone_else_is_named(self):
        v, n = lg.judge_activity([self.ev("push"), self.ev("push", "someone"), self.ev("branch_creation", "mikael-bashir")], self.SINCE)
        self.assertEqual(v, [])
        self.assertEqual(n, ["push by someone at 2026-10-09T10:00:00Z"])

    def test_old_events_are_ignored_and_a_record_without_a_time_is_not(self):
        v, _ = lg.judge_activity([self.ev("force_push", when="2026-09-01T00:00:00Z")], self.SINCE)
        self.assertEqual(v, [])
        v, _ = lg.judge_activity([{"activity_type": "push"}, "junk"], self.SINCE)
        self.assertEqual(len(v), 1)

    def test_a_login_is_printed_plain(self):
        v, _ = lg.judge_activity([self.ev("force_push", "x`](http://evil)")], self.SINCE)
        self.assertNotIn("`", v[0])
        self.assertNotIn("(", v[0])


class Cli(unittest.TestCase):
    def test_check_exits_1_on_a_change_and_0_on_an_append(self):
        b = Branch()
        text, tip = ledger_text(2)
        b.put("ledger.jsonl", text)
        base = b.commit("base")
        more, _ = ledger_text(1, 2, tip)
        b.put("ledger.jsonl", text + more)
        good = b.commit("append")
        run = lambda head: subprocess.run(  # noqa: E731
            [
                sys.executable,
                str(CI / "ledger_guard.py"),
                "check",
                "--repo",
                str(b.dir),
                "--branch",
                "trust-ledger",
                "--base",
                base,
                "--head",
                head,
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(run(good).returncode, 0, run(good).stdout)
        b.put("ledger.jsonl", text.replace(b'"n": 0', b'"n": 7') + more)
        bad = b.commit("edit")
        done = run(bad)
        self.assertEqual(done.returncode, 1)
        self.assertIn("ledger.jsonl", done.stdout)

    def test_bad_input_is_exit_2(self):
        done = subprocess.run(
            [sys.executable, str(CI / "ledger_guard.py"), "check", "--branch", "trust-ledger", "--base", "main", "--head", "x"],
            capture_output=True,
        )
        self.assertEqual(done.returncode, 2)


if __name__ == "__main__":
    unittest.main()
