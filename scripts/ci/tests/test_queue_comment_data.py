"""queue_comment.py in two steps: the job that built the group's code writes facts (no token); the job that may write validates
them as data, renders them inside fences they cannot close, and posts."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))
import queue_comment as qc  # noqa: E402

HOSTILE = {
    "kind": "lean",
    "prs": ["10", "2; rm -rf /", "x", "30", "٣"],
    "file": "Tengoku/Lib/`evil`.lean",
    "line": "4; DROP",
    "col": "2x",
    "msg": "unsolved goals\n```\n[click here](https://evil.example)\n```\n" + "z" * 5000,
    "src": "theorem t : 1 = 2 := by ``` simp",
    "record": "bad`name",
    "run_url": "javascript:alert(1)",
    "stat": ["Tengoku/A.lean", "x`y", "../../etc/passwd "],
}


def run_cli(*args: str, env: dict | None = None, cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(CI / "queue_comment.py"), *args], cwd=cwd, capture_output=True, text=True, env={**os.environ, **(env or {})}
    )


class Validation(unittest.TestCase):
    def test_nothing_that_is_not_the_right_shape_survives(self):
        v = qc.valid(HOSTILE)
        self.assertEqual(v["prs"], ["10", "30"])
        self.assertEqual((v["file"], v["record"], v["run_url"]), ("?", "?", "(no link)"))
        self.assertEqual((v["line"], v["col"]), (0, "0"))
        self.assertEqual(v["stat"], ["Tengoku/A.lean"])
        self.assertLessEqual(len(v["msg"]), qc.LIMITS["msg"])

    def test_garbage_facts_do_not_crash(self):
        for facts in ({}, {"prs": "12", "stat": None}, {"kind": 5, "prs": [None, 3.5, "7"]}):
            try:
                qc.valid(facts)
            except TypeError:
                self.fail(f"valid() crashed on {facts!r}")

    def test_the_comment_cannot_have_its_fence_closed_from_inside(self):
        where, detail, _ = qc.describe(qc.valid(HOSTILE))
        self.assertEqual(detail.count("```"), 4)  # the text block and the lean block: opening and closing, and no more
        self.assertIn("'''", detail)
        self.assertEqual(where, "`?:0:0`")

    def test_a_log_error_line_stays_inside_a_fence_as_well(self):
        _, detail, _ = qc.describe(qc.valid({"kind": "log", "err": "error: x\n```\n**bold**", "prs": ["1"]}))
        self.assertEqual(detail.count("```"), 2)


class TwoSteps(unittest.TestCase):
    def test_facts_are_written_without_posting_and_posted_from_the_facts(self):
        d = Path(tempfile.mkdtemp())
        (d / "build.log").write_text("error: Tengoku/Lib/_candidate_Basic.lean:4:2: unsolved goals\n")
        out = d / "facts.json"
        env = {"TENGOKU_CI_ROOT": str(d), "PATH": "/nonexistent"}  # no gh, no git: extraction must not need either to write facts
        subprocess.run(["git", "init", "-q", str(d)], check=True)
        subprocess.run(
            ["git", "-c", "user.email=t@t", "-c", "user.name=t", "-C", str(d), "commit", "-q", "--allow-empty", "-m", "base"], check=True
        )
        r = run_cli(
            "--facts",
            str(out),
            str(d / "build.log"),
            "https://github.com/o/r/actions/runs/1",
            env={**os.environ, **env, "PATH": os.environ["PATH"]},
            cwd=d,
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        facts = json.loads(out.read_text())
        self.assertEqual((facts["kind"], facts["file"], facts["line"]), ("lean", "Tengoku/Lib/_candidate_Basic.lean", 4))
        facts["prs"] = ["10", "11"]
        out.write_text(json.dumps(facts))
        r = run_cli(
            "--post",
            str(out),
            env={
                "TENGOKU_CI_ROOT": str(d),
                "TENGOKU_COMMENT_DRY": "1",
                "GITHUB_REF": "refs/heads/gh-readonly-queue/main/pr-11-" + "a" * 40,
            },
        )
        self.assertIn("would comment on: #11\n", r.stdout)
        self.assertIn("unsolved goals", r.stdout)

    def test_a_hostile_facts_file_posts_nothing_hostile(self):
        d = Path(tempfile.mkdtemp())
        f = d / "facts.json"
        f.write_text(json.dumps(HOSTILE))
        r = run_cli("--post", str(f), env={"TENGOKU_COMMENT_DRY": "1", "GITHUB_REF": "refs/heads/gh-readonly-queue/main/pr-10-" + "a" * 40})
        self.assertIn("would comment on: #10\n", r.stdout)
        self.assertNotIn("\n```\n[click here]", r.stdout)
        self.assertNotIn("2; rm", r.stdout)
        self.assertNotIn("javascript:", r.stdout)

    def test_the_recipient_is_the_queue_entry_and_never_a_pr_the_facts_name(self):
        d = Path(tempfile.mkdtemp())
        f = d / "facts.json"
        f.write_text(json.dumps({"kind": "log", "err": "error: x", "prs": ["99"], "run_url": "https://x.example/r"}))
        ref = "refs/heads/gh-readonly-queue/main/pr-11-" + "b" * 40
        r = run_cli("--post", str(f), env={"TENGOKU_COMMENT_DRY": "1", "GITHUB_REF": ref})
        self.assertIn("would comment on: #11\n", r.stdout)  # not in the facts at all, and the one the facts name is not told
        self.assertNotIn("#99\n", r.stdout.split("Removed from")[0])
        r = run_cli("--post", str(f), env={"TENGOKU_COMMENT_DRY": "1", "GITHUB_REF": ""})
        self.assertNotIn("would comment", r.stdout)  # no queue ref, no recipient: nothing is posted

    def test_a_path_outside_the_working_and_temporary_directories_is_refused(self):
        r = run_cli("--post", "/etc/hosts", cwd=Path(tempfile.mkdtemp()))
        self.assertEqual(r.returncode, 1)
        self.assertIn("outside the working directory", r.stdout + r.stderr)

    def test_a_log_cannot_make_extraction_read_outside_the_tree(self):
        self.assertEqual(qc.source_of("../../../../etc/hosts", 1), ("", "?"))
        self.assertEqual(qc.source_of("/etc/hosts", 1), ("", "?"))

    def test_facts_without_any_pr_post_nothing(self):
        d = Path(tempfile.mkdtemp())
        f = d / "facts.json"
        f.write_text(json.dumps({"kind": "log", "err": "error: x", "prs": ["not a number"], "run_url": "https://x.example/r"}))
        r = run_cli("--post", str(f), env={"TENGOKU_COMMENT_DRY": "1"})
        self.assertEqual(r.returncode, 0)
        self.assertNotIn("would comment", r.stdout)
        self.assertIn("Removed from the merge queue", r.stdout)


if __name__ == "__main__":
    unittest.main()
