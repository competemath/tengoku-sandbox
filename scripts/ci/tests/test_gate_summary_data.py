"""gate_summary.py is the one job that writes to a PR, and what it quotes is text a PR author influences: data, fenced, bounded."""

from __future__ import annotations

import os
import sys
import unittest
from pathlib import Path
from unittest import mock

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))
os.environ.update({"GITHUB_REPOSITORY": "o/r", "GITHUB_RUN_ID": "1", "PR_NUMBER": "7", "HEAD_SHA": "abcdef012345", "PR_CLASS": "content"})
import gate_summary as gs  # noqa: E402

FAILED = [{"name": "credits", "conclusion": "failure", "databaseId": 5, "steps": [{"name": "credits", "conclusion": "failure"}]}]


class Fence(unittest.TestCase):
    def test_a_quote_cannot_close_its_fence(self):
        self.assertNotIn("```", gs.fenced("a ``` b ````` c"))
        self.assertEqual(gs.fenced("plain text"), "plain text")

    def test_a_failed_jobs_excerpt_stays_inside_one_fence(self):
        with mock.patch.object(gs, "excerpt", return_value="evil ```\n@everyone [x](https://example.com)"):
            body, failed = gs.render(FAILED)
        self.assertTrue(failed)
        self.assertEqual(body.count("```"), 2)  # one block: its opening and its closing fence


class Advisory(unittest.TestCase):
    LOG = [
        "- before the heading: not a hit",
        "### sorry / admit in this PR (advisory: the merge queue's build decides)",
        "",
        "- data/staging/a.jsonl:3 — Lib.one",
        "not a bullet",
        "- " + "x" * 400,
    ]

    def test_only_the_bulleted_lines_under_the_heading_count_and_are_bounded(self):
        hits = gs.advisory_hits(self.LOG)
        self.assertEqual(hits[0], "- data/staging/a.jsonl:3 — Lib.one")
        self.assertEqual(len(hits), 2)
        self.assertEqual(len(hits[1]), 200)
        self.assertEqual(len(gs.advisory_hits(["### sorry / admit"] + [f"- {i}" for i in range(50)])), 20)
        self.assertEqual(gs.advisory_hits(["- no heading"]), [])

    def test_log_prefixes_timestamps_and_colours_are_stripped(self):
        self.assertEqual(gs.log_lines("job\tstep\t2026-10-04T10:00:00.1234567Z \x1b[36;1m- a\x1b[0m"), ["- a"])

    def test_the_advisory_reaches_the_comment_for_both_verdicts(self):
        ok, _ = gs.render([{"name": "credits", "conclusion": "success", "databaseId": 1, "steps": []}], "### advisory text")
        self.assertTrue(ok.endswith("### advisory text"))
        with mock.patch.object(gs, "excerpt", return_value="x"):
            bad, _ = gs.render(FAILED, "### advisory text")
        self.assertTrue(bad.endswith("### advisory text"))

    def test_a_failing_advisory_job_is_not_a_failed_check(self):
        body, failed = gs.render([{"name": "sorry-advisory", "conclusion": "failure", "databaseId": 2, "steps": []}])
        self.assertFalse(failed)
        self.assertIn("all checks passed", body)

    def test_the_comment_quotes_the_hits_in_a_fence(self):
        jobs = [{"name": "sorry-advisory", "conclusion": "success", "databaseId": 3, "steps": []}]
        log = "job\tstep\t2026-10-04T10:00:00Z ### sorry / admit in this PR\njob\tstep\t2026-10-04T10:00:00Z - p.lean:1 ``` @user"
        with mock.patch.object(gs, "gh", return_value=log):
            text = gs.advisory(jobs)
        self.assertEqual(text.count("```"), 2)
        self.assertIn("p.lean:1", text)
        self.assertEqual(gs.advisory([]), "")


if __name__ == "__main__":
    unittest.main()
