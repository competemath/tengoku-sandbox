"""fossa_check.py: FOSSA's three verdicts on the PR's head commit must all be success; silence is not a pass."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

import yaml

CI = Path(__file__).resolve().parents[1]
WORKFLOW = CI.parents[1] / ".github" / "workflows" / "pr-gate.yml"
sys.path.insert(0, str(CI))
import fossa_check as fc  # noqa: E402

BOT = {"login": "fossa-integration[bot]"}
OK = [
    {
        "context": c,
        "state": "success",
        "description": "All checks passed.",
        "creator": BOT,
        "target_url": "https://app.fossa.com/projects/x",
    }
    for c in fc.CONTEXTS
]


def with_state(context: str, state: str, **extra) -> list[dict]:
    return [{**s, "state": state, **extra} if s["context"] == context else s for s in OK]


class Judge(unittest.TestCase):
    def test_all_three_success_is_ok(self):
        self.assertEqual(fc.judge(OK)[0], "ok")

    def test_each_context_failing_alone_is_bad(self):
        for ctx in fc.CONTEXTS:
            for state in ("error", "failure"):
                with self.subTest(ctx=ctx, state=state):
                    self.assertEqual(fc.judge(with_state(ctx, state))[0], "bad")

    def test_a_missing_or_pending_context_waits_and_is_never_ok(self):
        for ctx in fc.CONTEXTS:
            self.assertEqual(fc.judge([s for s in OK if s["context"] != ctx])[0], "wait")
            self.assertEqual(fc.judge(with_state(ctx, "pending"))[0], "wait")
        self.assertEqual(fc.judge([])[0], "wait")

    def test_a_failure_wins_over_a_missing_context(self):
        self.assertEqual(fc.judge([{"context": "Security Analysis", "state": "error", "creator": BOT}])[0], "bad")

    def test_a_status_not_posted_by_fossa_is_ignored_whatever_it_says(self):
        """A collaborator with commit-status write access could post `success` under FOSSA's context names (CodeRabbit, #328)."""
        forged = [{**s, "creator": {"login": "someone"}} for s in OK]
        self.assertEqual(fc.judge(forged)[0], "wait")
        self.assertEqual(fc.judge([{**s, "creator": None} for s in OK])[0], "wait")
        self.assertEqual(fc.judge([{**s, "target_url": "https://evil.example/"} for s in OK])[0], "wait")
        # FOSSA's own pending status carries no link yet; its final one does
        self.assertEqual(fc.judge([{**s, "target_url": None, "state": "pending"} for s in OK])[0], "wait")
        self.assertEqual(fc.judge([{**s, "target_url": None} for s in OK])[0], "ok")
        # a forged failure is not a verdict either
        self.assertEqual(fc.judge(OK + [{"context": "Security Analysis", "state": "error", "creator": {"login": "someone"}}])[0], "ok")

    def test_other_statuses_do_not_count(self):
        other = [{"context": "codecov/patch", "state": "success"}, {"context": "CodeRabbit", "state": "success"}]
        self.assertEqual(fc.judge(other)[0], "wait")
        self.assertEqual(fc.judge([*OK, {"context": "codecov/patch", "state": "error"}])[0], "ok")

    def test_only_fossas_own_link_is_quoted_and_everything_is_bounded(self):
        mine = "https://app.fossa.com/projects/x"
        self.assertIn(mine, " ".join(fc.judge(with_state("Security Analysis", "error", target_url=mine))[1]))
        for url in ("https://evil.example/x", "http://app.fossa.com/x", "javascript:alert(1)", ""):
            self.assertNotIn(url or "<none>", " ".join(fc.judge(with_state("Security Analysis", "error", target_url=url))[1]))
        long = fc.judge(with_state("Security Analysis", "error", description="d" * 500, target_url=FOSSA + "a" * 900))[1]
        self.assertTrue(all(len(line) < 500 for line in long))


FOSSA = fc.FOSSA_URL


class NewestPerContext(unittest.TestCase):
    """The statuses come newest first; a context's first entry is its current state, an older `pending` behind a `success` does not count."""

    def test_an_older_pending_behind_a_success_does_not_hide_it(self):
        older = [{**s, "state": "pending", "target_url": None} for s in OK]
        self.assertEqual(fc.judge(OK + older)[0], "ok")
        self.assertEqual(fc.judge(older + OK)[0], "wait")  # the pending ones are newest: still waiting

    def test_the_fetch_reads_every_page_of_the_per_status_endpoint_which_carries_the_creator(self):
        """The combined endpoint leaves `creator` out: every status looked forged and the gate waited for verdicts that were there (2026-10-07).
        Every page is read (CodeRabbit, #340): a verdict on the second page of a busy commit is a verdict."""
        page1 = [{"context": "CodeRabbit", "state": "success"}] * 2
        page2 = [{"context": "Security Analysis", "state": "success", "creator": BOT, "target_url": FOSSA + "x"}]
        with mock.patch.object(fc.subprocess, "run") as run:
            run.return_value = mock.Mock(returncode=0, stdout=json.dumps([page1, page2]), stderr="")
            got = fc.fetch("o/r", "a" * 40)
            args = run.call_args[0][0]
        self.assertIn("repos/o/r/commits/" + "a" * 40 + "/statuses?per_page=100", args)
        self.assertIn("--paginate", args)
        self.assertEqual(got, page1 + page2)  # flattened, in order


class Waiting(unittest.TestCase):
    def run_wait(self, answers, minutes=1):
        """answers: what each successive lookup returns (a list of statuses, or an Exception to raise)."""
        calls, now = iter(answers), [0.0]

        def fetch(repo, sha):
            a = next(calls, answers[-1])
            if isinstance(a, Exception):
                raise a
            return a

        def sleep(s):
            now[0] += s

        return fc.wait_for_verdict("o/r", "a" * 40, minutes, fetch=fetch, sleep=sleep, clock=lambda: now[0]), now[0]

    def test_a_verdict_that_arrives_late_is_waited_for(self):
        (verdict, _), waited = self.run_wait([[], OK[:1], OK])
        self.assertEqual(verdict, "ok")
        self.assertEqual(waited, 40)

    def test_silence_to_the_end_is_a_failure_not_a_pass(self):
        (verdict, lines), waited = self.run_wait([[]], minutes=2)
        self.assertEqual(verdict, "wait")
        self.assertGreaterEqual(waited, 120)
        self.assertIn("not reported yet", lines[0])

    def test_a_failure_returns_at_once(self):
        (verdict, _), waited = self.run_wait([with_state("Dependency Quality", "error")])
        self.assertEqual((verdict, waited), ("bad", 0))

    def test_a_failed_lookup_is_asked_again(self):
        (verdict, _), _ = self.run_wait([RuntimeError("HTTP 502"), OK])
        self.assertEqual(verdict, "ok")

    def test_a_lookup_that_never_works_ends_as_a_failure(self):
        (verdict, lines), _ = self.run_wait([RuntimeError("HTTP 502")])
        self.assertEqual(verdict, "wait")
        self.assertIn("HTTP 502", lines[0])


class Main(unittest.TestCase):
    def exits(self, argv, verdict, lines=("l",)):
        with mock.patch.object(fc, "wait_for_verdict", return_value=(verdict, list(lines))), mock.patch("builtins.print"):
            try:
                fc.main(argv)
            except SystemExit as e:
                return e.code
        return 0

    ARGS = ["o/r", "a" * 40]

    def test_exit_codes(self):
        self.assertEqual(self.exits(self.ARGS, "ok"), 0)
        self.assertEqual(self.exits(self.ARGS, "bad"), 1)
        self.assertEqual(self.exits(self.ARGS, "wait"), 1)

    def test_bad_arguments_are_refused_before_any_lookup(self):
        for argv in (
            [],
            ["o/r"],
            ["o r", "a" * 40],
            ["o/r", "A" * 40],
            ["o/r", "a" * 39],
            ["o/r", "a" * 40 + "; rm"],
            ["../x", "a" * 40],
            ["o/..", "a" * 40],
            ["o/.", "a" * 40],
            ["o/r\n", "a" * 40],
            ["o/r", "a" * 40 + "\n"],
        ):
            with mock.patch.object(fc, "wait_for_verdict") as w, mock.patch("builtins.print"):
                self.assertRaises(SystemExit, fc.main, argv)
                w.assert_not_called()


class Wiring(unittest.TestCase):
    """The check is only as good as the job that runs it and the required `pr-gate` that depends on it."""

    jobs = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))["jobs"]

    def test_pr_gate_depends_on_the_fossa_job(self):
        self.assertIn("fossa", self.jobs["pr-gate"]["needs"])

    def test_the_job_runs_the_script_on_the_head_commit_of_this_repository_with_read_only_rights(self):
        job = self.jobs["fossa"]
        self.assertEqual(job["if"], "github.event_name == 'pull_request_target'")  # a queue entry never gets FOSSA's statuses
        self.assertEqual(job["permissions"], {"contents": "read", "statuses": "read"})
        runs = [s["run"] for s in job["steps"] if "run" in s]
        self.assertEqual(runs[-1], 'python3 scripts/ci/fossa_check.py "$GITHUB_REPOSITORY" "$HEAD"')
        self.assertFalse([s for s in job["steps"] if "actions/checkout" in s.get("uses", "")])  # the base comes by plain git (Sonar S7631)
        self.assertIn('git checkout -q --detach "$BASE"', runs[0])

    def aggregate(self, fossa: str) -> int:
        step = next(s for s in self.jobs["pr-gate"]["steps"] if s.get("name") == "Every job of this PR's class passed")
        code = step["run"].split("python3 -c '", 1)[1].rsplit("'", 1)[0]
        needs = {"classify": {"result": "success"}, "credits": {"result": "success"}, "fossa": {"result": fossa}}
        return subprocess.run([sys.executable, "-c", code], input=json.dumps(needs), text=True, capture_output=True).returncode

    def test_a_failed_or_cancelled_fossa_job_fails_pr_gate_and_a_passed_or_skipped_one_does_not(self):
        self.assertEqual([self.aggregate(r) for r in ("failure", "cancelled")], [1, 1])
        self.assertEqual([self.aggregate(r) for r in ("success", "skipped")], [0, 0])


if __name__ == "__main__":
    unittest.main()
