"""pr-gate.yml runs main's CURRENT scripts on every PR: each job checks out the base branch's tip (env SCRIPTS), not the base commit the event
recorded (env BASE, which stays the commit the diff is measured against). Regression (2026-10-07): every PR opened before the FOSSA gate
landed failed its new job with "can't open file", and only a push to the PR could fix it. The one job that compiles the PR's records
(vacuity) lays the PR's data changes over that tip as a BASE..HEAD patch: a snapshot of HEAD would undo what main changed since BASE."""

from __future__ import annotations

import unittest
from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "pr-gate.yml"
DOC = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


class ScriptsFromMain(unittest.TestCase):
    def test_scripts_is_the_base_branchs_tip_on_a_pr_and_the_entrys_base_in_the_queue(self):
        self.assertEqual(
            DOC["env"]["SCRIPTS"],
            "${{ github.event.pull_request.base.ref && format('refs/heads/{0}', github.event.pull_request.base.ref) || github.event.merge_group.base_sha }}",
        )
        self.assertEqual(
            DOC["env"]["BASE"], "${{ github.event.pull_request.base.sha || github.event.merge_group.base_sha }}"
        )  # the diff base is unchanged

    def test_vacuity_applies_the_prs_data_changes_as_a_patch_not_a_snapshot(self):
        runs = [s.get("run", "") for s in DOC["jobs"]["vacuity"]["steps"]]
        self.assertIn('git diff --binary "$BASE" "$HEAD" -- data | git apply --3way --index --allow-empty', runs)
        for name, job in DOC["jobs"].items():
            for s in job["steps"]:
                self.assertNotIn('git checkout -q "$HEAD" --', s.get("run", ""), name)  # a snapshot of HEAD undoes main's changes since BASE

    def test_no_job_checks_out_the_recorded_base_commit(self):
        checked_out_base, checked_out_scripts, plain = [], [], []
        for name, job in DOC["jobs"].items():
            for s in job["steps"]:
                if "actions/checkout" in s.get("uses", ""):
                    (checked_out_base if s["with"].get("ref") == "${{ env.BASE }}" else checked_out_scripts).append(name)
                if "git checkout -q --detach" in s.get("run", ""):
                    plain.append((name, s["run"]))
        self.assertEqual(checked_out_base, [])
        self.assertGreater(len(checked_out_scripts), 5)
        self.assertGreater(len(plain), 3)
        for name, run in plain:
            self.assertIn("git checkout -q --detach origin/scripts", run, name)
            self.assertIn('"+$SCRIPTS:refs/remotes/origin/scripts" "$BASE"', run, name)  # the diff base is fetched too


if __name__ == "__main__":
    unittest.main()
