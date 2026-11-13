"""pr-gate.yml runs main's CURRENT scripts on every PR: each job checks out the base branch's tip (env SCRIPTS), not the base commit the event
recorded (env BASE, which stays the commit the diff is measured against). Regression (2026-10-07): every PR opened before the FOSSA gate
landed failed its new job with "can't open file", and only a push to the PR could fix it. The one job that compiles the PR's records
(vacuity) lays the PR's data changes over that tip: a snapshot of HEAD alone would undo what main changed since BASE."""

from __future__ import annotations

import os
import subprocess
import tempfile
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

    def test_vacuity_lays_the_prs_data_changes_over_mains_tip(self):
        run = next(s["run"] for s in DOC["jobs"]["vacuity"]["steps"] if 'git checkout -q "$HEAD" -- data' in s.get("run", ""))
        self.assertIn(
            'git diff --no-renames --name-only -z "$BASE" origin/scripts -- data', run
        )  # what main changed under data/ since the PR's base
        self.assertIn("git checkout -q origin/scripts -- ", run)  # comes back from main: a snapshot of HEAD alone would undo it
        self.assertIn("exit 1", run)  # a file both changed fails the job; the queue would conflict on it too
        self.assertNotIn("git apply", run)  # pr-code: no patch in a job that holds the token

    def overlay(self, base: dict, main: dict, pr: dict) -> tuple[subprocess.CompletedProcess, Path]:
        """Run the vacuity job's data-overlay step in a real repository: BASE holds `base`, main's tip (origin/scripts) is BASE with `main`
        applied, the PR's HEAD is BASE with `pr` applied (a value of None deletes the file); the job starts on main's tip."""
        run = next(s["run"] for s in DOC["jobs"]["vacuity"]["steps"] if 'git checkout -q "$HEAD" -- data' in s.get("run", ""))
        repo = Path(tempfile.mkdtemp())
        self.addCleanup(subprocess.run, ["rm", "-rf", str(repo)])

        def git(*a: str) -> str:
            return subprocess.run(["git", *a], cwd=repo, check=True, capture_output=True, text=True).stdout.strip()

        def apply(files: dict) -> None:
            for name, text in files.items():
                path = repo / name
                if text is None:
                    path.unlink()
                else:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(text)
            git("add", "-A")
            git("-c", "user.name=t", "-c", "user.email=t@example.com", "commit", "-q", "--allow-empty", "-m", "c")

        git("init", "-q")
        apply(base)
        base_sha = git("rev-parse", "HEAD")
        apply(main)
        git("update-ref", "refs/remotes/origin/scripts", git("rev-parse", "HEAD"))
        git("checkout", "-q", "--detach", base_sha)
        apply(pr)
        head_sha = git("rev-parse", "HEAD")
        git("checkout", "-q", "--detach", "origin/scripts")
        env = {**os.environ, "BASE": base_sha, "HEAD": head_sha}
        return subprocess.run(["bash", "-e", "-c", run], cwd=repo, env=env, capture_output=True, text=True), repo

    BASE = {"data/a.jsonl": "a\n", "data/b.jsonl": "b\n", "data/c.jsonl": "c\n", "data/with space.jsonl": "s\n", "scripts/x.py": "x\n"}

    def test_the_overlay_has_the_prs_changes_and_mains_since_the_base(self):
        main = {"data/b.jsonl": "b main\n", "data/with space.jsonl": "s main\n", "data/new.jsonl": "new\n", "scripts/x.py": "x main\n"}
        done, repo = self.overlay(self.BASE, main, {"data/a.jsonl": "a pr\n"})
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual((repo / "data/a.jsonl").read_text(), "a pr\n")
        self.assertEqual((repo / "data/b.jsonl").read_text(), "b main\n")
        self.assertEqual((repo / "data/with space.jsonl").read_text(), "s main\n")  # a name with a space survives
        self.assertEqual((repo / "data/new.jsonl").read_text(), "new\n")
        self.assertEqual((repo / "scripts/x.py").read_text(), "x main\n")  # scripts stay main's

    def test_a_file_main_deleted_since_the_base_is_gone_from_the_overlay(self):
        done, repo = self.overlay(self.BASE, {"data/c.jsonl": None}, {"data/a.jsonl": "a pr\n"})
        self.assertEqual(done.returncode, 0, done.stderr)  # regression: `pathspec 'data/c.jsonl' did not match`
        self.assertFalse((repo / "data/c.jsonl").exists())
        self.assertEqual((repo / "data/a.jsonl").read_text(), "a pr\n")

    def test_a_file_both_changed_fails_and_is_named(self):
        done, _ = self.overlay(self.BASE, {"data/with space.jsonl": "s main\n"}, {"data/with space.jsonl": "s pr\n"})
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("rebase: data/with space.jsonl", done.stdout)

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
