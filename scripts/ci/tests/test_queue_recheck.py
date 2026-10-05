"""The merge group's re-check runs main's scripts on the merged result, from a checkout of the BASE: the one thing it cannot run is a script that the group itself
introduces. Regression (tengoku-sandbox#363, 2026-10-05): the PR that added imports_resolve.py and its queue step was ejected by the step, `can't open file`.

The step is executed here as a shell script in a temporary directory, with and without the script in it."""

from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

TREE = Path(__file__).resolve().parents[3]
WORKFLOW = TREE / ".github" / "workflows" / "pr-gate.yml"


def step_run(name_part: str) -> str:
    jobs = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))["jobs"]
    found = [s["run"] for s in jobs["queue-recheck"]["steps"] if name_part in s.get("name", "") and "run" in s]
    assert len(found) == 1, f"expected one queue-recheck step named like {name_part!r}, found {len(found)}"
    return found[0]


class ImportsStep(unittest.TestCase):
    def run_step(self, script_body: str | None):
        with tempfile.TemporaryDirectory() as d:
            if script_body is not None:
                p = Path(d) / "scripts" / "ci"
                p.mkdir(parents=True)
                (p / "imports_resolve.py").write_text(script_body)
            r = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c", step_run("Every import still resolves")],
                cwd=d,
                capture_output=True,
                text=True,
                env={**os.environ, "BASE": "b", "HEAD": "h"},
                check=False,
            )
            return r.returncode, r.stdout + r.stderr

    def test_the_group_that_introduces_the_script_is_not_ejected_for_lacking_it(self):
        rc, out = self.run_step(None)
        self.assertEqual(rc, 0, out)
        self.assertIn("introduced by this group", out)

    def test_once_main_has_the_script_it_runs_and_its_failure_fails_the_step(self):
        rc, out = self.run_step("import sys\nprint('ran', sys.argv[1:])\nsys.exit(3)\n")
        self.assertEqual(rc, 3, out)
        self.assertIn("ran ['b', 'h']", out)

    def test_once_main_has_the_script_a_pass_passes(self):
        rc, out = self.run_step("print('imports OK')\n")
        self.assertEqual(rc, 0, out)
        self.assertIn("imports OK", out)


if __name__ == "__main__":
    unittest.main()
