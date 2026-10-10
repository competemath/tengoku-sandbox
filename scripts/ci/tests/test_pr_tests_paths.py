"""pr-tests.yml is the PR's own lint and unit-test suite (about 15 runner-minutes). A content PR (a library's modules, the data records: an intake or extend part, a staging
or tag PR) changes no code the suite tests, and the lane opens hundreds of them a day, so such a PR skips the workflow: `paths-ignore`. Everything else runs it, and
what the merge needs does not depend on it: a workflow that a path filter skips leaves no check, so a required check produced there would stay pending for ever."""

from __future__ import annotations

import fnmatch
import unittest
from pathlib import Path

import yaml

WORKFLOWS = Path(__file__).resolve().parents[3] / ".github" / "workflows"
DOC = yaml.safe_load((WORKFLOWS / "pr-tests.yml").read_text(encoding="utf-8"))
ON = DOC[True]  # `on:` is read as True by YAML 1.1
REQUIRED = ("pr-gate", "queue-gate")


def skipped(path: str) -> bool:
    """GitHub's `*` does not cross `/` and `**` does; fnmatch's `*` crosses, so `Tengoku/**` is matched as a prefix here."""
    return any(path.startswith(p[:-2]) if p.endswith("/**") else fnmatch.fnmatch(path, p) for p in ON["pull_request"]["paths-ignore"])


class PrTestsPaths(unittest.TestCase):
    def test_a_content_only_pull_request_skips_it(self):
        for path in (
            "Tengoku/Lib/Basic.lean",
            "Tengoku/All.lean",
            "Tengoku/Lib.lean",
            "data/intake/lib/manifest.jsonl",
            "data/staging/lib/20261010T000000Z-000.jsonl",
        ):
            self.assertTrue(skipped(path), path)

    def test_a_change_to_code_or_configuration_runs_it(self):
        for path in (
            "scripts/ci/classify.py",
            "scripts/ci/tests/test_gates.py",
            ".github/workflows/pr-gate.yml",
            "pyproject.toml",
            ".pre-commit-config.yaml",
            "schemas/record.schema.json",
            "lean-toolchain",
            "README.md",
            "docs/pr-classes.md",
        ):
            self.assertFalse(skipped(path), path)

    def test_the_filter_is_an_ignore_list_not_an_allow_list(self):
        # `paths` would run the suite only for the listed files, and a new kind of file would silently never be tested
        self.assertNotIn("paths", ON["pull_request"])

    def test_nothing_the_merge_requires_is_produced_by_this_workflow(self):
        names = set(DOC["jobs"]) | {j.get("name") for j in DOC["jobs"].values() if j.get("name")} | {DOC.get("name")}
        for required in REQUIRED:
            self.assertNotIn(required, names)


if __name__ == "__main__":
    unittest.main()
