"""The unit tests run once per PR, under coverage, and SonarQube Cloud analyses that report in the same run (pr-tests.yml); sonar.yml scans
the main branch only. Before (2026-10-07) the suite ran plain in pr-tests and again under coverage in sonar.yml: five runner-minutes per PR."""

from __future__ import annotations

import unittest
from pathlib import Path

import yaml

WF = Path(__file__).resolve().parents[3] / ".github" / "workflows"
PR_TESTS = yaml.safe_load((WF / "pr-tests.yml").read_text(encoding="utf-8"))
SONAR = yaml.safe_load((WF / "sonar.yml").read_text(encoding="utf-8"))


def runs(job: dict) -> str:
    return "\n".join(s["run"] for s in job["steps"] if "run" in s)


def uses(job: dict) -> list[str]:
    return [s["uses"].split("@")[0] for s in job["steps"] if "uses" in s]


class OneTestRun(unittest.TestCase):
    def test_the_suite_runs_under_coverage_once_and_the_report_is_an_artifact(self):
        tests = runs(PR_TESTS["jobs"]["tooling-tests"])
        self.assertEqual(tests.count("coverage run -m unittest discover"), 2)  # scripts/tests and scripts/ci/tests
        self.assertNotIn("python3 -m unittest discover", tests)  # not a plain run as well
        self.assertIn("coverage xml", tests)
        up = [s for s in PR_TESTS["jobs"]["tooling-tests"]["steps"] if s.get("uses", "").startswith("actions/upload-artifact@")]
        self.assertEqual((up[0]["with"]["name"], up[0]["with"]["path"]), ("coverage", "coverage.xml"))

    def test_the_sonar_job_waits_for_the_tests_and_analyses_their_report(self):
        job = PR_TESTS["jobs"]["sonar"]
        self.assertEqual(job["needs"], "tooling-tests")
        self.assertIn("github.event.pull_request.head.repo.full_name == github.repository", job["if"])  # a fork's PR has no token
        down = [s for s in job["steps"] if s.get("uses", "").startswith("actions/download-artifact@")]
        self.assertEqual(down[0]["with"]["name"], "coverage")
        self.assertIn("SonarSource/sonarqube-scan-action", uses(job))
        self.assertNotIn("unittest", runs(job))  # the tests are not run again here
        self.assertEqual(job["permissions"], {"contents": "read", "pull-requests": "read"})

    def test_sonar_yml_no_longer_scans_pull_requests(self):
        self.assertNotIn("pull_request", SONAR[True] if True in SONAR else SONAR["on"])  # `on` parses as True in YAML 1.1

    def test_lint_python_caches_pre_commits_environments(self):
        job = PR_TESTS["jobs"]["lint-python"]
        cache = [s for s in job["steps"] if s.get("uses", "").startswith("actions/cache@")]
        self.assertEqual(cache[0]["with"]["path"], "~/.cache/pre-commit")
        self.assertIn("hashFiles('.pre-commit-config.yaml')", cache[0]["with"]["key"])


if __name__ == "__main__":
    unittest.main()
