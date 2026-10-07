"""A repository analyses into its own SonarQube Cloud project (organisation_repository). The sandbox is a copy of tengoku, and a sync that
copies sonar-project.properties from tengoku carries tengoku's key with it: every analysis of the sandbox then lands in tengoku's project
and replaces what its main branch shows (2026-10-04 to 2026-10-07: nine sandbox analyses, none of tengoku's own survived the housekeeping).
The expected key comes from the repository the tests run in, so the same file is right in both."""

from __future__ import annotations

import os
import re
import unittest
from pathlib import Path

PROPS = Path(__file__).resolve().parents[3] / "sonar-project.properties"


def project_key(text: str) -> str | None:
    found = re.findall(r"^sonar\.projectKey=(\S+)\s*$", text, re.M)
    return found[0] if len(found) == 1 else None


class SonarKey(unittest.TestCase):
    def test_the_key_is_read_from_exactly_one_uncommented_line(self):
        self.assertEqual(project_key("# sonar.projectKey=old\nsonar.projectKey=org_repo\n"), "org_repo")
        self.assertIsNone(project_key("sonar.projectKey=a\nsonar.projectKey=b\n"))
        self.assertIsNone(project_key("# sonar.projectKey=a\n"))

    @unittest.skipUnless(os.environ.get("GITHUB_REPOSITORY"), "needs the repository name (set by GitHub Actions)")
    def test_the_project_is_this_repositorys_own(self):
        repo = os.environ["GITHUB_REPOSITORY"]
        self.assertEqual(project_key(PROPS.read_text(encoding="utf-8")), repo.replace("/", "_"))


if __name__ == "__main__":
    unittest.main()
