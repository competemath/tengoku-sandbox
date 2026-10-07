"""A repository analyses into its own SonarQube Cloud project (organisation_repository). The sandbox is a copy of tengoku, and a sync that
copies sonar-project.properties from tengoku carries tengoku's key with it: every analysis of the sandbox then lands in tengoku's project
and replaces what its main branch shows (2026-10-04 to 2026-10-07: nine sandbox analyses, none of tengoku's own survived the housekeeping).
The expected key comes from the checkout's own remote (not from GITHUB_REPOSITORY: another test module sets that to `o/r` for the whole
process), so the same file is right in both repositories."""

from __future__ import annotations

import re
import subprocess
import unittest
import unittest.mock
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PROPS = ROOT / "sonar-project.properties"


def project_key(text: str) -> str | None:
    found = re.findall(r"^sonar\.projectKey=(\S+)\s*$", text, re.M)
    return found[0] if len(found) == 1 else None


def own_repository() -> str | None:
    """owner/name of the checkout's origin, or None when there is no remote."""
    r = subprocess.run(["git", "-C", str(ROOT), "remote", "get-url", "origin"], capture_output=True, text=True)
    m = re.search(r"github\.com[:/]([^/]+)/([^/]+?)(?:\.git)?/?$", r.stdout.strip()) if r.returncode == 0 else None
    return f"{m.group(1)}/{m.group(2)}" if m else None


class SonarKey(unittest.TestCase):
    def test_the_key_is_read_from_exactly_one_uncommented_line(self):
        self.assertEqual(project_key("# sonar.projectKey=old\nsonar.projectKey=org_repo\n"), "org_repo")
        self.assertIsNone(project_key("sonar.projectKey=a\nsonar.projectKey=b\n"))
        self.assertIsNone(project_key("# sonar.projectKey=a\n"))

    def test_the_remote_is_read_as_owner_and_name(self):
        for url in ("https://github.com/o/r", "https://github.com/o/r.git", "git@github.com:o/r.git", "https://x@github.com/o/r/"):
            with self.subTest(url=url):
                with unittest.mock.patch.object(subprocess, "run", return_value=subprocess.CompletedProcess([], 0, url + "\n", "")):
                    self.assertEqual(own_repository(), "o/r")

    def test_the_project_is_this_repositorys_own(self):
        repo = own_repository()
        if repo is None:
            self.skipTest("no origin remote")
        self.assertEqual(project_key(PROPS.read_text(encoding="utf-8")), repo.replace("/", "_"))


if __name__ == "__main__":
    unittest.main()
