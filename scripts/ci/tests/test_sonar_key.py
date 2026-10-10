"""A repository analyses into its own SonarQube Cloud project (organisation_repository). The sandbox is a copy of tengoku, and a sync that
copies sonar-project.properties from tengoku carries tengoku's key with it: every analysis of the sandbox then lands in tengoku's project
and replaces what its main branch shows (2026-10-04 to 2026-10-07: nine sandbox analyses, none of tengoku's own survived the housekeeping).
The expected key comes from the repository the tests run in, so the same file is right in both. That repository is read from the event file GitHub
writes (GITHUB_EVENT_PATH), not from GITHUB_REPOSITORY: test_gate_summary_data sets GITHUB_REPOSITORY to `o/r` when it is imported, and a discover run
imports every module before it runs one, so this test saw `o/r` (2026-10-09: every sandbox scan failed on 'competemath_tengoku-sandbox' != 'o_r')."""

from __future__ import annotations

import json
import os
import re
import unittest
from pathlib import Path

PROPS = Path(__file__).resolve().parents[3] / "sonar-project.properties"


def running_repository(env: dict[str, str]) -> str | None:
    """`owner/name` of the repository the tests run in: the event file's, else GITHUB_REPOSITORY (nothing else in the process may have rewritten the event file)."""
    event = env.get("GITHUB_EVENT_PATH")
    if event and Path(event).is_file():
        try:
            return json.loads(Path(event).read_text(encoding="utf-8"))["repository"]["full_name"]
        except (ValueError, KeyError, TypeError):
            pass
    return env.get("GITHUB_REPOSITORY") or None


def project_key(text: str) -> str | None:
    found = re.findall(r"^sonar\.projectKey=(\S+)\s*$", text, re.M)
    return found[0] if len(found) == 1 else None


class SonarKey(unittest.TestCase):
    def test_the_key_is_read_from_exactly_one_uncommented_line(self):
        self.assertEqual(project_key("# sonar.projectKey=old\nsonar.projectKey=org_repo\n"), "org_repo")
        self.assertIsNone(project_key("sonar.projectKey=a\nsonar.projectKey=b\n"))
        self.assertIsNone(project_key("# sonar.projectKey=a\n"))

    def test_the_repository_is_the_event_files_not_a_variable_another_test_may_have_set(self):
        import tempfile

        with tempfile.TemporaryDirectory() as d:
            event = Path(d) / "event.json"
            event.write_text(json.dumps({"repository": {"full_name": "competemath/tengoku-sandbox"}}), encoding="utf-8")
            self.assertEqual(
                running_repository({"GITHUB_EVENT_PATH": str(event), "GITHUB_REPOSITORY": "o/r"}), "competemath/tengoku-sandbox"
            )
            event.write_text("not json", encoding="utf-8")
            self.assertEqual(running_repository({"GITHUB_EVENT_PATH": str(event), "GITHUB_REPOSITORY": "a/b"}), "a/b")
        self.assertEqual(running_repository({"GITHUB_REPOSITORY": "a/b"}), "a/b")
        self.assertIsNone(running_repository({}))

    @unittest.skipUnless(running_repository(dict(os.environ)), "needs the repository name (set by GitHub Actions)")
    def test_the_project_is_this_repositorys_own(self):
        repo = running_repository(dict(os.environ))
        self.assertEqual(project_key(PROPS.read_text(encoding="utf-8")), repo.replace("/", "_"))


if __name__ == "__main__":
    unittest.main()
