"""cmdkw_check.py: the command keywords Lean reports against the list the content lint reads. A stale list would read a keyword the seed added as a continuation."""

from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import cmdkw_check as ck  # noqa: E402

REAL = json.loads((HERE.parent.parent.parent / "schemas" / "command-keywords.json").read_text(encoding="utf-8"))["commands"]


def run(stdin: str, *argv: str):
    out = io.StringIO()
    with mock.patch.object(sys, "stdin", io.StringIO(stdin)), redirect_stdout(out):
        rc = ck.main(list(argv))
    return rc, out.getvalue()


class Compare(unittest.TestCase):
    def test_new_and_gone_words(self):
        self.assertEqual(ck.compare({"a", "b", "c"}, {"b", "c", "d"}), (["a"], ["d"]))
        self.assertEqual(ck.compare({"a"}, {"a"}), ([], []))


class Main(unittest.TestCase):
    def listfile(self, words):
        d = Path(tempfile.mkdtemp())
        p = d / "list.json"
        p.write_text(json.dumps({"about": "x", "commands": words}), encoding="utf-8")
        return p

    def test_the_real_list_is_what_it_says_and_equals_itself(self):
        self.assertEqual(sorted(REAL), REAL)
        self.assertEqual(len(set(REAL)), len(REAL))
        rc, out = run("\n".join(REAL), str(self.listfile(REAL)))
        self.assertEqual(rc, 0, out)

    def test_a_keyword_the_list_lacks_fails_and_says_how_to_regenerate(self):
        rc, out = run("\n".join([*REAL, "frobnicate_cmd"]), str(self.listfile(REAL)))
        self.assertEqual(rc, 1)
        self.assertIn("frobnicate_cmd", out)
        self.assertIn("--write", out)

    def test_a_keyword_that_went_fails_too(self):
        rc, out = run("\n".join(REAL[1:]), str(self.listfile(REAL)))
        self.assertEqual(rc, 1)
        self.assertIn(REAL[0], out)

    def test_almost_nothing_from_lean_is_a_failure_of_the_program_not_a_list(self):
        rc, out = run("theorem\ndef\n", str(self.listfile(REAL)))
        self.assertEqual(rc, 2)
        self.assertIn("not the tree's command grammar", out)

    def test_write_regenerates_the_list_sorted(self):
        p = self.listfile(["old"])
        rc, out = run("\n".join(reversed([*REAL, "zzz_new"])), "--write", str(p))
        self.assertEqual(rc, 0, out)
        doc = json.loads(p.read_text(encoding="utf-8"))
        self.assertEqual(doc["commands"], sorted([*REAL, "zzz_new"]))
        self.assertEqual(doc["about"], "x")  # the rest of the file is kept


class CiJob(unittest.TestCase):
    """The pr-tests job `command-keywords` runs only when a file it depends on changes: the list must cover them, the workflow file included."""

    def trigger(self):
        import re

        text = (HERE.parent.parent.parent / ".github" / "workflows" / "pr-tests.yml").read_text(encoding="utf-8")
        job = re.search(r"^  command-keywords:\n(.*?)(?=^  \S|\Z)", text, re.S | re.M)
        self.assertIsNotNone(job, "the command-keywords job was not found")
        m = re.search(r"grep -qE '(\^\(.*?\))' <<< \"\$files\"", job.group(1))
        self.assertIsNotNone(m, "the touched step of the command-keywords job was not found")
        return re.compile(m.group(1))

    def test_every_file_the_job_depends_on_triggers_it(self):
        rx = self.trigger()
        for path in (
            "tools/CommandKeywords.lean",
            "schemas/command-keywords.json",
            "scripts/ci/cmdkw_check.py",
            "scripts/ci/allowlist.py",
            "lean-toolchain",
            ".github/workflows/pr-tests.yml",
        ):
            self.assertRegex(path, rx, path)

    def test_unrelated_files_do_not_trigger_it(self):
        rx = self.trigger()
        for path in ("scripts/seed.py", "Tengoku/Seed/Logic/Basic.lean", "docs/testing.md", "TengokuIsnad.lean"):
            self.assertNotRegex(path, rx, path)


if __name__ == "__main__":
    unittest.main()
