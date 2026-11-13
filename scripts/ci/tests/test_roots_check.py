"""The `roots` class (scripts/ci/roots_check.py): a PR is exactly what the base's scripts/roots_tree.py computes from the reports it adds, or it is refused."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from test_gates import TREE, Repo  # noqa: E402

MODULE = "module\n\npublic import Tengoku\n\npublic section\n\nopen Polynomial\n\ndef X : Nat := 1\n\ntheorem one_eq : X = 1 := rfl\n"
REPORT = "leakscan: 0 global instances\nroots: 1 declarations of the library are in the root namespace (x)\nroot: X\n"
RECORD = {"name": "X", "statement": "def X : Nat := 1", "module": "Tengoku.Foo.Bar", "library": "foo", "source_url": "https://x/y"}


class RootsPR(Repo):
    """a base with the script, one library with a root declaration, its manifest, and another library; a branch `pr` ready for the PR's commit"""

    def __init__(self):
        super().__init__()
        self.git("checkout", "-q", "main")
        shutil.copy(TREE / "scripts" / "roots_tree.py", self.dir / "scripts" / "roots_tree.py")
        self.write("Tengoku/Foo/Bar.lean", MODULE)
        self.write("Tengoku/Foo.lean", "import Tengoku.Foo.Bar\n")
        self.write("data/intake/foo/manifest.jsonl", json.dumps(RECORD) + "\n")
        self.commit("base with a root declaration")
        self.git("checkout", "-q", "pr")
        self.git("reset", "-q", "--hard", "main")

    def add_report(self, lib="Foo", text=REPORT, rid="r1"):
        self.write(f"data/roots/{rid}/{lib}.txt", text)

    def apply(self, rid="r1"):
        subprocess.run(
            [sys.executable, "scripts/roots_tree.py", "apply"],
            cwd=self.dir,
            check=True,
            capture_output=True,
        )


class RootsCheck(unittest.TestCase):
    def good(self):
        r = RootsPR()
        r.add_report()
        r.apply()
        r.commit("roots")
        return r

    def test_the_scripts_own_output_passes(self):
        r = self.good()
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("roots ok", out)

    def test_one_more_edit_in_a_module_is_refused(self):
        r = self.good()
        r.append("Tengoku/Foo/Bar.lean", "theorem sneaky : 1 = 1 := rfl\n")
        r.commit("sneak")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1)
        self.assertIn("differs from the script's output", out)

    def test_the_manifest_must_follow(self):
        r = RootsPR()
        r.add_report()
        r.apply()
        r.write("data/intake/foo/manifest.jsonl", json.dumps(RECORD) + "\n")  # the record left as it was
        r.commit("roots, manifest not updated")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1)
        self.assertIn("manifest.jsonl", out)

    def test_a_file_outside_the_libraries_is_refused(self):
        r = self.good()
        r.append("scripts/x.py", "print(2)\n")
        r.commit("also a script")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1)
        self.assertIn("nothing else", out)

    def test_a_report_for_a_library_the_base_lacks_is_refused(self):
        r = RootsPR()
        r.add_report(lib="Nope")
        r.commit("a report only")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1)
        self.assertIn("no such library", out)

    def test_a_pr_without_a_report_is_not_a_roots_pr(self):
        r = RootsPR()
        r.append("Tengoku/Foo/Bar.lean", "-- a comment\n")
        r.commit("hand edit")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1)
        self.assertIn("not a roots PR", out)

    def test_a_report_that_names_something_the_script_would_not_rename_changes_nothing_else(self):
        r = RootsPR()
        r.add_report(
            text="roots: 1 declarations of the library x\nroot: one_eq\n"
        )  # a theorem declared in a section: renaming it is the script's rule, and the PR must match it
        r.apply()
        r.commit("roots")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 0, out)

    def test_two_ids_in_one_pr_are_refused(self):
        r = RootsPR()
        r.add_report(rid="a")
        r.add_report(lib="Foo", rid="b")
        r.commit("two ids")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1)

    def test_the_classifier_names_the_class_whoever_sends_it(self):
        r = self.good()
        rc, out = r.gate("classify.py", env={"PR_ACTOR": "someone-else"})
        self.assertEqual(rc, 0, out)
        self.assertIn("class=roots", out)

    def test_the_other_gates_that_read_a_diff_accept_it(self):
        r = self.good()
        for script in ("append_only.py", "validate_records.py", "lint_banked.py", "dco.py"):
            rc, out = r.gate(script)
            self.assertEqual(rc, 0, f"{script}: {out}")

    def test_the_credits_gate_takes_a_rename_with_the_flag_and_only_with_it(self):
        r = self.good()
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 1, out)  # the record's source_url line changed: without the class flag that is a changed credit
        self.assertIn("manifest.jsonl", out)
        rc, out = r.gate("credits.py", "main", "pr", "--roots")
        self.assertEqual(rc, 0, out)

    def test_the_credits_flag_does_not_excuse_a_changed_source(self):
        r = RootsPR()
        r.add_report()
        r.apply()
        manifest = r.dir / "data" / "intake" / "foo" / "manifest.jsonl"
        rec = json.loads(manifest.read_text(encoding="utf-8"))
        rec["source_url"] = "https://elsewhere/z"
        manifest.write_text(json.dumps(rec) + "\n", encoding="utf-8")
        r.commit("roots, but the source changed")
        rc, out = r.gate("credits.py", "main", "pr", "--roots")
        self.assertEqual(rc, 1, out)

    def test_a_mode_change_alone_is_refused(self):
        r = self.good()
        (r.dir / "Tengoku" / "Foo" / "Bar.lean").chmod(0o755)  # the script's own content, one module made executable
        r.commit("mode")
        rc, out = r.gate("roots_check.py")
        self.assertEqual(rc, 1, out)
        self.assertIn("its mode changed", out)


if __name__ == "__main__":
    unittest.main()
