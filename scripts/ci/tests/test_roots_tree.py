"""scripts/roots_tree.py: the tree's libraries get their root-namespace names qualified, inside existing lines, once, and nothing else changes."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))
import roots_tree as rt

MODULE = """module

public import Tengoku

public section

open Polynomial

def X : Nat := 1

theorem one_eq : X = 1 := rfl

def Nat.double (n : Nat) : Nat := 2 * n

namespace Helper
def inner : Nat := 3
end Helper
"""
OTHER = "module\n\npublic import Tengoku\n\npublic section\n\ndef Y : Nat := 2\n"
REPORT = "leakscan: 0 global instances\nroots: 3 declarations of the library are in the root namespace (x)\nroot: X\nroot: Helper\nroot: instAddFoo\n"
RECORD = {"name": "X", "statement": "def X : Nat := 1", "module": "Tengoku.Foo.Bar", "library": "foo"}
OTHER_RECORD = {"name": "Y", "statement": "def Y : Nat := 2", "module": "Tengoku.Baz.Qux", "library": "baz"}


def make(tmp: Path) -> tuple[Path, Path]:
    tree, roots = tmp / "tree", tmp / "roots"
    (tree / "Tengoku" / "Foo").mkdir(parents=True)
    (tree / "Tengoku" / "Baz").mkdir(parents=True)
    (tree / "Tengoku" / "Foo" / "Bar.lean").write_text(MODULE, encoding="utf-8")
    (tree / "Tengoku" / "Baz" / "Qux.lean").write_text(OTHER, encoding="utf-8")
    (tree / "Tengoku" / "Foo.lean").write_text("import Tengoku.Foo.Bar\n", encoding="utf-8")
    for lib, rec in (("foo", RECORD), ("baz", OTHER_RECORD)):
        d = tree / "data" / "intake" / lib
        d.mkdir(parents=True)
        (d / "manifest.jsonl").write_text(json.dumps(rec) + "\n", encoding="utf-8")
    roots.mkdir()
    (roots / "Foo.txt").write_text(REPORT, encoding="utf-8")
    return tree, roots


class RootsTree(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.tree, self.roots = make(Path(self._tmp.name))
        self.bar = self.tree / "Tengoku" / "Foo" / "Bar.lean"

    def test_a_root_declaration_is_qualified_and_its_use_still_resolves(self):
        report = rt.apply(self.tree, self.roots)
        text = self.bar.read_text(encoding="utf-8")
        self.assertIn("def Tengoku.Foo.X : Nat := 1", text)
        self.assertIn(
            "namespace Tengoku.Foo end Tengoku.Foo open Tengoku.Foo ", text
        )  # the bare `X` of the theorem now means the library's own
        self.assertIn("theorem one_eq : X = 1", text)
        self.assertEqual(report["Foo"]["qualified"], 1)
        self.assertEqual(report["Foo"]["modules_opened"], 1)

    def test_a_namespace_block_of_a_root_moves_with_its_end(self):
        rt.apply(self.tree, self.roots)
        text = self.bar.read_text(encoding="utf-8")
        self.assertIn("namespace Tengoku.Foo.Helper", text)
        self.assertIn("end Tengoku.Foo.Helper", text)

    def test_a_dotted_extension_of_an_outside_namespace_is_not_a_root(self):
        rt.apply(self.tree, self.roots)
        self.assertIn("def Nat.double", self.bar.read_text(encoding="utf-8"))

    def test_no_line_moves(self):
        before = MODULE.split("\n")
        rt.apply(self.tree, self.roots)
        after = self.bar.read_text(encoding="utf-8").split("\n")
        # the generated note is the only added line, at the end; every other line is in its place
        self.assertEqual(len(after), len(before) + 1)
        self.assertTrue(after[-2].startswith("-- Tengoku: root names of this library moved to Tengoku.Foo"))

    def test_the_manifest_record_follows(self):
        rt.apply(self.tree, self.roots)
        rec = json.loads((self.tree / "data" / "intake" / "foo" / "manifest.jsonl").read_text(encoding="utf-8"))
        self.assertEqual(rec["name"], "Tengoku.Foo.X")
        self.assertEqual(rec["statement"], "def Tengoku.Foo.X : Nat := 1")

    def test_a_record_follows_the_module_pass_not_the_exact_name(self):
        manifest = self.tree / "data" / "intake" / "foo" / "manifest.jsonl"
        recs = [
            RECORD,
            {
                "name": "Helper.inner",
                "statement": "def Helper.inner : Nat := 3",
                "module": "Tengoku.Foo.Bar",
                "library": "foo",
            },  # a member of a root's namespace block
            {
                "name": "instAddFoo",
                "statement": "instance : Add Foo := inferInstance",
                "module": "Tengoku.Foo.Bar",
                "library": "foo",
            },  # a root no text declares
            {"name": "Nat.double", "statement": "def Nat.double (n : Nat) : Nat := 2 * n", "module": "Tengoku.Foo.Bar", "library": "foo"},
        ]
        manifest.write_text("".join(json.dumps(r) + "\n" for r in recs), encoding="utf-8")
        rt.apply(self.tree, self.roots)
        names = [json.loads(ln)["name"] for ln in manifest.read_text(encoding="utf-8").splitlines()]
        self.assertEqual(names, ["Tengoku.Foo.X", "Tengoku.Foo.Helper.inner", "instAddFoo", "Nat.double"])
        statements = [json.loads(ln)["statement"] for ln in manifest.read_text(encoding="utf-8").splitlines()]
        self.assertEqual(statements[1], "def Tengoku.Foo.Helper.inner : Nat := 3")
        self.assertEqual(statements[2], "instance : Add Foo := inferInstance")

    def test_a_name_no_text_declares_is_reported_not_renamed(self):
        report = rt.apply(self.tree, self.roots)
        self.assertIn("instAddFoo", report["Foo"]["unresolved"])

    def test_a_library_without_a_report_is_untouched(self):
        other = self.tree / "Tengoku" / "Baz" / "Qux.lean"
        rt.apply(self.tree, self.roots)
        self.assertEqual(other.read_text(encoding="utf-8"), OTHER)
        rec = json.loads((self.tree / "data" / "intake" / "baz" / "manifest.jsonl").read_text(encoding="utf-8"))
        self.assertEqual(rec["name"], "Y")

    def test_it_is_idempotent(self):
        rt.apply(self.tree, self.roots)
        once = self.bar.read_text(encoding="utf-8")
        rec_once = (self.tree / "data" / "intake" / "foo" / "manifest.jsonl").read_text(encoding="utf-8")
        report = rt.apply(self.tree, self.roots)
        self.assertEqual(self.bar.read_text(encoding="utf-8"), once)
        self.assertEqual((self.tree / "data" / "intake" / "foo" / "manifest.jsonl").read_text(encoding="utf-8"), rec_once)
        self.assertEqual(report["Foo"]["qualified"], 0)

    def test_the_umbrella_is_untouched(self):
        rt.apply(self.tree, self.roots)
        self.assertEqual((self.tree / "Tengoku" / "Foo.lean").read_text(encoding="utf-8"), "import Tengoku.Foo.Bar\n")


if __name__ == "__main__":
    unittest.main()
