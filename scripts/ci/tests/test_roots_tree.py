"""scripts/roots_tree.py: the tree's libraries get their root-namespace names qualified, inside existing lines, once, and nothing else changes."""

import json
import random
import re
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
        self.assertIn("def _root_.Tengoku.Foo.X : Nat := 1", text)
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


OLD_OPEN_LINE = re.compile(
    r"^(?P<pre>\s*(?:@\[[^\]]*\]\s*)?open\s+(?:scoped\s+)?)(?P<args>[^()]*?)(?P<post>\s+(?:hiding|renaming)\b.*|\s+in\s*|\s*\(.*)?\s*$"
)


class OpenLines(unittest.TestCase):
    """open_args is the factory's OPEN_LINE regular expression without its backtracking: the same arguments, at the same column, on every well-formed `open` line"""

    def test_well_formed_lines_agree_with_the_regular_expression(self):
        random.seed(11)
        words = ["Foo", "Bar.baz", "X", "«a b»", "Nat", "Polynomial", "MvPolynomial.C", "x₁", "y'"]
        for _ in range(20000):
            line = (
                random.choice(["", "@[simp] ", "  "])
                + "open "
                + random.choice(["", "scoped "])
                + " ".join(random.choice(words) for _ in range(random.randint(1, 4)))
            )
            line += random.choice(
                [
                    "",
                    " ",
                    " in",
                    " in ",
                    " hiding " + random.choice(words),
                    " renaming " + random.choice(words) + " → " + random.choice(words),
                    " (" + random.choice(words) + ")",
                ]
            )
            m = OLD_OPEN_LINE.match(line)
            old = (m.end("pre"), m.group("args")) if m else None
            self.assertEqual(rt.open_args(line), old, line)

    def test_what_is_not_an_open_line_is_not_one(self):
        for line in ["def X : Nat := 1", "opened Foo", "-- open Foo", "namespace Foo", ""]:
            self.assertIsNone(rt.open_args(line), line)

    def test_an_open_of_a_root_namespace_follows(self):
        with tempfile.TemporaryDirectory() as t:
            tree = Path(t)
            (tree / "Tengoku" / "Foo").mkdir(parents=True)
            (tree / "Tengoku" / "Foo" / "A.lean").write_text(
                "module\n\npublic import Tengoku\n\npublic section\n\nnamespace Helper\ndef inner : Nat := 3\nend Helper\n\nopen scoped Helper Nat\n",
                encoding="utf-8",
            )
            (tree / "roots").mkdir()
            (tree / "roots" / "Foo.txt").write_text("roots: 1 declarations of the library x\nroot: Helper\n", encoding="utf-8")
            rt.apply(tree, tree / "roots")
            self.assertIn("open scoped Tengoku.Foo.Helper Nat", (tree / "Tengoku" / "Foo" / "A.lean").read_text(encoding="utf-8"))


class Mask(unittest.TestCase):
    """mask blanks comments and string literals to spaces (same length, newlines kept), so a word found in it is code: (text, how many `X` are code)"""

    CASES = [
        ("def X := 1 -- X again\ndef Y", 1),
        ('def s := "X \\" X" X', 1),
        ("a /- X /- X -/ X -/ X", 1),
        ("a /- never closed X", 0),
        ('a "never closed X', 0),
        ("/-- doc X\nmore -/ X", 1),
        ("X /- X -/ X -- X\nX", 3),
    ]

    def test_table(self):
        for text, code_x in self.CASES:
            masked = rt.mask(text)
            self.assertEqual(masked.count("X"), code_x, text)
            self.assertEqual(len(masked), len(text), text)
            self.assertEqual([i for i, ch in enumerate(text) if ch == "\n"], [i for i, ch in enumerate(masked) if ch == "\n"], text)


class ExplicitRoot(unittest.TestCase):
    """`_root_.R…` spells a name from the root: it does not move with a namespace block, so the prefix follows (found by the merge queue on Hironaka: `def _root_.AnalyticManifold.transportChartedSpace`)"""

    def run_text(self, text, roots):
        files = {"Tengoku/Foo/A.lean": text}
        report = f"roots: {len(roots)} declarations\n" + "".join(f"root: {r}\n" for r in roots)
        changed, rep = rt.qualify_files(files, {"Foo": report})
        return changed.get("Tengoku/Foo/A.lean", text), rep

    def test_a_declaration_spelled_from_the_root_follows_its_structure(self):
        text = "module\n\npublic section\n\nstructure Mfd where\n  x : Nat\n\ndef _root_.Mfd.transport (M : Mfd) : Nat := M.x\n"
        out, rep = self.run_text(text, ["Mfd"])
        self.assertIn("structure _root_.Tengoku.Foo.Mfd where", out)
        self.assertIn("def _root_.Tengoku.Foo.Mfd.transport", out)
        self.assertEqual(rep["Foo"]["renamed"], ["Mfd"])

    def test_a_use_spelled_from_the_root_follows_too(self):
        text = "module\n\npublic section\n\ndef X : Nat := 1\n\ntheorem t : _root_.X = 1 := rfl\n"
        out, _ = self.run_text(text, ["X"])
        self.assertIn("theorem t : _root_.Tengoku.Foo.X = 1", out)

    def test_a_root_that_no_declaration_renamed_keeps_its_prefix(self):
        # instAddFoo is in the report (an anonymous instance) but nothing declares it: `_root_.instAddFoo` must keep naming it, and its manifest record must not move
        text = "module\n\npublic section\n\ndef X : Nat := 1\n\ntheorem t : _root_.instAddFoo = _root_.X := rfl\n"
        out, rep = self.run_text(text, ["X", "instAddFoo"])
        self.assertIn("_root_.instAddFoo = _root_.Tengoku.Foo.X", out)
        self.assertEqual(rep["Foo"]["renamed"], ["X"])

    def test_a_single_component_declaration_from_the_root_counts_as_declared(self):
        text = "module\n\npublic section\n\nnamespace Bar\ndef _root_.X : Nat := 1\nend Bar\n"
        out, rep = self.run_text(text, ["X"])
        self.assertIn("def _root_.Tengoku.Foo.X :", out)
        self.assertEqual(rep["Foo"]["unresolved"], [])

    def test_a_use_on_a_declaration_line_is_not_counted_as_a_declaration(self):
        text = "module\n\npublic section\n\nstructure Mfd where\n  x : Nat\n\ntheorem t : _root_.Mfd.foo = _root_.Mfd.foo := rfl\n"
        _, rep = self.run_text(text, ["Mfd"])
        self.assertEqual(rep["Foo"]["dotted"], 0)

    def test_the_roots_are_renamed_in_a_later_module_than_the_use(self):
        files = {
            "Tengoku/Foo/A.lean": "module\n\npublic section\n\ntheorem t : _root_.X = 1 := rfl\n",
            "Tengoku/Foo/B.lean": "module\n\npublic section\n\ndef X : Nat := 1\n",
        }
        changed, _ = rt.qualify_files(files, {"Foo": "roots: 1 declarations\nroot: X\n"})
        self.assertIn("_root_.Tengoku.Foo.X = 1", changed["Tengoku/Foo/A.lean"])

    def test_other_root_names_and_comments_are_left_alone(self):
        text = "module\n\npublic section\n\ndef X : Nat := 1\n\n-- uses _root_.Valuation and _root_.X in a comment\ntheorem t : _root_.Valuation = _root_.Valuation := rfl\n"
        out, _ = self.run_text(text, ["X"])
        self.assertIn("-- uses _root_.Valuation and _root_.X in a comment", out)
        self.assertIn("_root_.Valuation = _root_.Valuation", out)

    def test_it_is_idempotent(self):
        text = "module\n\npublic section\n\nstructure Mfd where\n  x : Nat\n\ndef _root_.Mfd.transport (M : Mfd) : Nat := M.x\n"
        once, _ = self.run_text(text, ["Mfd"])
        twice, _ = self.run_text(once, ["Mfd"])
        self.assertEqual(once, twice)


class DocComment(unittest.TestCase):
    """The inserted commands must not stand between a doc comment and its declaration (found by the merge queue on PadicLFunctions: `unexpected token 'namespace'; expected 'lemma'`)"""

    TEXT = "module\n\nimport Tengoku\n\n/-! module doc -/\n\n/-- the zeta value. -/\ndef zeta (k : Nat) : Nat := k\n\ntheorem zeta_zero : zeta 0 = 0 := rfl\n"

    def run_text(self, text):
        changed, _ = rt.qualify_files({"Tengoku/Foo/A.lean": text}, {"Foo": "roots: 1 declarations\nroot: zeta\n"})
        return changed.get("Tengoku/Foo/A.lean", text)

    def test_the_prelude_goes_in_front_of_the_doc_comment(self):
        out = self.run_text(self.TEXT)
        self.assertIn("namespace Tengoku.Foo end Tengoku.Foo open Tengoku.Foo /-- the zeta value. -/\ndef _root_.Tengoku.Foo.zeta", out)

    def test_a_module_doc_and_a_plain_comment_stay_header(self):
        out = self.run_text(self.TEXT.replace("/-- the zeta", "/- the zeta"))
        self.assertIn("/- the zeta value. -/\nnamespace Tengoku.Foo end Tengoku.Foo open Tengoku.Foo def _root_.Tengoku.Foo.zeta", out)

    def test_no_line_moves_and_it_is_idempotent(self):
        once = self.run_text(self.TEXT)
        self.assertEqual(
            len(once.split("\n")), len(self.TEXT.split("\n")) + 1
        )  # the one footer line the pass appends; none of the module's own lines moves
        self.assertEqual(once, self.run_text(once))


class BodyNamespace(unittest.TestCase):
    """`def NS.x` makes NS the namespace of its body: a bare `integral_add` there means `NS.integral_add` ONLY, no longer competing with an opened `MeasureTheory.integral_add` (the overload the root declaration took part in). The merge queue found it on LeanPool/OSforGFF/OS/OS3MixedRepInfra.lean (`integral_const_mul`); Leak IV reproduced it (`theorem Tq.useA` fails, `theorem _root_.Tq.useB` passes). A plain root declaration therefore keeps its body where it was, with `_root_.`."""

    TEXT = "module\n\npublic section\n\nopen MeasureTheory\n\ntheorem integral_add (n m : Nat) : n + m = m + n := Nat.add_comm n m\n\ntheorem use_it (n : Nat) : n + 0 = 0 + n := integral_add n 0\n"

    def run_text(self, text, roots=("integral_add",)):
        report = f"roots: {len(roots)} declarations\n" + "".join(f"root: {r}\n" for r in roots)
        changed, _ = rt.qualify_files({"Tengoku/Foo/A.lean": text}, {"Foo": report})
        return changed.get("Tengoku/Foo/A.lean", text)

    def test_a_plain_root_declaration_keeps_the_body_namespace(self):
        out = self.run_text(self.TEXT)
        self.assertIn("theorem _root_.Tengoku.Foo.integral_add (n m : Nat)", out)
        self.assertNotIn("theorem Tengoku.Foo.integral_add", out)

    def test_a_dotted_declaration_keeps_the_plain_form(self):
        text = "module\n\npublic section\n\nstructure Mfd where\n  x : Nat\n\ndef Mfd.double (M : Mfd) : Nat := 2 * M.x\n"
        out = self.run_text(text, ("Mfd",))
        self.assertIn("structure _root_.Tengoku.Foo.Mfd where", out)
        self.assertIn("def Tengoku.Foo.Mfd.double (M", out)  # its siblings are named from namespace Mfd: not `_root_`
        self.assertNotIn("_root_.Tengoku.Foo.Mfd.double", out)

    def test_a_manifest_statement_is_the_declaration_alone(self):
        text = (
            json.dumps({"name": "integral_add", "statement": "theorem integral_add (n m : Nat) : n = n := rfl", "module": "Tengoku.Foo.A"})
            + "\n"
        )
        out, n = rt.qualify_manifest_text(text, {"integral_add"}, "Tengoku.Foo")
        rec = json.loads(out)
        self.assertEqual(n, 1)
        self.assertEqual(rec["name"], "Tengoku.Foo.integral_add")
        self.assertTrue(rec["statement"].startswith("theorem Tengoku.Foo.integral_add"))
        self.assertNotIn("_root_", rec["statement"])

    def test_it_is_idempotent(self):
        once = self.run_text(self.TEXT)
        self.assertEqual(once, self.run_text(once))


if __name__ == "__main__":
    unittest.main()
