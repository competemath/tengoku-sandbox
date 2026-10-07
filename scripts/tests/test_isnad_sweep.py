"""scripts/isnad_sweep.py: which modules the next tag PR takes (the plan of the sweep). Its own file, so tests of other tools do not conflict with it."""

from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import isnad_sweep as sw  # noqa: E402

THM = "import Tengoku\n\ntheorem t : 1 + 1 = 2 := rfl\n"
TAG = "@isnad1 id=eq.0h2v.s4.05598c1b76c4 from=seed src=0 shape=900bc7c0 vocab=fc0e7020"
TAGGED = f"import Tengoku\n\n/-- One plus one.\n{TAG}\n-/\ntheorem t : 1 + 1 = 2 := rfl\n"


def tree(files: dict[str, str], intake=("fx-lib",)) -> Path:
    root = Path(tempfile.mkdtemp())
    for lib in intake:
        (root / "data" / "intake" / lib).mkdir(parents=True)
        (root / "data" / "intake" / lib / "manifest.jsonl").write_text("{}\n")
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    return root


class Selection(unittest.TestCase):
    def test_scopes(self):
        self.assertEqual(sw.scope_of("Tengoku/Seed/A/B.lean", {"FxLib"}), "seed")
        self.assertEqual(sw.scope_of("Tengoku/Native/A.lean", {"FxLib"}), "native")
        self.assertEqual(sw.scope_of("Tengoku/FxLib/A.lean", {"FxLib"}), "libs")
        self.assertIsNone(sw.scope_of("Tengoku/Other/A.lean", {"FxLib"}))  # a library generated from records, or none
        self.assertIsNone(sw.scope_of("Tengoku/Seed.lean", {"FxLib"}))  # a root file
        self.assertIsNone(sw.scope_of("Tengoku/All.lean", {"FxLib"}))

    def test_the_scope_is_the_one_tag_check_judges(self):
        sys.path.insert(0, str(HERE.parent / "ci"))
        import tag_check

        for rel in (
            "Tengoku/Seed/A.lean",
            "Tengoku/Native/A.lean",
            "Tengoku/FxLib/A.lean",
            "Tengoku/Other/A.lean",
            "Tengoku/Seed.lean",
            "Tengoku/All.lean",
        ):
            self.assertEqual(sw.scope_of(rel, {"FxLib"}) is not None, tag_check.in_scope(rel, {"FxLib"}), rel)

    def test_a_theorem_in_code_counts_and_one_in_prose_does_not(self):
        for text in (
            THM,
            "@[simp] lemma a : True := trivial\n",
            "protected theorem Nat.x : True := trivial\n",
            "  theorem indented : True := trivial\n",
            "@[simp]\ntheorem own_line : True := trivial\n",
            "@[simp, norm_cast] @[inline] private lemma two_attrs : True := trivial\n",
            "noncomputable protected theorem Nat.x : True := trivial\n",
        ):
            self.assertTrue(sw.has_theorem(text), text)
        for text in (
            "/-- theorem about stuff -/\ndef x := 1\n",
            "-- theorem nope\ndef x := 1\n",
            'def s := "theorem inside"\n',
            "/- lemma\n x -/\n",
            "def x := 1\n",
            "/-\ntheorem prose : True\n-/\ndef y := 1\n",  # a line of an ordinary comment
            "/-- Doc.\ntheorem in a docstring : True\n-/\ndef y := 1\n",
            'def s := "\ntheorem in a string : True\n"\n',
        ):
            self.assertFalse(sw.has_theorem(text), text)

    def test_what_is_not_a_theorem_command(self):
        for text in (
            "theorem\n",
            "theorem",
            "@[simp def x := 1\n",
            "def theorem_x := 1\n",
            "@[simp] def x := 1\n",
            "private def lemma_x := 1\n",
            "mytheorem x : True\n",
        ):
            self.assertFalse(sw.has_theorem(text), text)

    def test_a_crafted_line_does_not_make_it_slow(self):
        """CodeQL: the old attribute pattern backtracked exponentially on '@[]' followed by many '\t@[]'"""
        import time

        t0 = time.time()
        self.assertFalse(sw.has_theorem("@[]" + "\t@[]" * 5000 + "\n"))
        self.assertTrue(sw.has_theorem("@[]" + "\t@[]" * 5000 + " theorem t : True := trivial\n"))
        self.assertLess(time.time() - t0, 2.0)

    def test_a_tag_anywhere_in_a_docstring_marks_the_module_done(self):
        self.assertTrue(sw.is_tagged(TAGGED))
        self.assertFalse(sw.is_tagged(THM))
        self.assertFalse(sw.is_tagged(f"-- {TAG}\n" + THM))  # a comment is not a tag
        self.assertFalse(sw.is_tagged(f"/-\n{TAG}\n-/\n" + THM))  # nor is a line of an ordinary block comment
        self.assertFalse(sw.is_tagged(f'def s := "\n{TAG}\n"\n' + THM))  # nor a string

    def test_only_untagged_modules_with_a_theorem_in_scope_are_to_do(self):
        root = tree(
            {
                "Tengoku/Seed/A.lean": THM,
                "Tengoku/Seed/Done.lean": TAGGED,
                "Tengoku/Seed/NoThm.lean": "def x := 1\n",
                "Tengoku/Seed.lean": THM,
                "Tengoku/FxLib/L.lean": THM,
                "Tengoku/Native/N.lean": THM,
                "Tengoku/Other/O.lean": THM,
                "Tengoku/All.lean": "import Tengoku.Seed\n",
            }
        )
        self.assertEqual(sw.todo(root), ["Tengoku.FxLib.L", "Tengoku.Native.N", "Tengoku.Seed.A"])
        self.assertEqual(sw.todo(root, "seed"), ["Tengoku.Seed.A"])
        self.assertEqual(sw.todo(root, "native"), ["Tengoku.Native.N"])
        self.assertEqual(sw.todo(root, "libs"), ["Tengoku.FxLib.L"])

    def test_a_library_that_is_not_an_intake_bundle_is_left_out(self):
        root = tree({"Tengoku/FxLib/L.lean": THM}, intake=())
        self.assertEqual(sw.todo(root), [])


class Order(unittest.TestCase):
    def test_dependents_come_before_what_they_import(self):
        order = sw.dependents_first({"A": {"B"}, "B": {"C"}, "C": set(), "D": {"C"}})
        for m, deps in {"A": {"B"}, "B": {"C"}, "D": {"C"}}.items():
            for d in deps:
                self.assertLess(order.index(m), order.index(d), (m, d, order))
        self.assertEqual(sorted(order), ["A", "B", "C", "D"])

    def test_the_order_is_the_same_every_time_and_ties_go_by_name(self):
        imports = {"Z": set(), "A": set(), "M": {"Z"}, "B": {"A"}}
        self.assertEqual(sw.dependents_first(imports), sw.dependents_first(dict(reversed(list(imports.items())))))
        self.assertEqual(sw.dependents_first({"B": set(), "A": set()}), ["A", "B"])

    def test_a_cycle_is_not_lost(self):
        self.assertEqual(sorted(sw.dependents_first({"A": {"B"}, "B": {"A"}, "C": set()})), ["A", "B", "C"])

    def test_the_plan_follows_the_imports_of_the_files(self):
        root = tree(
            {
                "Tengoku/Seed/Low.lean": THM,
                "Tengoku/Seed/Mid.lean": "import Tengoku.Seed.Low\n" + THM,
                "Tengoku/Seed/High.lean": "public import Tengoku.Seed.Mid\n" + THM,
                "Tengoku/Seed/Aaa.lean": THM,
            }
        )
        got = sw.todo(root)
        self.assertEqual(got, ["Tengoku.Seed.Aaa", "Tengoku.Seed.High", "Tengoku.Seed.Mid", "Tengoku.Seed.Low"])


class Plan(unittest.TestCase):
    def files(self, n=5):
        return {f"Tengoku/Seed/M{i:02d}.lean": THM for i in range(n)}

    def test_max_and_prefix(self):
        root = tree({**self.files(5), "Tengoku/Seed/Other/X.lean": THM})
        self.assertEqual(sw.plan(root, "seed", "", 2), ["Tengoku.Seed.M00", "Tengoku.Seed.M01"])
        self.assertEqual(sw.plan(root, "seed", "Tengoku.Seed.Other", 400), ["Tengoku.Seed.Other.X"])

    def test_a_part_is_never_more_than_400(self):
        root = tree({f"Tengoku/Seed/M{i:03d}.lean": THM for i in range(450)})
        self.assertEqual(len(sw.plan(root, "seed", "", 10_000)), 400)
        self.assertEqual(len(sw.plan(root, "seed", "", 400)), 400)
        self.assertEqual(len(sw.plan(root, "seed", "", 399)), 399)

    def test_tagging_a_part_moves_the_plan_on(self):
        root = tree(self.files(3))
        first = sw.plan(root, "seed", "", 1)
        (root / "Tengoku" / "Seed" / f"{first[0].rsplit('.', 1)[1]}.lean").write_text(TAGGED)
        self.assertEqual(sw.plan(root, "seed", "", 1), ["Tengoku.Seed.M01"])

    def test_the_command_line(self):
        root = tree(self.files(3))
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(sw.main(["plan", "--root", str(root), "--scope", "seed", "--max", "2"]), 0)
        self.assertEqual(out.getvalue().split(), ["Tengoku.Seed.M00", "Tengoku.Seed.M01"])
        out = io.StringIO()
        with redirect_stdout(out):
            sw.main(["plan", "--root", str(root), "--list"])
        info = json.loads(out.getvalue())
        self.assertEqual((info["to_tag"], info["parts"], info["first_of_each_part"]), (3, 1, ["Tengoku.Seed.M00"]))


if __name__ == "__main__":
    unittest.main()
