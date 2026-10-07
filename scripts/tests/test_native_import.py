"""scripts/native_import.py: trusted records into modules of Tengoku/Native/. Its own file, so tests of other tools do not conflict with it."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / "ci"))
import allowlist  # noqa: E402
import native_import as ni  # noqa: E402

OPTIONS = set(json.loads((HERE.parent.parent / "schemas" / "allowed-options.json").read_text())["allowed"])
KEYWORDS = set(json.loads((HERE.parent.parent / "schemas" / "command-keywords.json").read_text())["commands"])


def rec(name, statement, proof=":= rfl", n=1, url=None):
    return {
        "name": name,
        "statement": statement,
        "proof": proof,
        "status": "trusted",
        "library": "competemath",
        "source_url": url or f"https://competemath.com/practice/problems/{n}",
        "toolchain": "leanprover/lean4:v4.29.1",
    }


ONE = rec("one", "import Mathlib\n\ntheorem one : 1 + 1 = 2", n=1)
TWO = rec("two", "import Mathlib\n\nset_option maxRecDepth 8000\nopen Finset\n\ntheorem two : (Finset.range 3).card = 3", ":= by simp", n=2)


def build(records, **kw):
    return ni.build(records, "Competemath", "competemath.com", set(kw.get("exclude", ())), kw.get("per_module", 40), "CompeteMath")


class Selection(unittest.TestCase):
    def test_a_record_that_trusts_the_compiler_or_is_unfinished_is_left_out(self):
        for bad in (
            ":= by native_decide",
            ":= by sorry",
            ":= by\n  exact Lean.ofReduceBool _ _ rfl",
            ":= by decide +native -- native_decide",
        ):
            files, out, where = build([ONE, rec("bad", "import Mathlib\n\ntheorem bad : 1 = 1", bad, n=3)])
            self.assertEqual(sorted(where), ["one"], bad)
            self.assertEqual([n for n, _ in out], ["bad"])

    def test_the_word_in_a_longer_name_does_not_count_but_an_axiom_helper_does(self):
        self.assertIsNone(ni.left_out(rec("a", "theorem a : 1 = 1", ":= not_sorry_lemma"), set(), set()))
        self.assertIsNone(ni.left_out(rec("a", "theorem a : 1 = 1", ":= foo_sorry"), set(), set()))  # a name that ends in the word
        self.assertIsNotNone(ni.left_out(rec("a", "theorem a : 1 = 1", ":= Foo._native.native_decide.ax_1"), set(), set()))

    def test_no_theorem_a_repeated_name_and_an_excluded_one(self):
        files, out, where = build(
            [ONE, ONE, rec("d", "import Mathlib\n\ndef d : ℕ := 1", ":= rfl", n=4), rec("ex", "theorem ex : 1 = 1", n=5)], exclude=["ex"]
        )
        self.assertEqual(sorted(where), ["one"])
        self.assertEqual(sorted(w for _, w in out), ["a name this source already has", "excluded", "no theorem or lemma of its own"])

    def test_a_lemma_counts_and_so_does_an_attribute(self):
        files, out, where = build([rec("l", "import Mathlib\n\n@[simp] lemma l : 1 = 1", n=6)])
        self.assertEqual(list(where), ["l"])


class Rendering(unittest.TestCase):
    def test_every_record_has_a_namespace_and_a_docstring_of_its_own(self):
        files, _, _ = build([ONE, TWO])
        text = next(t for p, t in files.items() if p.endswith(".lean") and "Native/Competemath/" in p and "theorem one" in t)
        self.assertIn("namespace Native.Competemath.P1\n", text)
        self.assertIn("/-- competemath.com problem 1. -/\ntheorem one", text)
        self.assertIn("end Native.Competemath.P1\n", text)

    def test_the_preamble_stays_inside_its_namespace(self):
        files, _, _ = build([TWO])
        text = next(t for t in files.values() if "theorem two" in t)
        ns, end = text.index("namespace Native.Competemath.P2"), text.index("end Native.Competemath.P2")
        for needle in ("set_option maxRecDepth 8000", "open Finset", "/-- competemath.com problem 2. -/\ntheorem two"):
            self.assertTrue(ns < text.index(needle) < end, needle)
        self.assertNotIn("import Mathlib", text)

    def test_two_records_of_one_problem_get_two_namespaces(self):
        files, _, where = build([ONE, rec("one_again", "import Mathlib\n\ntheorem one_again : 1 + 1 = 2", ":= by norm_num", n=1)])
        text = "".join(files.values())
        self.assertEqual(len(where), 2)
        self.assertIn("namespace Native.Competemath.P1\n", text)
        self.assertIn("namespace Native.Competemath.P1_2\n", text)

    def test_a_docstring_the_record_has_is_kept_and_not_doubled(self):
        files, _, _ = build([rec("o", "import Mathlib\n\n/-- My own words. -/\ntheorem o : 1 = 1", n=7)])
        text = "".join(files.values())
        self.assertIn("My own words.", text)
        self.assertEqual(text.count("/--"), 1)

    def test_a_helper_definition_is_inside_the_namespace_and_before_the_theorem(self):
        r = rec("t", "import Mathlib\n\ndef f : ℕ → ℕ\n  | 0 => 0\n  | n+1 => f n\n\ntheorem t : f 2 = 0", ":= rfl", n=8)
        text = "".join(build([r])[0].values())
        self.assertLess(text.index("def f"), text.index("theorem t"))
        self.assertLess(text.index("namespace Native.Competemath.P8"), text.index("def f"))

    def test_the_header_credits_the_author_and_imports_only_the_tree(self):
        files, _, _ = build([ONE])
        module = next(t for p, t in files.items() if "Native/Competemath/" in p)
        self.assertTrue(module.startswith("/-\nAuthors: CompeteMath\n-/\nimport Tengoku\n"))

    def test_the_umbrella_imports_every_module_once(self):
        files, _, _ = build([ONE, TWO, rec("x", "import Mathlib\n\ntheorem x : Real.pi > 3", ":= by positivity", n=9)])
        umbrella = [ln.split()[1] for ln in files["Tengoku/Native.lean"].splitlines()]
        modules = sorted(p[: -len(".lean")].replace("/", ".") for p in files if p.startswith("Tengoku/Native/"))
        self.assertEqual(umbrella, modules)

    def test_what_it_writes_passes_the_content_lint_of_the_gate(self):
        files, _, _ = build([ONE, TWO])
        for path, text in files.items():
            if path == "Tengoku/Native.lean":
                continue
            body = "\n".join("" if ln.startswith("import ") else ln for ln in text.split("\n"))
            self.assertEqual(allowlist.violations(body, OPTIONS, KEYWORDS), [], path)


class Commands(unittest.TestCase):
    def test_the_docstring_goes_in_front_of_attributes_on_their_own_line(self):
        files, _, _ = build([rec("a", "import Mathlib\n\n@[simp]\n@[norm_cast]\ntheorem a : 1 = 1", n=11)])
        text = "".join(files.values())
        self.assertIn("/-- competemath.com problem 11. -/\n@[simp]\n@[norm_cast]\ntheorem a", text)

    def test_what_is_a_theorem_command(self):
        for line in (
            "theorem a : True",
            "  lemma a : True",
            "@[simp] private lemma a : True",
            "noncomputable protected theorem Nat.a : True",
        ):
            self.assertTrue(ni.starts_theorem(line), line)
        for line in ("theorem", "def theorem_a := 1", "@[simp def x := 1", "@[simp] def a := 1", "mytheorem a : True"):
            self.assertFalse(ni.starts_theorem(line), line)

    def test_a_crafted_line_does_not_make_it_slow(self):
        """CodeQL found the old attribute pattern exponential on '@[]' followed by many '\\t@[]'"""
        import time

        t0 = time.time()
        self.assertIsNone(ni.theorem_offset("@[]" + "\t@[]" * 5000 + "\n"))
        self.assertIsNotNone(ni.theorem_offset("@[]" + "\t@[]" * 5000 + " theorem t : True := trivial\n"))
        self.assertLess(time.time() - t0, 2.0)


class Areas(unittest.TestCase):
    def test_the_words_of_a_statement_decide(self):
        self.assertEqual(ni.area_of("theorem a (p : ℕ) (hp : Nat.Prime p) : p ∣ 6"), "NumberTheory")
        self.assertEqual(ni.area_of("theorem a : (Finset.range 4).card = 4"), "Combinatorics")
        self.assertEqual(ni.area_of("theorem a : Polynomial.eval 1 (Polynomial.X : Polynomial ℤ) = 1"), "Polynomials")
        self.assertEqual(ni.area_of("theorem a : (1 : ℝ) = 1"), "Misc")

    def test_a_big_area_is_cut_into_numbered_modules(self):
        recs = [rec(f"c{i}", f"import Mathlib\n\ntheorem c{i} : (Finset.range {i}).card = {i}", ":= by simp", n=100 + i) for i in range(5)]
        files, _, _ = build(recs, per_module=2)
        self.assertEqual(
            sorted(p for p in files if "Native/Competemath/" in p), [f"Tengoku/Native/Competemath/Combinatorics{k}.lean" for k in (1, 2, 3)]
        )

    def test_the_command_line_writes_files_and_a_report(self):
        d = Path(tempfile.mkdtemp())
        (d / "r.jsonl").write_text(
            "".join(json.dumps(r) + "\n" for r in (ONE, rec("bad", "theorem bad : 1 = 1", ":= by native_decide", n=3)))
        )
        self.assertEqual(ni.main([str(d / "r.jsonl"), "--out", str(d / "out")]), 0)
        report = json.loads((d / "out" / "native-import.json").read_text())
        self.assertEqual([n for n, _ in report["left_out"]], ["bad"])
        self.assertTrue((d / "out" / "Tengoku" / "Native.lean").is_file())


if __name__ == "__main__":
    unittest.main()
