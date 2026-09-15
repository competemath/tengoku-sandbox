import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import derive


class TokensAndGloss(unittest.TestCase):
    def test_tokenizes_dots_underscores_and_camel_case(self):
        self.assertEqual(derive.tokens("Nat.add_comm"), ["nat", "add", "comm"])
        self.assertEqual(derive.tokens("Finset.sum_range_succ"), ["finset", "sum", "range", "succ"])
        self.assertEqual(derive.tokens("MeasureTheory.integral_add"), ["measure", "theory", "integral", "add"])
        self.assertEqual(derive.tokens("Real.sqrt_nonneg'"), ["real", "sqrt", "nonneg"])
        self.assertEqual(derive.tokens("«command#minimize_imports»"), ["command", "minimize", "imports"])

    def test_name_gloss_expands_abbreviations(self):
        g = derive.name_gloss("Nat.add_comm")
        self.assertIn("natural number", g)
        self.assertIn("addition", g)
        self.assertIn("commutative", g)

    def test_statement_gloss_verbalises_symbols(self):
        g = derive.statement_gloss("∀ (a b : ℕ), a + b = b + a")
        self.assertIn("for all", g)
        self.assertIn("natural numbers", g)
        self.assertIn("plus", g)
        self.assertIn("equals", g)
        self.assertNotIn("∀", g)

    def test_topics_from_module(self):
        self.assertEqual(
            derive.topics("Tengoku.Analysis.SpecialFunctions.Trigonometric.Basic"), ["analysis", "special functions", "trigonometric"]
        )


class TypeHash(unittest.TestCase):
    def test_alpha_renaming_gives_the_same_hash(self):
        h1 = derive.type_hash("∀ (a b : ℕ), a + b = b + a", [{"name": "a"}, {"name": "b"}])
        h2 = derive.type_hash("∀ (x y : ℕ), x + y = y + x", [{"name": "x"}, {"name": "y"}])
        self.assertEqual(h1, h2)

    def test_different_statements_differ(self):
        h1 = derive.type_hash("∀ (a b : ℕ), a + b = b + a", [{"name": "a"}, {"name": "b"}])
        h2 = derive.type_hash("∀ (a b : ℕ), a * b = b * a", [{"name": "a"}, {"name": "b"}])
        self.assertNotEqual(h1, h2)

    def test_binder_name_inside_another_identifier_is_untouched(self):
        h = derive.type_hash("∀ (n : ℕ), Nat.succ n = n + 1", [{"name": "n"}])
        h2 = derive.type_hash("∀ (m : ℕ), Nat.succ m = m + 1", [{"name": "m"}])
        self.assertEqual(h, h2)


class Graph(unittest.TestCase):
    def test_pagerank_sums_to_one_and_rewards_in_links(self):
        nodes = ["hub", "a", "b", "c"]
        edges = {"a": ["hub"], "b": ["hub"], "c": ["hub", "a"], "hub": []}
        pr = derive.pagerank(nodes, edges)
        self.assertAlmostEqual(sum(pr.values()), 1.0, places=6)
        self.assertGreater(pr["hub"], pr["a"])
        self.assertGreater(pr["a"], pr["b"])

    def test_derive_end_to_end(self):
        decls = [
            {
                "name": "Nat.add_comm",
                "kind": "theorem",
                "module": "Tengoku.Algebra.Group.Basic",
                "statement": "∀ (n m : ℕ), n + m = m + n",
                "binders": [{"name": "n"}, {"name": "m"}],
                "constants_type": ["Nat", "HAdd.hAdd", "Eq"],
            },
            {
                "name": "Nat.add_zero",
                "kind": "theorem",
                "module": "Tengoku.Init.Nat",
                "statement": "∀ (n : ℕ), n + 0 = n",
                "binders": [{"name": "n"}],
                "constants_type": ["Nat", "HAdd.hAdd", "Eq", "OfNat.ofNat"],
            },
        ]
        deps = {"Nat.add_comm": ["Nat.add_zero", "Nat.succ"], "Nat.add_zero": []}
        derived, symbols, tokens = derive.derive(decls, deps)
        by = {d["name"]: d for d in derived}
        self.assertEqual(by["Nat.add_zero"]["in_degree"], 1)
        self.assertEqual(by["Nat.add_comm"]["out_degree"], 1)  # Nat.succ is not in the index
        self.assertIn("+", by["Nat.add_comm"]["notation_used"])
        self.assertEqual(symbols[0]["df"], 2)
        self.assertEqual({s["name"] for s in symbols if s["df"] == 2}, {"Nat", "HAdd.hAdd", "Eq"})
        self.assertEqual({t["token"]: t["df"] for t in tokens}, {"nat": 2, "add": 2, "comm": 1, "zero": 1})


if __name__ == "__main__":
    unittest.main()
