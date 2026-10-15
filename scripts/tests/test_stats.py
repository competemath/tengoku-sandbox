import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import stats


def write(p: Path, lines):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(json.dumps(l) + "\n" for l in lines))


class StatsTest(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        write(
            self.root / "data/trusted/alpha.jsonl",
            [{"name": "a", "promoted_at": "2026-09-01T00:00:00Z"}, {"name": "b", "promoted_at": "2026-09-13T10:00:00Z"}],
        )
        write(self.root / "data/staging/alpha.jsonl", [{"name": "c"}])
        write(self.root / "data/tentative/beta.jsonl", [{"name": "d"}, {"name": "e"}, {"name": "f"}])
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")

    def test_counts_per_library_and_tier(self):
        s = stats.collect(self.root)
        self.assertEqual(s["libraries"]["alpha"]["trusted"], 2)
        self.assertEqual(s["libraries"]["alpha"]["staging"], 1)
        self.assertEqual(s["libraries"]["alpha"]["tentative"], 0)
        self.assertEqual(s["libraries"]["beta"]["tentative"], 3)
        self.assertEqual(s["totals"], {"trusted": 2, "staging": 1, "tentative": 3, "all": 6, "tentative_already_trusted": 0})
        self.assertEqual(s["library_count"], 2)

    def test_last_promoted_is_the_newest_timestamp(self):
        s = stats.build(self.root)
        self.assertEqual(s["libraries"]["alpha"]["last_promoted_at"], "2026-09-13T10:00:00Z")
        self.assertEqual(s["last_promoted_at"], "2026-09-13T10:00:00Z")
        self.assertEqual(s["toolchain"], "leanprover/lean4:v4.34.0-rc2")
        self.assertRegex(s["generated_at"], r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")

    def test_a_factory_bundles_theorems_count_as_trusted(self):
        """An intake library has no records: its manifest's lines are its trusted theorems (16,699 in 23 libraries were invisible, 2026-10-07)."""
        write(self.root / "data/intake/gamma/manifest.jsonl", [{"name": "g1"}, {"name": "g2"}, {"name": "g3"}])
        write(self.root / "data/intake/alpha/manifest.jsonl", [{"name": "a-in-a-bundle"}])  # records and a bundle: both count
        s = stats.collect(self.root)
        self.assertEqual(
            (s["libraries"]["gamma"]["trusted"], s["libraries"]["gamma"]["intake"], s["libraries"]["gamma"]["staging"]), (3, 3, 0)
        )
        self.assertEqual((s["libraries"]["alpha"]["trusted"], s["libraries"]["alpha"]["intake"]), (3, 1))
        self.assertEqual(s["totals"], {"trusted": 6, "staging": 1, "tentative": 3, "all": 10, "tentative_already_trusted": 0})
        self.assertEqual(s["library_count"], 3)
        self.assertNotIn("intake", s["libraries"]["beta"])

    def test_a_tentative_record_the_tree_already_trusts_is_counted_once(self):
        """Tentative files are append-only: a record stays when its library arrives as a bundle (same statement, bare name) and
        when it is promoted (same name; the trusted copy may drop an attribute). Either way it is one theorem, counted as trusted."""
        write(
            self.root / "data/tentative/delta.jsonl",
            [
                {"name": "lemma1", "statement": "theorem lemma1 (n : ℕ) :\n    n + 0 = n"},
                {"name": "lemma2", "statement": "@[simp] theorem lemma2 : True"},
                {"name": "lemma3", "statement": "theorem lemma3 : 1 = 1"},
                {"name": "lemma4", "statement": "theorem lemma4 : 4 = 4"},
            ],
        )
        write(
            self.root / "data/intake/delta/manifest.jsonl",
            [
                {"name": "Delta.lemma1", "statement": "theorem lemma1 (n : ℕ) : n + 0 = n"},  # the bundle: whitespace aside, the same
                {"name": "Delta.extra", "statement": "theorem extra : 2 = 2"},  # only in the bundle
            ],
        )
        write(
            self.root / "data/trusted/delta.jsonl",
            [{"name": "lemma2", "statement": "theorem lemma2 : True", "promoted_at": "2026-10-01T00:00:00Z"}],
        )
        s = stats.collect(self.root)
        d = s["libraries"]["delta"]
        self.assertEqual((d["trusted"], d["intake"], d["tentative"], d["tentative_already_trusted"]), (3, 2, 2, 2))
        self.assertEqual(s["totals"], {"trusted": 5, "staging": 1, "tentative": 5, "all": 11, "tentative_already_trusted": 2})
        self.assertNotIn("tentative_already_trusted", s["libraries"]["beta"])  # nothing trusted to compare with

    def test_empty_tree(self):
        empty = Path(tempfile.mkdtemp())
        s = stats.collect(empty)
        self.assertEqual(s["totals"]["all"], 0)
        self.assertEqual(s["libraries"], {})


if __name__ == "__main__":
    unittest.main()
