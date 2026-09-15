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
        self.assertEqual(s["totals"], {"trusted": 2, "staging": 1, "tentative": 3, "all": 6})
        self.assertEqual(s["library_count"], 2)

    def test_last_promoted_is_the_newest_timestamp(self):
        s = stats.build(self.root)
        self.assertEqual(s["libraries"]["alpha"]["last_promoted_at"], "2026-09-13T10:00:00Z")
        self.assertEqual(s["last_promoted_at"], "2026-09-13T10:00:00Z")
        self.assertEqual(s["toolchain"], "leanprover/lean4:v4.34.0-rc2")
        self.assertRegex(s["generated_at"], r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")

    def test_empty_tree(self):
        empty = Path(tempfile.mkdtemp())
        s = stats.collect(empty)
        self.assertEqual(s["totals"]["all"], 0)
        self.assertEqual(s["libraries"], {})


if __name__ == "__main__":
    unittest.main()
