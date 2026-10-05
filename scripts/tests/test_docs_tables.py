"""Every Markdown table of the documentation has one row per line and the same number of cells in every row.

Regression (CodeRabbit, 2026-10-05): a table row of docs/isnad.md was broken over two source lines by an edit, so the second half rendered as a row with too few
cells and the description was cut off. Nothing in CI looked at it.
"""

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DOCS = sorted([*(ROOT / "docs").glob("*.md"), ROOT / "README.md", ROOT / "CONTRIBUTING.md"])


def cells(line: str) -> int:
    return len(re.split(r"(?<!\\)\|", line.strip().strip("|")))


def tables(text: str) -> list[list[tuple[int, str]]]:
    """The tables of a document: each a list of (line number, line) for the consecutive lines that start with `|`."""
    out, block = [], []
    for no, line in enumerate(text.split("\n"), 1):
        if line.startswith("|"):
            block.append((no, line))
        elif block:
            out.append(block)
            block = []
    return out + ([block] if block else [])


def problems(text: str) -> list[str]:
    found = []
    for block in tables(text):
        width = cells(block[0][1])
        for no, line in block:
            if cells(line) != width or not line.rstrip().endswith("|"):
                found.append(f"line {no}: {cells(line)} cells where the header has {width}, or no closing pipe")
    return found


class DocsTables(unittest.TestCase):
    def test_every_table_of_the_docs_is_well_formed(self):
        bad = {str(f.relative_to(ROOT)): problems(f.read_text(encoding="utf-8")) for f in DOCS if problems(f.read_text(encoding="utf-8"))}
        self.assertEqual(bad, {})

    def test_the_isnad_spec_has_its_tables(self):
        # a floor, so that a path or glob change cannot make the check above pass over nothing
        self.assertGreaterEqual(sum(len(tables(f.read_text(encoding="utf-8"))) for f in DOCS), 10)

    def test_the_checker_finds_a_row_split_over_two_lines(self):
        broken = "| a | b |\n|---|---|\n| `x` | first half of a long cell, a bound instance\nvariable included) |\n"
        self.assertEqual(len(problems(broken)), 1)
        self.assertEqual(problems("| a | b |\n|---|---|\n| 1 | 2 |\n"), [])
        self.assertEqual(len(problems("| a | b |\n|---|---|\n| 1 | 2 | 3 |\n")), 1)
        self.assertEqual(len(problems("| a | b |\n|---|---|\n| 1 | 2\n")), 1)


if __name__ == "__main__":
    unittest.main()
