"""credits.py: a credit line that one Markdown file loses and another Markdown file gains, verbatim, has moved, not gone.

Regression (2026-10-07, tengoku#330): the README's credit example (`Author: Ada Lovelace …`) moved to docs/credit.md and the credits
gate refused the PR as a removed credit. Only Markdown to Markdown counts as a move; a credit in a module or a record never travels."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import Repo  # noqa: E402

EXAMPLE = "  Author: Ada Lovelace (https://github.com/ada), with Claude Fable 5.1. -/\n"
SENTENCE = "One sentence on what it says, then one line starting with `Author:`.\n"
README = "# t\n\n## Contributors\n\n  ```lean\n  /-- The sum.\n\n" + EXAMPLE + "  ```\n\n" + SENTENCE


def repo() -> Repo:
    r = Repo()
    r.write("README.md", README)
    r.commit("the credit example in the README")
    return r


def credits(r: Repo):
    return r.gate("credits.py", "pr~1", "pr")


class MarkdownMove(unittest.TestCase):
    def test_a_credit_line_moved_verbatim_to_another_markdown_file_is_not_a_removal(self):
        r = repo()
        r.write("README.md", "# t\n\n## Contributors\n\nSee [credit](docs/credit.md).\n")
        r.write("docs/credit.md", "# Credit\n\n  ```lean\n  /-- The sum.\n\n" + EXAMPLE + "  ```\n\n" + SENTENCE)
        r.commit("move")
        rc, out = credits(r)
        self.assertEqual(rc, 0, out)

    def test_a_credit_line_removed_from_markdown_and_not_re_added_fails(self):
        r = repo()
        r.write("README.md", "# t\n")
        r.commit("drop")
        rc, out = credits(r)
        self.assertEqual(rc, 1)
        self.assertIn("Author: Ada Lovelace", out)

    def test_a_credit_line_re_added_with_different_words_fails(self):
        r = repo()
        r.write("README.md", "# t\n")
        r.write("docs/credit.md", EXAMPLE.replace("Ada Lovelace", "Someone Else") + SENTENCE)
        r.commit("move, changed")
        self.assertEqual(credits(r)[0], 1)

    def test_a_credit_line_moved_into_an_exempt_or_non_markdown_file_still_counts_as_removed(self):
        for target in ("scripts/ci/README.md", "Tengoku/Credit.lean"):
            with self.subTest(target=target):
                r = repo()
                r.write("README.md", "# t\n")
                r.write(target, EXAMPLE + SENTENCE)
                r.commit("move into " + target)
                self.assertEqual(credits(r)[0], 1, target)

    def test_a_modules_credit_does_not_travel_into_markdown(self):
        r = Repo()
        r.write("Tengoku/Logic/Basic.lean", "/-\n-/\ntheorem seeded : True := trivial\n")
        r.write("docs/credit.md", "Authors: Mathlib\n")
        r.commit("strip the module's credit, write it in a doc")
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 1)
        self.assertIn("Authors", out)


if __name__ == "__main__":
    unittest.main()
