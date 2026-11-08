"""credits.py: a docstring that gets a line added at its end loses its ` -/` on the line that carried it; the credit text is still there.

Regression (2026-10-13, tengoku#539): the isnad tagger appends `@isnad1 ...` inside an existing docstring, which rewrites its last line (`... no further credit. -/`
becomes `... no further credit.`), and the credits gate refused the PR: the sentence contains the ordinary word "credit". A line whose text survives verbatim as a gained line,
with only the terminator gone, has lost nothing; every other change of a marker line still fails."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import Repo  # noqa: E402

LEAN = "Tengoku/Lib/Potential.lean"
DOC = "/-- A selected boundary endpoint supplies four credits. All added vertices\nare outside earlier configurations, so they require no further credit. -/\ntheorem t : True := trivial\n"
AUTHORED = "/-- The sum.\n\nAuthors: Ada Lovelace (https://github.com/ada). -/\ntheorem s : True := trivial\n"


def pr(before: str, after: str):
    r = Repo()
    r.write(LEAN, before)
    r.commit("the module")
    r.write(LEAN, after)
    r.commit("the tags")
    return r.gate("credits.py", "pr~1", "pr")


class DocstringTerminator(unittest.TestCase):
    def test_a_tag_appended_inside_a_docstring_whose_last_line_says_credit_passes(self):
        after = DOC.replace("further credit. -/\n", "further credit.\n@isnad1 id=le.1 from=translated\n-/\n")
        rc, out = pr(DOC, after)
        self.assertEqual(rc, 0, out)

    def test_the_same_for_an_authors_line(self):
        after = AUTHORED.replace("/ada). -/\n", "/ada).\n@isnad1 id=le.1\n-/\n")
        rc, out = pr(AUTHORED, after)
        self.assertEqual(rc, 0, out)

    def test_a_credit_that_changes_words_while_the_terminator_moves_still_fails(self):
        after = AUTHORED.replace("Ada Lovelace (https://github.com/ada). -/\n", "Someone Else.\n@isnad1 id=le.1\n-/\n")
        self.assertEqual(pr(AUTHORED, after)[0], 1)

    def test_a_credit_line_that_is_removed_outright_still_fails(self):
        after = AUTHORED.replace("Authors: Ada Lovelace (https://github.com/ada). -/\n", "-/\n")
        self.assertEqual(pr(AUTHORED, after)[0], 1)

    def test_text_added_on_the_same_line_as_the_credit_still_fails(self):
        after = DOC.replace("further credit. -/\n", "further credit. and more.\n@isnad1 id=le.1\n-/\n")
        self.assertEqual(pr(DOC, after)[0], 1)  # the line is not the old one with the terminator gone: a person looks

    def test_a_marker_line_changed_without_a_terminator_still_fails(self):
        before = "/-\nAuthors: Ada Lovelace\n-/\ntheorem t : True := trivial\n"
        self.assertEqual(pr(before, before.replace("Ada Lovelace", "Grace Hopper"))[0], 1)

    def test_one_gained_line_covers_one_removal(self):
        """Two docstrings end in the same sentence; one gets its tag, the other loses the sentence outright: the single gained line covers one removal, not both."""
        second = DOC.replace("theorem t", "theorem u")
        tagged = DOC.replace("further credit. -/\n", "further credit.\n@isnad1 id=le.1\n-/\n")
        lost = second.replace("so they require no further credit. -/\n", "-/\n")
        self.assertEqual(pr(DOC + second, tagged + lost)[0], 1)
        both = second.replace("further credit. -/\n", "further credit.\n@isnad1 id=le.2\n-/\n")
        rc, out = pr(DOC + second, tagged + both)
        self.assertEqual(rc, 0, out)  # two gains, two removals

    def test_only_lean_files_get_the_allowance(self):
        r = Repo()
        r.write("Tengoku/Lib/notes.md", "Authors: Ada Lovelace -/\n")
        r.commit("md")
        r.write("Tengoku/Lib/notes.md", "Authors: Ada Lovelace\n")
        r.commit("md2")
        self.assertEqual(r.gate("credits.py", "pr~1", "pr")[0], 1)


if __name__ == "__main__":
    unittest.main()
