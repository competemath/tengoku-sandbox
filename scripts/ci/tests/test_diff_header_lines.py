"""_git.added_lines / removed_lines: the `--- a/path` and `+++ b/path` headers are skipped, and nothing else is.

Found 2026-10-13 while testing the credits rule (tengoku#543): both helpers skipped every diff line that STARTS with `---` / `+++`. A removed Lean comment line that begins with `--`
(`-- Authors: Ada Lovelace`, a common credit style at column 0) shows in a diff as `--- Authors: Ada Lovelace`, so the credits gate never saw it: the line could be deleted and the gate
said "credits OK". The same for an added line that begins with `++`."""

from __future__ import annotations

import os
import subprocess
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import Repo  # noqa: E402

LEAN = "Tengoku/Lib/Credit.lean"
CI = HERE.parent  # scripts/ci: the helpers under test (the scratch repository holds only the fixture)
HELPER = "import sys; sys.path.insert(0, sys.argv[3]); import _git; print(repr(getattr(_git, sys.argv[1])('pr~1', 'pr', sys.argv[2])))"


def lines(r: Repo, which: str) -> list:
    out = subprocess.run(
        [sys.executable, "-c", HELPER, which, LEAN, str(CI)],
        cwd=r.dir,
        capture_output=True,
        text=True,
        check=True,
        env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir)},
    ).stdout
    return eval(out)  # noqa: S307  (our own repr of a list of tuples)


def change(before: str, after: str) -> Repo:
    r = Repo()
    r.write(LEAN, before)
    r.commit("m")
    r.write(LEAN, after)
    r.commit("t")
    return r


class HeaderLines(unittest.TestCase):
    def test_a_removed_comment_line_that_starts_with_two_dashes_is_seen(self):
        r = change("-- Authors: Ada Lovelace\ntheorem t : True := trivial\n", "theorem t : True := trivial\n")
        self.assertEqual(lines(r, "removed_lines"), [(1, "-- Authors: Ada Lovelace")])

    def test_an_added_line_that_starts_with_two_pluses_is_seen(self):
        r = change("theorem t : True := trivial\n", "theorem t : True := trivial\n++ x\n")
        self.assertEqual(lines(r, "added_lines"), [(2, "++ x")])

    def test_the_file_headers_are_still_skipped(self):
        r = change("theorem t : True := trivial\n", "theorem u : True := trivial\n")
        self.assertEqual(lines(r, "removed_lines"), [(1, "theorem t : True := trivial")])
        self.assertEqual(lines(r, "added_lines"), [(1, "theorem u : True := trivial")])

    def test_line_numbers_stay_right_after_such_lines(self):
        r = change("a\n-- one\nb\n-- two\nc\n", "a\nb\nc\n")
        self.assertEqual(lines(r, "removed_lines"), [(2, "-- one"), (4, "-- two")])

    def test_the_credits_gate_now_refuses_a_deleted_dash_dash_credit(self):
        r = change("-- Authors: Ada Lovelace\ntheorem t : True := trivial\n", "theorem t : True := trivial\n")
        rc, out = r.gate("credits.py", "pr~1", "pr")
        self.assertEqual(rc, 1, out)
        self.assertIn("Authors: Ada Lovelace", out)

    def test_the_credits_gate_passes_a_dash_dash_comment_that_is_not_a_credit(self):
        r = change("-- a note\ntheorem t : True := trivial\n", "theorem t : True := trivial\n")
        self.assertEqual(r.gate("credits.py", "pr~1", "pr")[0], 0)


if __name__ == "__main__":
    unittest.main()
