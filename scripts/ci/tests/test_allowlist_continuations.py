"""allowlist.py: a word at column 0 that continues the command above is not a new command.

Regression (2026-10-05): the lint took the first word of every column-0 line outside its command list for the start of a command, so a definition with its
`termination_by`/`decreasing_by` at column 0, or a body that starts with `by`/`fun`/`match` unindented, was refused as "does not start an allowed command". Of the
theorems the factory could not bundle, 2,176 + 1,987 module-uses were `termination_by`/`decreasing_by`, 769 `by`, 317 `fun`, 163 `match` (compfiles,
imoshortlist, lean-pool). The list of continuations is short on purpose: an unknown word is still refused, and everything on a continuation line is still scanned."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import allowlist  # noqa: E402


def refused(text: str) -> list[str]:
    return allowlist.violations(text, {"maxHeartbeats"})


class Continuations(unittest.TestCase):
    def test_termination_clauses_at_column_zero(self):
        text = (
            "def ack : Nat → Nat → Nat\n"
            "  | 0, n => n + 1\n"
            "  | m + 1, 0 => ack m 1\n"
            "  | m + 1, n + 1 => ack m (ack (m + 1) n)\n"
            "termination_by m n => (m, n)\n"
            "decreasing_by\n"
            "  all_goals simp_wf\n"
            "  all_goals omega\n"
        )
        self.assertEqual(refused(text), [])

    def test_an_unindented_body(self):
        for text in (
            "theorem t : True :=\nby\n  trivial\n",
            "def f : Nat → Nat :=\nfun n => n + 1\n",
            "def g (n : Nat) : Nat :=\nmatch n with\n| 0 => 1\n| k + 1 => k\n",
        ):
            self.assertEqual([v for v in refused(text) if "does not start" in v], [], text)

    def test_an_unknown_word_is_still_not_a_command(self):
        # including words that look harmless but were not among the ones the reports show: the list is the observed five, not "anything lowercase"
        for word in ("frobnicate", "length", "run_cmd_like", "informal_lemma", "if", "then"):
            self.assertIn(f"`{word}` does not start an allowed command", refused(f"theorem t : True := trivial\n{word} x\n"))

    def test_the_commands_that_run_code_are_still_refused_at_column_zero(self):
        for text in (
            "run_cmd foo\n",
            "initialize x : Nat ← pure 0\n",
            'elab "x" : term => pure (Lean.mkNatLit 1)\n',
            "#eval 1\n",
            'macro "m" : term => `(1)\n',
        ):
            self.assertTrue(refused(text), text)

    def test_a_continuation_line_is_still_scanned_like_any_other(self):
        # the keyword is allowed to continue; what follows it is read as usual
        for text in (
            "theorem t : True :=\nby native_decide\n",
            "def f : Nat :=\nfun n => run_cmd_marker\ntermination_by initialize\n",
            "theorem t : True :=\nby\n  #eval 1\n  trivial\n",
        ):
            self.assertTrue(refused(text), text)

    def test_a_continuation_word_does_not_hide_a_second_command_on_the_next_line(self):
        v = refused("def f : Nat := 1\ntermination_by 1\nfrobnicate\n")
        self.assertIn("`frobnicate` does not start an allowed command", v)


if __name__ == "__main__":
    unittest.main()
