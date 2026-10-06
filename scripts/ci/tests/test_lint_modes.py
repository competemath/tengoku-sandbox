"""The content lint of an intake bundle: the exact column-0 rule, the inert commands, and the three modes (strict, proposed, wide).

Regression (2026-10-05): the lint took the first word of every column-0 line outside its command list for the start of a command, so a definition with its
`termination_by`/`decreasing_by` at column 0, or a body that starts with `by`/`fun`/`match`/`rfl` unindented, was refused. On the real shards of lean-pool this one
rule kept 10,937 of 79,378 Gate-2-passed theorems out of the bundle (56,947 -> 67,884 with the rule made exact), on tauceti 233 of 45,969. The rule is exact now: a
word at column 0 starts a command only if it is a command keyword of the tree's Lean (schemas/command-keywords.json, read from Lean's own `command` parser
category), so no list of "words that continue" has to be kept. Its own file, so tests of other gates do not conflict with it."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import allowlist  # noqa: E402
from test_gates import Repo  # noqa: E402

KEYWORDS = set(json.loads((HERE.parent.parent.parent / "schemas" / "command-keywords.json").read_text())["commands"])
OPTIONS = {"maxHeartbeats"}


def refused(text: str, keywords=KEYWORDS) -> list[str]:
    return allowlist.violations(text, OPTIONS, keywords)


class ExactColumnZero(unittest.TestCase):
    def test_what_continues_a_command_is_not_a_command(self):
        for text in (
            "def ack : Nat → Nat → Nat\n  | 0, n => n + 1\n  | m + 1, 0 => ack m 1\n  | m + 1, n + 1 => ack m (ack (m + 1) n)\ntermination_by m n => (m, n)\ndecreasing_by\n  all_goals omega\n",
            "theorem t : True :=\nby\n  trivial\n",
            "def f : Nat → Nat :=\nfun n => n + 1\n",
            "def g (n : Nat) : Nat :=\nmatch n with\n| 0 => 1\n| k + 1 => k\n",
            "theorem t : 1 = 1 :=\nrfl\n",
            "theorem t (l : List Nat) : l.length = l.length :=\nlength_eq l\n",  # a name Mathlib has no command called
            "theorem t : True := by\n  trivial\nfrobnicate\n",  # a word that is no command of the tree: Lean refuses it if it does not continue the command, it never runs
        ):
            self.assertEqual([v for v in refused(text) if "does not start" in v], [], text)

    def test_a_command_keyword_of_the_tree_that_is_not_allowed_is_still_refused_at_column_zero(self):
        for word, text in (
            ("elab", 'elab "x" : term => pure (Lean.mkNatLit 1)\n'),
            ("initialize", "initialize x : Nat ← pure 0\n"),
            ("run_cmd", "run_cmd foo\n"),
            ("macro", 'macro "m" : term => `(1)\n'),
            ("syntax", 'syntax "m" : term\n'),
            ("declare_syntax_cat", "declare_syntax_cat foo\n"),
            ("simproc", "simproc foo (x) := fun _ => pure .continue\n"),
            ("opaque", "opaque f : Nat\n"),
            ("axiom", "axiom a : False\n"),
            ("register_simp_attr", "register_simp_attr foo\n"),
            ("builtin_initialize", "builtin_initialize x : Nat ← pure 0\n"),
        ):
            self.assertIn(f"`{word}` does not start an allowed command", refused(text), text)

    def test_the_conservative_reading_stays_for_callers_without_the_list(self):
        # the records lint passes no list: every word outside the command list at column 0 counts, as before
        self.assertIn(
            "`frobnicate` does not start an allowed command", refused("theorem t : True := trivial\nfrobnicate x\n", keywords=None)
        )
        self.assertIn("`termination_by` does not start an allowed command", refused("def f : Nat := 1\ntermination_by 1\n", keywords=None))

    def test_the_words_this_lint_relies_on_are_in_the_list(self):
        # if a command that runs code were missing from the list, the exact rule would read it as a continuation
        for word in (
            "elab",
            "elab_rules",
            "macro",
            "macro_rules",
            "syntax",
            "declare_syntax_cat",
            "initialize",
            "builtin_initialize",
            "run_cmd",
            "run_elab",
            "run_meta",
            "simproc",
            "dsimproc",
            "opaque",
            "axiom",
            "notation",
            "notation3",
            "infix",
            "infixl",
            "infixr",
            "prefix",
            "postfix",
            "unsafe",
            "partial",
            "import",
            "theorem",
            "def",
            "instance",
            "structure",
            "inductive",
            "namespace",
            "section",
            "end",
            "open",
            "attribute",
            "variable",
            "universe",
            "example",
            "#eval",
            "#check",
            "#print",
            "#guard",
            "grind_pattern",
            "suppress_compilation",
            "deprecated_module",
            "recommended_spelling",
        ):
            self.assertIn(word, KEYWORDS, word)
        self.assertGreater(len(KEYWORDS), 200)

    def test_every_allowed_command_is_a_real_command(self):
        # a word we allow that Lean has no command for would be a typo in COMMANDS; `where`/`mutual` etc. belong to declaration syntax
        for word in allowlist.COMMANDS - {
            "where",
            "lemma",
            "omit",
            "include",
            "library_note",
            "irreducible_def",
            "initialize_simps_projections",
            "add_decl_doc",
            "assert_not_exists",
            "recall",
        }:
            self.assertIn(word, KEYWORDS, word)

    def test_a_continuation_line_is_still_scanned_like_any_other(self):
        for text in (
            "theorem t : True :=\nby native_decide\n",
            "def f : Nat :=\nfun n => run_cmd_marker\ntermination_by initialize\n",
            "theorem t : True :=\nby\n  #eval 1\n  trivial\n",
        ):
            self.assertTrue(refused(text), text)

    def test_a_second_command_after_a_continuation_is_still_seen(self):
        v = refused("def f : Nat := 1\ntermination_by 1\ninitialize x : Nat ← pure 0\n")
        self.assertIn("`initialize` does not start an allowed command", v)


class InertCommands(unittest.TestCase):
    def test_commands_that_carry_no_code_and_change_no_statement_are_allowed(self):
        for text in (
            "grind_pattern foo => bar\n",
            "suppress_compilation\n",
            "unsuppress_compilation\n",
            'recommended_spelling "x" for "y" in foo\n',
            'deprecated_module "use Foo" (since := "2026-01-01")\n',
            "meta section\nend\n",
            "meta def helper : Nat := 1\n",
        ):
            self.assertEqual([v for v in refused(text) if "does not start" in v], [], text)

    def test_meta_is_a_modifier_not_a_way_to_hide_a_command(self):
        self.assertTrue(refused("meta initialize x : Nat ← pure 0\n"))
        self.assertTrue(refused('meta elab "x" : term => pure (Lean.mkNatLit 1)\n'))


class Modes(unittest.TestCase):
    """`intake_check.py --lint strict|proposed|wide` on a module that uses each family."""

    MOD = "import Tengoku\n\nnamespace Fx\n\ntheorem good : 1 + 1 = 2 := rfl\n\nend Fx\n"

    def repo(self):
        r = Repo()
        r.write("lean-toolchain", "leanprover/lean4:v4.34.0-rc2\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\n")
        r.commit("toolchain and All")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def bundle(self, r, mod):
        manifest = {
            "name": "Fx.good",
            "statement": "theorem good : 1 + 1 = 2",
            "module": "Tengoku.FxLib.Fx.Basic",
            "library": "fx-lib",
            "toolchain": "leanprover/lean4:v4.34.0-rc2",
            "via": "equal",
        }
        r.write("Tengoku/FxLib/Fx/Basic.lean", mod)
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.Basic\n")
        r.write("data/intake/fx-lib/manifest.jsonl", json.dumps(manifest) + "\n")
        r.write("data/intake/fx-lib/report.json", "{}\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("intake fx-lib")

    def modes(self, mod):
        r = self.repo()
        self.bundle(r, mod)
        return {m: r.gate("intake_check.py", "main", "pr", "--lint", m)[0] == 0 for m in ("strict", "proposed", "wide")}

    def test_a_plain_module_passes_every_mode(self):
        self.assertEqual(self.modes(self.MOD), {"strict": True, "proposed": True, "wide": True})

    def test_a_column_zero_continuation_passes_every_mode(self):
        mod = self.MOD + "\ndef f (n : Nat) : Nat :=\nmatch n with\n| 0 => 1\n| k + 1 => f k\ntermination_by n\ndecreasing_by omega\n"
        self.assertEqual(self.modes(mod), {"strict": True, "proposed": True, "wide": True})

    def test_notation_needs_proposed_or_wide(self):
        self.assertEqual(self.modes(self.MOD + '\nnotation "ℓ" => 1\n'), {"strict": False, "proposed": True, "wide": True})
        self.assertEqual(self.modes(self.MOD + '\ninfixl:65 " +\' " => Nat.add\n'), {"strict": False, "proposed": True, "wide": True})

    def test_the_macro_family_needs_wide(self):
        for text in (
            '\nmacro "m" : term => `(1)\n',
            '\nsyntax "m2" : term\nmacro_rules\n| `(m2) => `(2)\n',
            "\ndeclare_syntax_cat foo\n",
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": True}, text)

    def test_what_runs_code_is_refused_in_every_mode(self):
        for text in (
            '\nelab "x" : term => pure (Lean.mkNatLit 1)\n',
            "\ninitialize x : Nat ← pure 0\n",
            "\nrun_cmd foo\n",
            "\n#eval 1\n",
            "\ntheorem t : True := by native_decide\n",
            "\naxiom a : False\n",
            "\nopaque f : Nat\n",
            "\nunsafe def u : Nat := 1\n",
            "\n@[implemented_by foo] def g : Nat := 1\n",
            '\ndef h : IO Unit := IO.println "x"\n',
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": False}, text)

    def test_a_macro_cannot_smuggle_a_forbidden_word_in_a_quotation(self):
        # the macro family is allowed in wide, the words it could expand into are not: they stay refused wherever they appear
        for text in (
            '\nmacro "m" : command => `(run_cmd foo)\n',
            '\nmacro "m" : command => `(#eval 1)\n',
            '\nmacro "m" : command => `(initialize x : Nat ← pure 0)\n',
            '\nmacro "m" : term => `(unsafeCast 1)\n',
        ):
            self.assertEqual(self.modes(self.MOD + text)["wide"], False, text)

    def test_an_unknown_mode_is_refused(self):
        r = self.repo()
        self.bundle(r, self.MOD)
        rc, out = r.gate("intake_check.py", "main", "pr", "--lint", "everything")
        self.assertNotEqual(rc, 0)
        self.assertIn("--lint is one of strict, proposed, wide", out)

    def test_the_queues_content_lint_follows_the_mode(self):
        # (module text, the verdict of the queue's lint in strict, proposed, wide): notation from proposed on, the macro family only in wide, elab never
        for text, want in (
            ('\nnotation "ℓ" => 1\n', (False, True, True)),
            ('\nmacro "m" : term => `(1)\n', (False, False, True)),
            ('\nsyntax "m2" : term\n', (False, False, True)),
            ('\nelab "x" : term => pure (Lean.mkNatLit 1)\n', (False, False, False)),
            ("\nelab_rules : term\n| `(x) => pure (Lean.mkNatLit 1)\n", (False, False, False)),
            ('\nscoped elab "x" : term => pure (Lean.mkNatLit 1)\n', (False, False, False)),
            ('\n@[term_elab foo] elab "x" : term => pure (Lean.mkNatLit 1)\n', (False, False, False)),
        ):
            r = self.repo()
            self.bundle(r, self.MOD + text)
            got = tuple(r.gate("lint_banked.py", env={"TENGOKU_INTAKE_LINT": m})[0] == 0 for m in ("strict", "proposed", "wide"))
            self.assertEqual(got, want, text)

    def test_the_queue_refuses_what_runs_code_in_every_mode_even_where_the_macro_family_is_allowed(self):
        r = self.repo()
        self.bundle(r, self.MOD + '\nmacro "m" : command => `(run_cmd foo)\n')
        for mode in ("strict", "proposed", "wide"):
            self.assertNotEqual(r.gate("lint_banked.py", env={"TENGOKU_INTAKE_LINT": mode})[0], 0, mode)


if __name__ == "__main__":
    unittest.main()
