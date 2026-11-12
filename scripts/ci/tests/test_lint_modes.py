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

    def test_a_modifier_word_followed_by_a_symbol_is_not_a_command_and_does_not_crash(self):
        """Regression (2026-10-06): lean-pool's bundle compose died with `AttributeError: NoneType has no attribute group` on a column-0 line like `meta : Nat`
        (a structure field called meta): after the modifier is dropped the next word starts with a symbol."""
        for text in (
            "structure S where\nmeta : Nat\n",
            "def f := 1\nprivate (x : Nat)\n",
            "def f := 1\nlocal ⟨x⟩\n",
            "theorem t : True := by\n  trivial\nprotected :=\n",
        ):
            for keywords in (KEYWORDS, None):
                self.assertEqual(refused(text, keywords), [], (text, keywords))

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
        r.write("data/intake/fx-lib/report.json", '{"gate2_unjudged": []}\n')
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("intake fx-lib")

    def modes(self, mod):
        r = self.repo()
        self.bundle(r, mod)
        return {m: r.gate("intake_check.py", "main", "pr", "--lint", m)[0] == 0 for m in ("strict", "proposed", "wide")}

    def test_a_plain_module_passes_every_mode(self):
        self.assertEqual(self.modes(self.MOD), {"strict": True, "proposed": True, "wide": True})

    def test_the_linter_options_that_only_silence_a_warning_are_allowed_and_the_ones_that_change_elaboration_are_not(self):
        """2026-10-18, the OpenAI release's dependencies: `set_option linter.style.header false` (lana-formal-schemes) cost every module that carries it, 693 theorems of one library,
        `linter.unusedSectionVars` 294 of lana-tate-curves-theta: a linter option silences a warning and changes nothing a theorem says. `hygiene`, `quotPrecheck`, `backward.defeqAttrib.useBackward`
        and a library's own options (`leancert.trust`) change how text elaborates, and stay refused."""
        for opt in (
            "linter.style.header",
            "linter.unusedSectionVars",
            "linter.unusedTactic",
            "linter.flexible",
            "linter.unnecessarySimpa",
            "linter.unnecessarySeqFocus",
            "linter.unusedSimpArgs",
            "linter.unreachableTactic",
        ):
            self.assertEqual(
                self.modes(self.MOD + f"\nset_option {opt} false in\ntheorem t2 : True := trivial\n"),
                {"strict": True, "proposed": True, "wide": True},
                opt,
            )
        for opt in ("hygiene", "quotPrecheck", "backward.defeqAttrib.useBackward", "leancert.trust"):
            self.assertEqual(
                self.modes(self.MOD + f"\nset_option {opt} false in\ntheorem t2 : True := trivial\n"),
                {"strict": False, "proposed": False, "wide": False},
                opt,
            )

    def test_a_column_zero_continuation_passes_every_mode(self):
        mod = self.MOD + "\ndef f (n : Nat) : Nat :=\nmatch n with\n| 0 => 1\n| k + 1 => f k\ntermination_by n\ndecreasing_by omega\n"
        self.assertEqual(self.modes(mod), {"strict": True, "proposed": True, "wide": True})

    def test_notation_needs_proposed_or_wide_and_scoped_or_local(self):
        for text in (
            '\nscoped notation "ℓ" => 1\n',
            '\nlocal infixl:65 " +\' " => Nat.add\n',
            '\n@[inherit_doc] scoped prefix:80 "-" => Nat.succ\n',
            '\nscoped notation3 "∑ᵢ " x ", " f => f x\n',
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": True, "wide": True}, text)

    def test_a_global_notation_is_refused_in_every_mode(self):
        """2026-10-17: lean-pool's `prefix:80 "-" => complement` (global) made `-(3 * x)` on ℝ fail in the whole tree, and the atoms of a global notation/syntax/macro became reserved tokens. A mode that
        allows notation allows it `scoped` or `local` only."""
        for text in (
            '\nnotation "ℓ" => 1\n',
            '\ninfixl:65 " +\' " => Nat.add\n',
            '\nprefix:80 "-" => Nat.succ\n',
            '\npostfix:max "!" => Nat.succ\n',
            '\n@[inherit_doc] infixr:35 " ∧ " => And\n',  # attributes in front do not make it scoped
            '\nopen Nat in notation "ℓ" => 1\n',  # nor does an `open … in`
            '\nset_option linter.unusedVariables false in notation "ℓ" => 1\n',
            '\nnotation3 "∑ᵢ " x ", " f => f x\n',
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": False}, text)

    def test_the_macro_family_needs_wide_and_macro_and_syntax_need_scoped_or_local(self):
        for text in (
            '\nscoped macro "m" : term => `(1)\n',
            '\nlocal syntax "m2" : term\nmacro_rules\n| `(m2) => `(2)\n',
            "\ndeclare_syntax_cat foo\n",
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": True}, text)
        for text in (
            '\nmacro "m" : term => `(1)\n',
            '\nsyntax "m2" : term\nmacro_rules\n| `(m2) => `(2)\n',
            '\n@[inherit_doc] syntax "m3" : term\n',
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": False}, text)

    def test_a_word_that_is_not_a_command_is_not_refused_for_being_global(self):
        # a name that ends in the keyword, a dotted name, a docstring and a string: none is a command, so proposed stays as it was for them
        mod = (
            self.MOD
            + "\n/-- The notation `prefix` of a list. -/\ntheorem tp (l : List Nat) (h : List.prefix l = l) (g : isPrefix l = l) : List.postfix l = l := h\n"
            + 'def s : String := "notation \\"x\\" => 1"\n'
        )
        self.assertEqual(self.modes(mod)["proposed"], True)

    def test_a_global_command_in_the_middle_of_a_line_is_refused_in_every_mode(self):
        """gitar on tengoku#615: Lean needs no line break between commands, so the gate reads every occurrence of the keyword, not the start of a line"""
        for text in (
            '\ndef a : Nat := 1 prefix:80 "-" => Nat.succ\n',
            '\ntheorem t2 : True := trivial notation "ℓ" => 1\n',
            '\nprivate infix:50 " ~ " => Nat.add\n',
            '\nprotected notation "ℓ" => 1\n',
            '\nnoncomputable postfix:max "!" => Nat.succ\n',
        ):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": False}, text)
        for text in ('\ndef a : Nat := 1 syntax "m3" : term\n', '\ndef b : Nat := 1 macro "m4" : term => `(1)\n'):
            self.assertEqual(self.modes(self.MOD + text), {"strict": False, "proposed": False, "wide": False}, text)

    def test_the_queue_reads_the_middle_of_a_line_too(self):
        for text in ('\ndef a : Nat := 1 prefix:80 "-" => Nat.succ\n', '\ndef b : Nat := 1 elab "x" : term => pure (Lean.mkNatLit 1)\n'):
            r = self.repo()
            self.bundle(r, self.MOD + text)
            for mode in ("strict", "proposed", "wide"):
                rc, out = r.gate("lint_banked.py", env={"TENGOKU_INTAKE_LINT": mode})
                self.assertNotEqual(rc, 0, f"{mode}: {text}")

    def test_scoped_with_a_namespace_argument_is_scoped(self):
        self.assertEqual(self.modes(self.MOD + '\nscoped[Fx] notation "ℓ" => 1\n'), {"strict": False, "proposed": True, "wide": True})

    def test_the_importers_open_scoped_is_not_a_notation_command(self):
        self.assertEqual(self.modes(self.MOD + "\nopen scoped Fx\n"), {"strict": True, "proposed": True, "wide": True})

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
            ('\nscoped notation "ℓ" => 1\n', (False, True, True)),
            ('\nlocal notation "ℓ" => 1\n', (False, True, True)),
            ('\nnotation "ℓ" => 1\n', (False, False, False)),  # global: refused in every mode
            ('\nscoped macro "m" : term => `(1)\n', (False, False, True)),
            ('\nmacro "m" : term => `(1)\n', (False, False, False)),
            ('\nscoped syntax "m2" : term\n', (False, False, True)),
            ('\nsyntax "m2" : term\n', (False, False, False)),
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


class ChangedModules(unittest.TestCase):
    """2026-10-11: isnad tag PR #438 was ejected from the merge queue by `banked content lint: …PathJoining.lean: notation declarations`. A tag moves the `-/` that closes a docstring to its
    own line, so the docstring's last line (`prefix length](hyp:Z,p,k) with … have [an active prefix](goal).`) was an added line, and read alone it starts with the word `prefix`."""

    DOC = "/-- In [a finite directed acyclic graph](hyp:V,G), [a conditioning set, walk, and\nprefix length](hyp:Z,p,k) with [an active full walk](hyp:hact) have [an active prefix](goal). -/\ntheorem Lib.take : True := trivial\n"

    def changed(self, after: str, before: str | None = None):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("Tengoku/Lib/Doc.lean", before if before is not None else self.DOC)
        r.commit("a module with a docstring")
        r.git("checkout", "-q", "-B", "pr")
        r.write("Tengoku/Lib/Doc.lean", after)
        r.commit("change it")
        return r.gate("lint_banked.py")

    def test_a_docstring_line_that_starts_with_a_command_word_is_prose_when_the_tag_moves_the_close(self):
        tagged = self.DOC.replace("(goal). -/", "(goal).\n@isnad1 id=x from=translated src=- shape=1 vocab=2\n-/")
        rc, out = self.changed(tagged)
        self.assertEqual(rc, 0, out)

    def test_every_word_the_notation_and_macro_rules_name_is_prose_in_a_docstring(self):
        for word in ("notation", "infixl", "infixr", "prefix", "postfix", "macro", "syntax", "elab", "local notation", "scoped macro"):
            doc = (
                f"/-- Intro.\n{word} of the walk is the thing. -/\ntheorem Lib.t : True := trivial\n"  # the rewritten line is the last one
            )
            rc, out = self.changed(doc.replace("thing. -/", "thing.\n@isnad1 id=x\n-/"), before=doc)
            self.assertEqual(rc, 0, f"{word}: {out}")

    def test_code_a_change_adds_is_still_judged(self):
        for added in (
            'notation "ℓ" => 1',
            "#eval 1",
            "initialize x : Nat ← pure 0",
            "native_decide",
            'elab "x" : term => pure (Lean.mkNatLit 1)',
        ):
            rc, out = self.changed(self.DOC + "\n" + added + "\n")
            self.assertEqual(rc, 1, f"{added}: {out}")
        rc, out = self.changed(self.DOC + "\n-- #eval 1 in a line comment\n/- initialize x -/\n")  # prose: comments do not run
        self.assertEqual(rc, 0, out)

    def test_a_close_added_early_turns_what_follows_into_code_that_is_judged(self):
        before = "/-- Intro.\nTalk about things. -/\ntheorem Lib.t : True := trivial\n"
        after = "/-- Intro. -/\n#eval 1\n/- Talk about things. -/\ntheorem Lib.t : True := trivial\n"
        rc, out = self.changed(after, before=before)
        self.assertEqual(rc, 1, out)
        self.assertIn("#eval", out)


class NarrowedNotation(unittest.TestCase):
    """2026-10-17: tengoku#601 (the scope-fix of lean-pool's global notation) was ejected from the merge queue by `banked content lint: …: notation declarations` on 64 modules. Making a
    notation `scoped` or `local` edits the line of its command, so the PR "adds" a notation command; an importer gets `local <command>` for a command that was made local. The text is
    the tree's own, in a narrower scope: in a diff of the scope-fix shape (scope_fix_check.py judges every line of it) that is not a new declaration. Everything else that starts with a
    command word still is, and Gitar's reading of the first version (tengoku#603) is pinned: the exemption is per module, for code, and for commands the PR makes local."""

    GL = 'namespace GL\n\n/-- doc -/\nprefix:80 "-" => complement -- the complement\n\nend GL\n'
    GAL = 'notation "Gal("K ", "F")" => K ≃ₐ[F] K -- Galois group\n'
    INTAKE = {"data/intake/lib/manifest.jsonl": "{}\n"}  # Lib arrived as an intake bundle: its modules are the ones a scope-fix PR may edit

    def changed(self, before: dict, after: dict, env=None, intake=True):
        r = Repo()
        r.git("checkout", "-q", "main")
        for p, s in {**(self.INTAKE if intake else {}), **before}.items():
            r.write(p, s)
        r.commit("modules")
        r.git("checkout", "-q", "-B", "pr")
        for p, s in after.items():
            r.write(p, s)
        r.commit("scope fix")
        return r.gate("lint_banked.py", env=env)

    def test_a_notation_made_scoped_or_local_is_not_a_new_declaration_in_any_mode(self):
        for mode in (None, "strict", "proposed", "wide"):
            env = {"TENGOKU_INTAKE_LINT": mode} if mode else None
            rc, out = self.changed(
                {"Tengoku/Lib/Modal.lean": self.GL},
                {
                    "Tengoku/Lib/Modal.lean": self.GL.replace('prefix:80 "-"', 'scoped prefix:80 "-"').replace(
                        "end GL\n",
                        "end GL\n\nopen scoped GL\n-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)\n",
                    )
                },
                env,
            )
            self.assertEqual(rc, 0, f"{mode}: {out}")

    def test_the_importers_copy_of_a_command_made_local_is_not_a_new_declaration(self):
        rc, out = self.changed(
            {"Tengoku/Lib/Gal.lean": self.GAL, "Tengoku/Lib/Use.lean": "theorem u : True := trivial\n"},
            {
                "Tengoku/Lib/Gal.lean": "local " + self.GAL,
                "Tengoku/Lib/Use.lean": 'local notation "Gal("K ", "F")" => K ≃ₐ[F] K\n\ntheorem u : True := trivial\n',
            },
        )
        self.assertEqual(rc, 0, out)

    def test_attributes_stay_in_front_and_the_macro_family_and_elab_narrow_too(self):
        for src, after in (
            ('@[inherit_doc X] infix : 120 " ∈ " => f\n', '@[inherit_doc X] scoped infix : 120 " ∈ " => f\n'),
            ('macro "m" : term => `(1)\n', 'scoped macro "m" : term => `(1)\n'),
            ('syntax "m2" : term\n', 'scoped syntax "m2" : term\n'),
            ('elab "x" : term => pure (Lean.mkNatLit 1)\n', 'scoped elab "x" : term => pure (Lean.mkNatLit 1)\n'),
        ):
            rc, out = self.changed(
                {"Tengoku/Lib/Modal.lean": "namespace GL\n" + src + "end GL\n"},
                {"Tengoku/Lib/Modal.lean": "namespace GL\n" + after + "end GL\n"},
            )
            self.assertEqual(rc, 0, f"{src}: {out}")

    def test_a_notation_that_is_not_the_old_line_with_a_word_in_front_is_a_new_declaration(self):
        for after in (
            self.GL.replace('prefix:80 "-" => complement', 'scoped prefix:80 "-" => evil'),  # another right-hand side
            self.GL.replace('prefix:80 "-" => complement', 'scoped prefix:80 "~" => complement'),
            self.GL + 'scoped notation "ℓ" => 1\n',  # nothing was removed for it
            self.GL.replace("prefix:80", "notation:80", 1),
        ):
            rc, out = self.changed({"Tengoku/Lib/Modal.lean": self.GL}, {"Tengoku/Lib/Modal.lean": after})
            self.assertEqual(rc, 1, f"{after}: {out}")
            self.assertIn("notation declarations", out)

    def test_a_local_copy_needs_a_command_some_module_of_the_pr_makes_local(self):
        use = {"Tengoku/Lib/Use.lean": 'local notation "Gal("K ", "F")" => K ≃ₐ[F] K\n\ntheorem u : True := trivial\n'}
        for gal in (
            self.GAL,
            "scoped " + self.GAL,
        ):  # nothing was changed / it was made scoped, not local: an importer opens it, it does not declare it again
            rc, out = self.changed(
                {"Tengoku/Lib/Gal.lean": self.GAL, "Tengoku/Lib/Use.lean": "theorem u : True := trivial\n"},
                {"Tengoku/Lib/Gal.lean": gal, **use},
            )
            self.assertEqual(rc, 1, f"{gal}: {out}")
            self.assertIn("notation declarations", out)

    def test_a_narrowed_line_hides_nothing_else(self):
        rc, out = self.changed(
            {"Tengoku/Lib/Modal.lean": self.GL},
            {"Tengoku/Lib/Modal.lean": self.GL.replace('prefix:80 "-"', 'scoped prefix:80 "-"') + "#eval 1\n"},
        )
        self.assertEqual(rc, 1, out)
        self.assertIn("#eval", out)
        self.assertNotIn("notation declarations", out)

    def test_a_line_that_was_prose_in_the_base_does_not_come_back_as_code(self):
        # Gitar on tengoku#603: PR 1 puts `elab …` in a docstring (prose, passes), PR 2 removes that line and adds `scoped elab …` as code
        doc = '/-- Intro.\nelab "e" : term => pure (Lean.mkNatLit 1)\n-/\ntheorem Lib.t : True := trivial\n'
        code = 'scoped elab "e" : term => pure (Lean.mkNatLit 1)\ntheorem Lib.t : True := trivial\n'
        rc, out = self.changed({"Tengoku/Lib/Doc.lean": doc}, {"Tengoku/Lib/Doc.lean": code})
        self.assertEqual(rc, 1, out)
        self.assertIn("elab declarations", out)

    def test_a_line_that_was_prose_in_the_base_does_not_come_back_as_a_local_copy(self):
        # the same through the importer-copy path: the docstring line equals the added line minus `local`
        doc = '/-- Intro.\nelab "e" : term => pure (Lean.mkNatLit 1)\n-/\ntheorem Lib.t : True := trivial\n'
        rc, out = self.changed(
            {"Tengoku/Lib/Doc.lean": doc.replace('elab "e" : term => pure (Lean.mkNatLit 1)', 'notation "e" => 1')},
            {"Tengoku/Lib/Doc.lean": 'local notation "e" => 1\ntheorem Lib.t : True := trivial\n'},
        )
        self.assertEqual(rc, 1, out)
        self.assertIn("notation declarations", out)

    def test_a_line_removed_from_one_module_does_not_excuse_the_same_text_in_another(self):
        other = "namespace GL\n\nend GL\n"
        rc, out = self.changed(
            {"Tengoku/Lib/Modal.lean": self.GL, "Tengoku/Lib/Other.lean": other},
            {
                "Tengoku/Lib/Modal.lean": self.GL.replace('prefix:80 "-" => complement -- the complement\n', ""),
                "Tengoku/Lib/Other.lean": other.replace("\nend GL", 'scoped prefix:80 "-" => complement -- the complement\nend GL'),
            },
        )
        self.assertEqual(rc, 1, out)
        self.assertIn("Other.lean: notation declarations", out)

    def test_only_a_diff_of_the_scope_fix_shape_gets_the_exemption(self):
        scoped = self.GL.replace('prefix:80 "-"', 'scoped prefix:80 "-"')
        for kw in (
            {"intake": False},  # Lib is no intake library at the base
        ):
            rc, out = self.changed({"Tengoku/Lib/Modal.lean": self.GL}, {"Tengoku/Lib/Modal.lean": scoped}, **kw)
            self.assertEqual(rc, 1, f"{kw}: {out}")
            self.assertIn("Modal.lean: notation declarations", out)
        rc, out = self.changed(
            {"Tengoku/Lib/Modal.lean": self.GL}, {"Tengoku/Lib/Modal.lean": scoped, "Tengoku/Lib/New.lean": "theorem n : True := trivial\n"}
        )  # also adds a module
        self.assertEqual(rc, 1, out)
        self.assertIn("Modal.lean: notation declarations", out)
        rc, out = self.changed(
            {"Tengoku/Lib/Modal.lean": self.GL}, {"Tengoku/Lib/Modal.lean": scoped, "scripts/x.py": "print(2)\n"}
        )  # also touches a tool
        self.assertEqual(rc, 1, out)
        self.assertIn("Modal.lean: notation declarations", out)

    def test_a_scoped_line_added_elsewhere_does_not_scope_a_later_added_notation(self):
        """Gitar on tengoku#615: the added lines of a module were joined, so a lone `scoped` line added far above made a `notation` added far below look scoped. The command is judged against the
        module as it stands (the line before it is the module's own), and counted when it is on an added line."""
        before = 'theorem t : True := trivial\n\nnotation "a" => 1\n\ntheorem u : True := trivial\n'
        after = "scoped\n" + before + '\nnotation "-" => evil\n'
        manifest = {
            "data/intake/lib/manifest.jsonl": "{}\n{}\n"
        }  # the PR also touches the bundle's manifest: the module is the bundle's own, where the mode allows notation
        for mode in ("proposed", "wide"):
            rc, out = self.changed(
                {"Tengoku/Lib/Mod.lean": before}, {"Tengoku/Lib/Mod.lean": after, **manifest}, env={"TENGOKU_INTAKE_LINT": mode}
            )
            self.assertEqual(rc, 1, f"{mode}: {out}")
            self.assertIn("`notation` without `scoped` or `local`", out)
        # the same PR with the second notation really scoped passes: only the added line is judged, the old global one is the tree's
        rc, out = self.changed(
            {"Tengoku/Lib/Mod.lean": before},
            {"Tengoku/Lib/Mod.lean": before + '\nscoped notation "-" => evil\n', **manifest},
            env={"TENGOKU_INTAKE_LINT": "proposed"},
        )
        self.assertEqual(rc, 0, out)

    def test_deleting_the_scoped_line_in_front_of_an_unchanged_notation_makes_it_global(self):
        """CodeRabbit on tengoku#615: Lean allows a line break between `scoped` and the command. Deleting the `scoped` line leaves the notation's own line untouched, but the module declares one more
        global command than the base did."""
        before = 'theorem t : True := trivial\n\nscoped\nnotation "q" => 1\n'
        after = 'theorem t : True := trivial\n\nnotation "q" => 1\n'
        for mode in (None, "proposed", "wide"):
            env = {"TENGOKU_INTAKE_LINT": mode} if mode else None
            rc, out = self.changed({"Tengoku/Lib/Mod.lean": before}, {"Tengoku/Lib/Mod.lean": after}, env=env)
            self.assertEqual(rc, 1, f"{mode}: {out}")
            self.assertIn("`notation` without `scoped` or `local`", out)

    def test_a_global_notation_the_tree_already_has_is_not_a_new_one(self):
        before = 'theorem t : True := trivial\n\nnotation "q" => 1\n\n-- old\n'
        after = 'theorem t : True := trivial\n\nnotation "q" => 1\n\n-- new\ntheorem u : True := trivial\n'
        rc, out = self.changed({"Tengoku/Lib/Mod.lean": before}, {"Tengoku/Lib/Mod.lean": after})
        self.assertEqual(rc, 0, out)
        rc, out = self.changed(
            {"Tengoku/Lib/Mod.lean": before}, {"Tengoku/Lib/Mod.lean": after + 'notation "q" => 1\n'}
        )  # the same text a second time is one more
        self.assertEqual(rc, 1, out)

    ET = "Tengoku/EquationalTheories/Asterix.lean"  # equational-theories has a corpus in schemas/sources.json: the generator rebuilds it, it is no intake bundle

    def test_a_regeneration_of_a_generated_library_may_narrow_its_notation_the_same_way(self):
        """2026-10-18: equational-theories (generated) keeps 11 global notation commands that scripts/generate.py now scopes (scripts/scope_notation.py). The regenerated modules are the old ones with
        `scoped`/`local` in front of those lines, a promotion PR, and only that is exempt."""
        scoped = self.GL.replace('prefix:80 "-"', 'scoped prefix:80 "-"').replace("end GL\n", "end GL\n\nopen scoped GL\n")
        rc, out = self.changed({self.ET: self.GL}, {self.ET: scoped}, intake=False)
        self.assertEqual(rc, 0, out)
        for after in (
            self.GL.replace('prefix:80 "-" => complement', 'scoped prefix:80 "-" => evil'),  # another right-hand side
            self.GL + 'scoped notation "ℓ" => 1\n',  # a command nothing was removed for
            self.GL.replace('prefix:80 "-"', 'prefix:80 "-"') + 'notation "ℓ" => 1\n',  # a global one
        ):
            rc, out = self.changed({self.ET: self.GL}, {self.ET: after}, intake=False)
            self.assertEqual(rc, 1, f"{after}: {out}")
            self.assertIn("notation declarations", out)
        rc, out = self.changed(
            {self.ET: self.GL}, {self.ET: scoped, "Tengoku/EquationalTheories/New.lean": "theorem n : True := trivial\n"}, intake=False
        )  # also adds a module
        self.assertEqual(rc, 1, out)
        self.assertIn("Asterix.lean: notation declarations", out)


if __name__ == "__main__":
    unittest.main()
