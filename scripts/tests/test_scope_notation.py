"""scripts/scope_notation.py: a generated library must not leak notation, macros, elaborators or syntax (2026-10-17/18, lean-pool's `prefix:80 "-"`, equational-theories' `elab "resolve"`).
Pure text: Lean is not run (the merge queue builds the modules). Its own file, so tests of other scripts do not conflict with it."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import scope_notation as sn  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_generate_verified import HEAD, own, prelude, rec  # noqa: E402


class Library(unittest.TestCase):
    """a library directory <tmp>/Tengoku/Lx with the given modules"""

    def make(self, files: dict[str, str]) -> Path:
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        for rel, text in files.items():
            p = tmp / "Tengoku" / "Lx" / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return tmp / "Tengoku" / "Lx"

    def run_pass(self, lib: Path, **kw):
        return sn.scope_library(lib, "Lx", **kw)

    def text(self, lib: Path, rel: str) -> str:
        return (lib / rel).read_text()


class Commands(Library):
    def test_a_command_in_a_namespace_becomes_scoped_and_one_at_the_root_local(self):
        lib = self.make({"A.lean": 'namespace Lx\nprefix:80 "-" => neg\nend Lx\n', "B.lean": 'notation "Gal" => G\n'})
        r = self.run_pass(lib)
        self.assertEqual(self.text(lib, "A.lean"), 'namespace Lx\nscoped prefix:80 "-" => neg\nend Lx\n')
        self.assertEqual(self.text(lib, "B.lean"), 'local notation "Gal" => G\n')
        self.assertEqual((len(r["scoped"]), r["unscopable"]), (2, []))

    def test_every_kind_of_command_and_what_stands_before_it(self):
        src = (
            "namespace Lx\n"
            'infixl:65 " ⊕ " => f\n'
            'postfix:max "!" => g\n'
            'notation3 "∑ " x => h\n'
            '@[inherit_doc] infix:50 " ≺ " => lt\n'
            'syntax "myterm" : term\n'
            "open Lean in\n"
            'macro "Facts " x:term : term => `($x)\n'
            'elab "resolve " a:term : term => do pure a\n'
            "end Lx\n"
        )
        lib = self.make({"A.lean": src})
        self.run_pass(lib)
        got = self.text(lib, "A.lean")
        for line in (
            'scoped infixl:65 " ⊕ " => f',
            'scoped postfix:max "!" => g',
            'scoped notation3 "∑ " x => h',
            '@[inherit_doc] scoped infix:50 " ≺ " => lt',
            'scoped syntax "myterm" : term',
            'scoped macro "Facts " x:term : term => `($x)',
            'scoped elab "resolve " a:term : term => do pure a',
        ):
            self.assertIn(line, got)
        self.assertIn("open Lean in\nscoped macro", got)  # the `open … in` line stays in front of the command

    def test_what_is_scoped_or_local_already_and_what_only_looks_like_a_command_stay(self):
        src = (
            "namespace Lx\n"
            'scoped notation "a" => 1\n'
            'local notation "b" => 2\n'
            '-- notation "in a comment" => 3\n'
            '/- notation "in a block" => 4 -/\n'
            'def notation_name := "notation \\"x\\" => 5"\n'
            "macro_rules | `(a) => `(1)\n"
            "end Lx\n"
        )
        lib = self.make({"A.lean": src})
        r = self.run_pass(lib)
        self.assertEqual(self.text(lib, "A.lean"), src)
        self.assertEqual((r["scoped"], r["unscopable"]), ([], []))

    def test_a_second_pass_changes_nothing(self):
        lib = self.make(
            {"A.lean": 'namespace Lx\nnotation "q" => 1\nend Lx\n', "B.lean": "import Tengoku.Lx.A\n\ntheorem t : q = 1 := rfl\n"}
        )
        self.run_pass(lib)
        once = {p.name: p.read_text() for p in lib.glob("*.lean")}
        r = self.run_pass(lib)
        self.assertEqual({p.name: p.read_text() for p in lib.glob("*.lean")}, once)
        self.assertEqual((r["scoped"], r["reopened"], r["unscopable"]), ([], [], []))

    def test_a_dry_run_touches_nothing(self):
        lib = self.make({"A.lean": 'namespace Lx\nnotation "q" => 1\nend Lx\n'})
        r = self.run_pass(lib, write=False)
        self.assertEqual(len(r["scoped"]), 1)
        self.assertEqual(self.text(lib, "A.lean"), 'namespace Lx\nnotation "q" => 1\nend Lx\n')


class WhatTheGateReads(Library):
    """gitar/coderabbit on tengoku#615: the gate reads every occurrence of the keyword (Lean needs no line break between commands), so the pass must read the same places or stop"""

    def test_a_command_after_open_in_on_the_same_line_is_scoped_in_place(self):
        lib = self.make(
            {
                "A.lean": 'namespace Lx\nopen Nat in notation "ℓ" => 1\nset_option linter.all false in prefix:80 "~" => f\nend Lx\n',
                "B.lean": 'open Nat in notation "m" => 2\n',
            }
        )
        r = self.run_pass(lib)
        self.assertEqual(r["unscopable"], [])
        self.assertEqual(
            self.text(lib, "A.lean"),
            'namespace Lx\nopen Nat in scoped notation "ℓ" => 1\nset_option linter.all false in scoped prefix:80 "~" => f\nend Lx\n',
        )
        self.assertEqual(self.text(lib, "B.lean"), 'open Nat in local notation "m" => 2\n')

    def test_a_command_in_the_middle_of_a_line_stops_the_pass_instead_of_staying_global(self):
        for src in (
            'namespace Lx\ndef a := 1 prefix:80 "-" => f\nend Lx\n',
            'theorem t : True := trivial notation "q" => 1\n',
        ):
            lib = self.make({"A.lean": src})
            r = self.run_pass(lib)
            self.assertEqual(len(r["unscopable"]), 1, src)
            self.assertIn("a global command is left", r["unscopable"][0][1])

    def test_a_character_literal_with_a_quote_does_not_blank_the_rest_of_the_file(self):
        lib = self.make({"A.lean": 'def quote : Char := \'"\'\n\nnamespace Lx\nnotation "q" => 1\nend Lx\n'})
        r = self.run_pass(lib)
        self.assertEqual((len(r["scoped"]), r["unscopable"]), (1, []))
        self.assertIn('scoped notation "q"', self.text(lib, "A.lean"))

    def test_a_keyword_inside_an_escaped_name_or_a_string_is_not_a_command(self):
        lib = self.make({"A.lean": 'def «notation» := "notation \\"x\\" => 1"\n'})
        r = self.run_pass(lib)
        self.assertEqual((r["scoped"], r["unscopable"]), ([], []))


class SameFile(Library):
    def test_a_use_after_the_namespace_ends_gets_an_open_scoped_after_the_end(self):
        lib = self.make({"A.lean": 'namespace Lx\nnotation "q" => 1\nend Lx\n\ntheorem t : q = 1 := rfl\n'})
        r = self.run_pass(lib)
        self.assertEqual(
            self.text(lib, "A.lean"), 'namespace Lx\nscoped notation "q" => 1\nend Lx\nopen scoped Lx\n\ntheorem t : q = 1 := rfl\n'
        )
        self.assertEqual(len(r["reopened"]), 1)

    def test_a_use_in_a_namespace_entered_again_needs_nothing(self):
        src = 'namespace Lx\nnotation "q" => 1\nend Lx\n\nnamespace Lx\ntheorem t : q = 1 := rfl\nend Lx\n'
        lib = self.make({"A.lean": src})
        self.run_pass(lib)
        self.assertNotIn("open scoped", self.text(lib, "A.lean"))

    def test_a_root_command_used_after_its_section_ends_cannot_be_scoped(self):
        src = 'section\nnotation "q" => 1\nend\n\ntheorem t : q = 1 := rfl\n'
        lib = self.make({"A.lean": src})
        r = self.run_pass(lib)
        self.assertEqual(self.text(lib, "A.lean"), src)  # left as it is, and reported
        self.assertEqual(len(r["unscopable"]), 1)
        self.assertIn("used after its block ends", r["unscopable"][0][1])

    def test_a_use_after_the_end_in_a_namespace_of_the_seeded_tree_cannot_be_scoped(self):
        src = 'namespace Nat\nnotation "q" => 1\nend Nat\n\ntheorem t : q = 1 := rfl\n'
        lib = self.make({"A.lean": src})
        r = self.run_pass(lib, external={"Nat"})
        self.assertEqual(self.text(lib, "A.lean"), src)
        self.assertIn("seeded tree", r["unscopable"][0][1])

    def test_a_word_that_only_contains_the_atom_is_no_use(self):
        lib = self.make(
            {
                "A.lean": 'namespace Lx\nelab "resolve " a:term : term => do pure a\nend Lx\n\ndef resolved := 1\n/-- resolve it -/\ndef x := 2\n'
            }
        )
        r = self.run_pass(lib)
        self.assertEqual((len(r["scoped"]), r["reopened"], r["unscopable"]), (1, [], []))


class Importers(Library):
    DECL = 'namespace Lx\nnotation "q" => 1\nend Lx\n'

    def test_an_importer_inside_the_namespace_needs_nothing(self):
        lib = self.make({"A.lean": self.DECL, "B.lean": "import Tengoku.Lx.A\n\nnamespace Lx\ntheorem t : q = 1 := rfl\nend Lx\n"})
        r = self.run_pass(lib)
        self.assertEqual(self.text(lib, "B.lean"), "import Tengoku.Lx.A\n\nnamespace Lx\ntheorem t : q = 1 := rfl\nend Lx\n")
        self.assertEqual(r["unscopable"], [])

    def test_an_importer_outside_the_namespace_opens_it_right_after_its_imports_and_so_does_one_two_steps_away(self):
        lib = self.make(
            {
                "A.lean": self.DECL,
                "B.lean": "import Tengoku.Lx.A\n\ntheorem t : q = 1 := rfl\n",
                "C.lean": "import Mathlib\nimport Tengoku.Lx.B\n\ntheorem u : q = 1 := rfl\n",
            }
        )
        self.run_pass(lib)
        self.assertEqual(self.text(lib, "B.lean"), "import Tengoku.Lx.A\nopen scoped Lx\n\ntheorem t : q = 1 := rfl\n")
        self.assertEqual(self.text(lib, "C.lean"), "import Mathlib\nimport Tengoku.Lx.B\nopen scoped Lx\n\ntheorem u : q = 1 := rfl\n")

    def test_a_module_that_does_not_import_it_is_not_looked_at(self):
        lib = self.make({"A.lean": self.DECL, "B.lean": "theorem t : q = 1 := rfl\n"})
        r = self.run_pass(lib)
        self.assertEqual((self.text(lib, "B.lean"), r["unscopable"]), ("theorem t : q = 1 := rfl\n", []))

    def test_a_root_command_used_by_an_importer_cannot_be_scoped(self):
        lib = self.make({"A.lean": 'notation "q" => 1\n', "B.lean": "import Tengoku.Lx.A\n\ntheorem t : q = 1 := rfl\n"})
        r = self.run_pass(lib)
        self.assertEqual(self.text(lib, "A.lean"), 'notation "q" => 1\n')
        self.assertIn("root-level command", r["unscopable"][0][1])

    def test_an_importer_outside_a_namespace_of_the_seeded_tree_is_refused(self):
        lib = self.make(
            {"A.lean": 'namespace Set\nnotation "q" => 1\nend Set\n', "B.lean": "import Tengoku.Lx.A\n\ntheorem t : q = 1 := rfl\n"}
        )
        r = self.run_pass(lib, external={"Set"})
        self.assertEqual(len(r["unscopable"]), 1)
        self.assertNotIn("open scoped", self.text(lib, "B.lean"))


class Generator(unittest.TestCase):
    """through scripts/generate.py: the modules it writes come out scoped, and a command it cannot scope stops it"""

    def setUp(self):
        self.out = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.out)
        shutil.copytree(ROOT / "scripts", self.out / "scripts")
        (self.out / "schemas").mkdir()
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]}}})
        )
        (self.out / "Tengoku").mkdir()
        (self.out / "data" / "trusted").mkdir(parents=True)

    def generate(self, records):
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))
        return subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )

    def test_a_notation_in_a_prelude_block_comes_out_scoped_and_the_run_says_so(self):
        ctx = HEAD + prelude("Lx.A", 'namespace Lx\nnotation "q" => 1\nend Lx') + own("Lx/C.lean", 4, "namespace Lx")
        r = self.generate([rec("Lx.t", "Lx/C.lean", ctx, stmt="theorem t : q = 1")])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn('scoped notation "q" => 1', (self.out / "Tengoku/LibX/Deps/A.lean").read_text())
        self.assertIn("made scoped or local", r.stdout)

    def test_a_command_that_cannot_be_scoped_stops_the_generator_instead_of_leaking(self):
        ctx = HEAD + prelude("Lx.A", 'section\nnotation "q" => 1\nend\n\ndef u := q') + own("Lx/C.lean", 4, "")
        r = self.generate([rec("Lx.t", "Lx/C.lean", ctx)])
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("cannot be made scoped or local", r.stderr)
        self.assertIn("would leak", r.stderr + r.stdout)


if __name__ == "__main__":
    unittest.main()
