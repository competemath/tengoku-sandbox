import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS))
import notices  # noqa: E402

HEADER = """/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Tengoku.Logic.Basic

/-! # Groups -/
"""
LINE = notices.notice(
    "mathlib",
    "https://github.com/leanprover-community/mathlib4.git",
    "85e3a25e006c35636f0e53b0e9296caca2685bc0",  # pragma: allowlist secret
    "import paths rewritten",
)


class Stamp(unittest.TestCase):
    def test_notice_line(self):
        self.assertEqual(
            LINE, "Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten."
        )

    def test_goes_at_the_end_of_the_licence_header_and_touches_nothing_else(self):
        out = notices.stamp(HEADER, LINE)
        before, after = HEADER.split("\n"), out.split("\n")
        self.assertEqual(after[4], LINE)
        self.assertEqual(after[5], "-/")
        self.assertEqual(before, after[:4] + after[5:])  # only one line added, credit lines untouched

    def test_idempotent(self):
        once = notices.stamp(HEADER, LINE)
        self.assertEqual(notices.stamp(once, LINE), once)

    def test_replaces_a_stale_notice(self):
        once = notices.stamp(HEADER, LINE)
        other = LINE.replace("import paths rewritten", "import paths rewritten, and more")
        self.assertEqual(notices.stamp(once, other).count("Changed for Tengoku"), 1)
        self.assertIn(other, notices.stamp(once, other))

    def test_headerless_file_gets_a_block_of_its_own(self):
        text = "module\n\npublic import Tengoku.Meta.Qq.Macro\n"
        self.assertEqual(notices.stamp(text, LINE), f"/-\n{LINE}\n-/\n" + text)

    def test_never_written_into_a_module_docstring(self):
        text = "/-! # Qq\nQuoting. -/\nimport Tengoku.Meta.Qq.Macro\n"
        self.assertTrue(notices.stamp(text, LINE).startswith(f"/-\n{LINE}\n-/\n/-!"))

    def test_one_line_comment_is_not_opened(self):
        text = "/- Copyright (c) 2024 X. -/\nimport Tengoku.A\n"
        self.assertTrue(notices.stamp(text, LINE).startswith(f"/-\n{LINE}\n-/\n/- Copyright"))

    def test_a_comment_that_is_not_a_licence_header_is_left_alone(self):
        text = "/-\nTODO: tidy\n-/\nimport Tengoku.A\n"
        self.assertTrue(notices.stamp(text, LINE).startswith(f"/-\n{LINE}\n-/\n/-\nTODO"))

    def test_notice_can_never_open_or_close_a_comment(self):
        with self.assertRaises(AssertionError):
            notices.notice("mathlib", "x", "y", "a -/ b")

    def test_describe(self):
        self.assertEqual(notices.describe(False, False), "")
        self.assertEqual(notices.describe(True, True), "import paths rewritten, instance-name suffix `_mathlib` renamed `_tengoku`")


def write(root: Path, rel: str, text: str) -> Path:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    return p


class Tree(unittest.TestCase):
    """The CLI over a small tree: changed seeded files are stamped, everything else is not."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        r = self.root
        write(
            r,
            "SEED.md",
            "| package | origin | rev | mapped to |\n|---|---|---|---|\n"
            "| mathlib | https://github.com/leanprover-community/mathlib4.git | 85e3a25e006c35636f0e53b0e9296caca2685bc0 | `Tengoku` |\n"  # pragma: allowlist secret
            "| batteries | https://github.com/leanprover-community/batteries | d54dddc581e08be364c278052863524bff7a99a9 | `Tengoku.Std` |\n",  # pragma: allowlist secret
        )
        write(r, "data/trusted/equational-theories.jsonl", "{}\n")
        self.root_file = write(
            r,
            "Tengoku.lean",
            "-- Tengoku: one self-contained tree.\nmodule\n\npublic import Tengoku.Algebra.X\npublic import Tengoku.Std\n",
        )
        self.algebra = write(r, "Tengoku/Algebra/X.lean", HEADER)
        self.std = write(r, "Tengoku/Std/Z.lean", "module\n\npublic import Tengoku.Std.Y\n")
        self.plain = write(r, "Tengoku/Data/Plain.lean", "/-\nCopyright (c) 2020 A.\n-/\nmodule\n\nimport Init\n")
        self.kept = write(r, "Tengoku/EquationalTheories/A.lean", "import Tengoku\n")
        self.all = write(r, "Tengoku/All.lean", "import Tengoku\n")

    def run_cli(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPTS / "notices.py"), "--root", str(self.root), *args], capture_output=True, text=True
        )

    def test_check_then_stamp_then_check(self):
        before = self.run_cli("--check")
        self.assertEqual(before.returncode, 1)
        self.assertIn("3 changed seeded files without a notice", before.stdout)
        self.assertEqual(self.run_cli().returncode, 0)
        self.assertEqual(self.run_cli("--check").returncode, 0, self.run_cli("--check").stdout)
        self.assertIn("stamped 0 files", self.run_cli().stdout)  # idempotent

    def test_provenance_and_scope(self):
        self.run_cli()
        self.assertIn(
            "copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.", self.algebra.read_text()
        )
        self.assertIn("copied from Batteries (leanprover-community/batteries at d54dddc581e0)", self.std.read_text())
        self.assertIn(notices.ROOT_CHANGE, self.root_file.read_text())
        self.assertNotIn("Changed for Tengoku", self.plain.read_text())  # copied byte for byte
        self.assertNotIn("Changed for Tengoku", self.kept.read_text())  # not seed
        self.assertNotIn("Changed for Tengoku", self.all.read_text())  # generated


class SeedStamps(unittest.TestCase):
    """scripts/seed.py over fake packages writes the notices itself (and the Seed layout), so a re-seed keeps them."""

    def test_reseed(self):
        sys.path.insert(0, str(SCRIPTS))
        import seed

        tmp = Path(tempfile.mkdtemp())
        pkgs = tmp / "proj" / ".lake" / "packages"
        manifest = {"packages": []}
        for pkg, (srcdir, root_mod, _mapped) in seed.PACKAGES.items():
            write(pkgs / pkg, f"{srcdir}.lean", f"module\n\npublic import {root_mod}.A\n")
            write(
                pkgs / pkg,
                f"{srcdir}/A.lean",
                f"/-\nCopyright (c) 2024 Someone.\nReleased under Apache 2.0 license.\n-/\nmodule\n\nimport {root_mod}.B\n",
            )
            write(pkgs / pkg, f"{srcdir}/B.lean", "/-\nCopyright (c) 2024 Someone.\n-/\nmodule\n\nimport Init\n")
            manifest["packages"].append(
                {"name": pkg, "url": f"https://github.com/example/{pkg}", "rev": "0123456789abcdef0123"}  # pragma: allowlist secret
            )
        write(tmp / "proj", "lake-manifest.json", json.dumps(manifest))
        write(tmp / "proj", "lean-toolchain", "leanprover/lean4:v4.34.0-rc2\n")
        out = tmp / "tree"
        out.mkdir()
        r = subprocess.run(
            [sys.executable, str(SCRIPTS / "seed.py"), "--from", str(pkgs), "--out", str(out)], capture_output=True, text=True
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        a = out / "Tengoku" / "Seed" / "A.lean"
        self.assertIn("Changed for Tengoku: copied from Mathlib (example/mathlib at 0123456789ab); import paths rewritten.", a.read_text())
        self.assertTrue(
            a.read_text().startswith("/-\nCopyright (c) 2024 Someone.\nReleased under Apache 2.0 license.\nChanged for Tengoku")
        )
        self.assertNotIn("Changed for Tengoku", (out / "Tengoku" / "Seed" / "B.lean").read_text())  # unchanged by the seed
        root = (out / "Tengoku.lean").read_text()
        self.assertEqual(root.count("Changed for Tengoku"), 1)
        self.assertIn(notices.ROOT_CHANGE, root)
        self.assertIn("copied from Batteries (example/batteries", (out / "Tengoku" / "Seed" / "Std" / "A.lean").read_text())
        # the CLI agrees with what the seed wrote
        c = subprocess.run([sys.executable, str(SCRIPTS / "notices.py"), "--root", str(out), "--check"], capture_output=True, text=True)
        self.assertEqual(c.returncode, 0, c.stdout)


class SeedLayoutTree(Tree):
    """The notices CLI over the tree after the seed moved under Tengoku/Seed/: the same notices, the same scope."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        r = self.root
        write(
            r,
            "SEED.md",
            "| package | origin | rev | mapped to |\n|---|---|---|---|\n"
            "| mathlib | https://github.com/leanprover-community/mathlib4.git | 85e3a25e006c35636f0e53b0e9296caca2685bc0 | `Tengoku.Seed` |\n"  # pragma: allowlist secret
            "| batteries | https://github.com/leanprover-community/batteries | d54dddc581e08be364c278052863524bff7a99a9 | `Tengoku.Seed.Std` |\n",  # pragma: allowlist secret
        )
        write(r, "data/trusted/equational-theories.jsonl", "{}\n")
        self.root_file = write(
            r,
            "Tengoku.lean",
            "-- Tengoku: one self-contained tree.\nmodule\n\npublic import Tengoku.Seed.Algebra.X\npublic import Tengoku.Seed.Std\n",
        )
        self.algebra = write(r, "Tengoku/Seed/Algebra/X.lean", HEADER.replace("Tengoku.Logic", "Tengoku.Seed.Logic"))
        self.std = write(r, "Tengoku/Seed/Std/Z.lean", "module\n\npublic import Tengoku.Seed.Std.Y\n")
        self.plain = write(r, "Tengoku/Seed/Data/Plain.lean", "/-\nCopyright (c) 2020 A.\n-/\nmodule\n\nimport Init\n")
        self.kept = write(r, "Tengoku/EquationalTheories/A.lean", "import Tengoku\n")
        self.all = write(r, "Tengoku/All.lean", "import Tengoku\n")

    def test_only_the_seed_folder_and_the_root_are_seeded(self):
        stray = write(self.root, "Tengoku/Stray/B.lean", "import Tengoku.Seed.Algebra.X\n")  # neither seed nor a registered library
        self.assertEqual(
            sorted(p.relative_to(self.root).as_posix() for p in notices.seeded_files(self.root)),
            ["Tengoku.lean", "Tengoku/Seed/Algebra/X.lean", "Tengoku/Seed/Data/Plain.lean", "Tengoku/Seed/Std/Z.lean"],
        )
        self.run_cli()
        self.assertNotIn("Changed for Tengoku", stray.read_text())

    def test_the_notice_names_the_package_of_the_module(self):
        self.run_cli()
        self.assertIn("copied from Mathlib", self.algebra.read_text())
        self.assertIn("copied from Batteries", self.std.read_text())


class PackageOf(unittest.TestCase):
    TABLE = [
        ("Tengoku", "Tengoku", "mathlib"),
        ("Tengoku.Algebra.X", "Tengoku.Seed.Algebra.X", "mathlib"),
        ("Tengoku.Tactic.Simp", "Tengoku.Seed.Tactic.Simp", "mathlib"),
        ("Tengoku.Meta.Other", "Tengoku.Seed.Meta.Other", "mathlib"),
        ("Tengoku.Std", "Tengoku.Seed.Std", "batteries"),
        ("Tengoku.Std.Data.List", "Tengoku.Seed.Std.Data.List", "batteries"),
        ("Tengoku.Tactic.Aesop.Foo", "Tengoku.Seed.Tactic.Aesop.Foo", "aesop"),
        ("Tengoku.Meta.Qq.Macro", "Tengoku.Seed.Meta.Qq.Macro", "Qq"),
        ("Tengoku.Widgets.Component.Basic", "Tengoku.Seed.Widgets.Component.Basic", "proofwidgets"),
        ("Tengoku.Testing.Random.Gen", "Tengoku.Seed.Testing.Random.Gen", "plausible"),
        ("Tengoku.Search.LeanSearchClient", "Tengoku.Seed.Search.LeanSearchClient", "LeanSearchClient"),
        ("Tengoku.Meta.ImportGraph.Main", "Tengoku.Seed.Meta.ImportGraph.Main", "importGraph"),
        ("Tengoku.Meta.Cli", "Tengoku.Seed.Meta.Cli", "Cli"),
    ]

    def test_either_layout_finds_the_package(self):
        for old, new, pkg in self.TABLE:
            self.assertEqual(notices.package_of(old), pkg, old)
            self.assertEqual(notices.package_of(new), pkg, new)


if __name__ == "__main__":
    unittest.main()
