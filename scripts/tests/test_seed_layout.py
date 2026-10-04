"""scripts/seed.py writes the Seed layout: everything seeded under Tengoku/Seed/, `Tengoku.lean` still the tree's root. The table of mapped
roots is also what the earlier layout (topic folders straight under Tengoku/) is derived from."""

from __future__ import annotations

import json
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS))
import notices  # noqa: E402
import restructure  # noqa: E402
import seed  # noqa: E402

# the table before the Seed layout, spelled out: the earlier layout must keep mapping exactly so
OLD = {
    "mathlib": "Tengoku",
    "batteries": "Tengoku.Std",
    "aesop": "Tengoku.Tactic.Aesop",
    "Qq": "Tengoku.Meta.Qq",
    "proofwidgets": "Tengoku.Widgets",
    "plausible": "Tengoku.Testing.Random",
    "LeanSearchClient": "Tengoku.Search.LeanSearchClient",
    "importGraph": "Tengoku.Meta.ImportGraph",
    "Cli": "Tengoku.Meta.Cli",
}
REV = "0123456789abcdef0123"  # pragma: allowlist secret
NEW = {
    "mathlib": "Tengoku.Seed",
    "batteries": "Tengoku.Seed.Std",
    "aesop": "Tengoku.Seed.Tactic.Aesop",
    "Qq": "Tengoku.Seed.Meta.Qq",
    "proofwidgets": "Tengoku.Seed.Widgets",
    "plausible": "Tengoku.Seed.Testing.Random",
    "LeanSearchClient": "Tengoku.Seed.Search.LeanSearchClient",
    "importGraph": "Tengoku.Seed.Meta.ImportGraph",
    "Cli": "Tengoku.Seed.Meta.Cli",
}


def write(root: Path, rel: str, text: str) -> Path:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")
    return p


def roots(layout_seed: bool) -> list[tuple[str, str]]:
    return [(v[1], seed.in_layout(v[2], layout_seed)) for v in seed.PACKAGES.values()]


class Mapping(unittest.TestCase):
    def test_mapped_roots_are_the_seed_layout(self):
        self.assertEqual({k: v[2] for k, v in seed.PACKAGES.items()}, NEW)

    def test_the_earlier_layout_is_the_same_table_without_the_seed_folder(self):
        self.assertEqual({k: seed.in_layout(v[2], False) for k, v in seed.PACKAGES.items()}, OLD)

    def test_in_layout_only_renames_seed_modules(self):
        self.assertEqual(seed.in_layout("Tengoku.Seed", False), "Tengoku")
        self.assertEqual(seed.in_layout("Tengoku.Seed.Init", False), "Tengoku.Init")
        self.assertEqual(seed.in_layout("Tengoku.Seed.Init", True), "Tengoku.Seed.Init")
        for other in ("Tengoku", "Tengoku.SeedLib", "Tengoku.Lib.Seed", "Mathlib.Seed"):
            self.assertEqual(seed.in_layout(other, False), other)

    def test_a_package_root_maps_to_its_aggregator(self):
        self.assertEqual(seed.module_map("Mathlib", "Tengoku.Seed", "Mathlib"), "Tengoku")  # `import Mathlib` is `import Tengoku`
        self.assertEqual(seed.module_map("Mathlib", "Tengoku", "Mathlib"), "Tengoku")
        self.assertEqual(seed.module_map("Mathlib", "Tengoku.Seed", "Mathlib.Algebra.Group"), "Tengoku.Seed.Algebra.Group")
        self.assertEqual(seed.module_map("Batteries", "Tengoku.Seed.Std", "Batteries"), "Tengoku.Seed.Std")
        self.assertEqual(seed.module_map("Batteries", "Tengoku.Seed.Std", "Batteries.Data.List"), "Tengoku.Seed.Std.Data.List")
        self.assertIsNone(seed.module_map("Mathlib", "Tengoku.Seed", "MathlibExtras"))

    def test_imports_are_rewritten_for_either_layout(self):
        text = (
            "module\n\nimport Mathlib\npublic import Mathlib.Algebra.X\nmeta import Batteries.Data.List\nimport all Aesop\n"
            "import Qq.Macro\nimport Lean.Elab\nimport Init\n"
        )
        self.assertEqual(
            seed.rewrite_imports(text, roots(True)),
            "module\n\nimport Tengoku\npublic import Tengoku.Seed.Algebra.X\nmeta import Tengoku.Seed.Std.Data.List\n"
            "import all Tengoku.Seed.Tactic.Aesop\nimport Tengoku.Seed.Meta.Qq.Macro\nimport Lean.Elab\nimport Init\n",
        )
        self.assertEqual(
            seed.rewrite_imports(text, roots(False)),
            "module\n\nimport Tengoku\npublic import Tengoku.Algebra.X\nmeta import Tengoku.Std.Data.List\n"
            "import all Tengoku.Tactic.Aesop\nimport Tengoku.Meta.Qq.Macro\nimport Lean.Elab\nimport Init\n",
        )

    def test_the_layout_is_told_by_the_seed_folder(self):
        root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, root)
        self.assertFalse(seed.seed_layout(root))
        write(root, "Tengoku/Algebra/X.lean", "")
        self.assertFalse(seed.seed_layout(root))
        write(root, "Tengoku/Seed", "a file is not the folder")
        self.assertFalse(seed.seed_layout(root))
        (root / "Tengoku" / "Seed").unlink()
        write(root, "Tengoku/Seed/Algebra/X.lean", "")
        self.assertTrue(seed.seed_layout(root))

    def test_assets_sit_where_the_include_str_dots_lead(self):
        """`include_str` is relative to the including module's directory. ProofWidgets' paths stay inside the seed, where its js is; Mathlib's
        (upstream spelling below) climb out of Tengoku/Seed/ and gain a `..` (restructure.fix_include_str) to reach widget/ at the root."""
        cases = [
            ("proofwidgets", "Tengoku/Seed/Widgets/Component/Basic.lean", '".." / ".." / "widget" / "js" / "interactiveExpr.js"'),
            ("proofwidgets", "Tengoku/Seed/Widgets/Component/Panel/GoalTypePanel.lean", '".." / ".." / ".." / "widget" / "js" / "g.js"'),
            ("mathlib", "Tengoku/Seed/Tactic/Widget/CommDiag.lean", '".."/".."/".."/"widget"/"src"/"penrose"/"commutative.dsl"'),
        ]
        for pkg, module, path in cases:
            text = restructure.fix_include_str(f"def x := include_str {path}\n", module.count("/") - 2)
            comps = [c for lit in re.findall(r'"([^"]*)"', text) for c in lit.split("/")]
            asset = posixpath.normpath(posixpath.join(posixpath.dirname(module), *comps))
            self.assertTrue(any(asset.startswith(dst + "/") for _, dst in seed.ASSETS[pkg]), f"{asset} is outside {seed.ASSETS[pkg]}")


MATHLIB_WIDGET = 'module\n\nimport Mathlib.A\n\ndef dsl := include_str ".."/".."/".."/"widget"/"src"/"p.dsl"\n'
PROOFWIDGETS_JS = 'module\n\nimport ProofWidgets.A\n\ndef js := include_str ".." / ".." / "widget" / "js" / "a.js"\n'


def fake_packages(tmp: Path) -> Path:
    """.lake/packages of a fake environment: every package has a root file, A (imports B) and B; Mathlib also C, importing across."""
    pkgs = tmp / "proj" / ".lake" / "packages"
    manifest = {"packages": []}
    for pkg, (srcdir, root_mod, _mapped) in seed.PACKAGES.items():
        write(pkgs / pkg, f"{srcdir}.lean", f"module\n\npublic import {root_mod}.A\n")
        write(pkgs / pkg, f"{srcdir}/A.lean", f"/-\nCopyright (c) 2024 Someone.\n-/\nmodule\n\nimport {root_mod}.B\n")
        write(pkgs / pkg, f"{srcdir}/B.lean", "/-\nCopyright (c) 2024 Someone.\n-/\nmodule\n\nimport Init\n")
        manifest["packages"].append({"name": pkg, "url": f"https://github.com/example/{pkg}", "rev": REV})
    write(pkgs / "mathlib", "Mathlib/C.lean", "module\n\nimport Mathlib\nimport Batteries.Data.X\nimport Lean\n")
    write(pkgs / "batteries", "Batteries/Data/X.lean", "module\n\nimport Init\n")
    write(pkgs / "proofwidgets", "ProofWidgets/Demos/D.lean", "import ProofWidgets.A\n")
    # what reads assets at compile time: Mathlib's three levels up (the package root), ProofWidgets' two levels up (widget/js)
    write(pkgs / "mathlib", "Mathlib/Tactic/Widget/X.lean", MATHLIB_WIDGET)
    write(pkgs / "mathlib", "widget/src/p.dsl", "dsl")
    write(pkgs / "proofwidgets", "ProofWidgets/Component/Basic.lean", PROOFWIDGETS_JS)
    write(pkgs / "proofwidgets", "widget/js/a.js", "js")
    write(tmp / "proj", "lake-manifest.json", json.dumps(manifest))
    write(tmp / "proj", "lean-toolchain", "leanprover/lean4:v4.34.0-rc2\n")
    return pkgs


def run_seed(pkgs: Path, out: Path) -> str:
    r = subprocess.run([sys.executable, str(SCRIPTS / "seed.py"), "--from", str(pkgs), "--out", str(out)], capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    return r.stdout


class Seeding(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        self.out = self.tmp / "tree"
        # a tree in the earlier layout, as the last seed left it, with a subtree that is not seed
        write(self.out, "Tengoku/Std/Old.lean", "old")
        write(self.out, "Tengoku/Algebra/Old.lean", "old")
        write(self.out, "Tengoku/EquationalTheories/A.lean", "kept")
        write(self.out, "Tengoku.lean", "old root")
        self.log = run_seed(fake_packages(self.tmp), self.out)

    def lean(self, rel: str) -> str:
        return (self.out / rel).read_text(encoding="utf-8")

    def test_every_package_lands_under_its_mapped_root_in_the_seed_folder(self):
        for pkg, mapped in NEW.items():
            folder = self.out.joinpath(*mapped.split("."))
            self.assertTrue((folder / "A.lean").is_file(), f"{pkg}: {folder}")
            self.assertIn(f"import {mapped}.B", (folder / "A.lean").read_text(encoding="utf-8"))
        for pkg in ("batteries", "aesop", "Qq", "proofwidgets", "plausible", "LeanSearchClient", "importGraph", "Cli"):
            self.assertTrue(self.out.joinpath(*NEW[pkg].split(".")).with_suffix(".lean").is_file(), f"{pkg}: its root aggregator")

    def test_the_root_aggregator_stays_tengoku_lean(self):
        self.assertFalse((self.out / "Tengoku" / "Seed.lean").exists())  # Mathlib's root is the tree's root, not a module of the seed
        root = self.lean("Tengoku.lean")
        self.assertIn("public import Tengoku.Seed.A\n", root)  # Mathlib.lean's own import
        for pkg, mapped in NEW.items():
            if pkg != "mathlib":
                self.assertIn(f"public import {mapped}\n", root)
        self.assertEqual(root.count("Changed for Tengoku"), 1)

    def test_imports_between_packages_and_of_the_root_are_mapped(self):
        c = self.lean("Tengoku/Seed/C.lean")
        self.assertIn("import Tengoku\n", c)  # `import Mathlib`
        self.assertIn("import Tengoku.Seed.Std.Data.X\n", c)  # `import Batteries.Data.X`
        self.assertIn("import Lean\n", c)

    def test_nothing_of_the_earlier_layout_is_left_but_what_is_not_seed(self):
        self.assertFalse((self.out / "Tengoku" / "Std").exists())
        self.assertFalse((self.out / "Tengoku" / "Algebra").exists())
        self.assertEqual(self.lean("Tengoku/EquationalTheories/A.lean"), "kept")
        self.assertEqual(sorted(p.name for p in (self.out / "Tengoku").iterdir() if p.suffix == ".lean"), [])

    def test_assets_follow_their_modules(self):
        self.assertEqual(self.lean("Tengoku/Seed/widget/js/a.js"), "js")  # inside the seed, next to its reader
        self.assertEqual(self.lean("widget/src/p.dsl"), "dsl")  # Mathlib's stays at the repository root
        self.assertFalse((self.out / "Tengoku" / "widget").exists())

    def include_path(self, rel: str) -> list[str]:
        """The components of the one include_str path of a written module."""
        m = restructure.INCLUDE_STR.search(self.lean(rel))
        return [c for lit in re.findall(r'"([^"]*)"', m.group("path")) for c in lit.split("/")]

    def test_a_path_that_leaves_the_seed_gains_a_dot_dot(self):
        rel = "Tengoku/Seed/Tactic/Widget/X.lean"
        self.assertIn('include_str ".."/".."/".."/".."/"widget"/"src"/"p.dsl"', self.lean(rel))
        comps = self.include_path(rel)
        self.assertEqual(comps, ["..", "..", "..", "..", "widget", "src", "p.dsl"])
        self.assertEqual((self.out / rel).parent.joinpath(*comps).resolve(), (self.out / "widget" / "src" / "p.dsl").resolve())

    def test_a_path_that_stays_in_the_seed_is_unchanged(self):
        rel = "Tengoku/Seed/Widgets/Component/Basic.lean"
        self.assertIn('include_str ".." / ".." / "widget" / "js" / "a.js"', self.lean(rel))
        comps = self.include_path(rel)
        self.assertEqual(
            (self.out / rel).parent.joinpath(*comps).resolve(), (self.out / "Tengoku" / "Seed" / "widget" / "js" / "a.js").resolve()
        )

    def test_restructure_verify_finds_every_import_and_asset(self):
        self.assertEqual(restructure.verify(self.out), [])

    def test_the_demos_are_still_left_out(self):
        self.assertFalse((self.out / "Tengoku" / "Seed" / "Widgets" / "Demos").exists())

    def test_the_seed_notices_agree_with_the_cli(self):
        self.assertIn("copied from Batteries (example/batteries", self.lean("Tengoku/Seed/Std/A.lean"))
        self.assertEqual(notices.package_of("Tengoku.Seed.Std.A"), "batteries")
        for args in (["--check"], []):
            r = subprocess.run(
                [sys.executable, str(SCRIPTS / "notices.py"), "--root", str(self.out), *args], capture_output=True, text=True
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("seeded 31 files", self.log)

    def test_a_second_seed_changes_nothing(self):
        before = {p: p.read_bytes() for p in sorted(self.out.rglob("*")) if p.is_file()}
        run_seed(self.tmp / "proj" / ".lake" / "packages", self.out)
        self.assertEqual({p: p.read_bytes() for p in sorted(self.out.rglob("*")) if p.is_file()}, before)


def write_old_layout(pkgs: Path, out: Path) -> None:
    """What seed.py wrote before the Seed layout (the same steps, the earlier names): topic folders under Tengoku/, ProofWidgets' js at
    Tengoku/widget/js, Mathlib's widget/ at the root, Mathlib's root aggregator as Tengoku.lean with the other roots added."""
    manifest = {p["name"]: p for p in json.loads((pkgs.parent.parent / "lake-manifest.json").read_text())["packages"]}
    old_roots = roots(False)
    for pkg, (srcdir, _root_mod, mapped) in seed.PACKAGES.items():
        folder = Path(*seed.in_layout(mapped, False).split("."))
        pairs = [(f, folder / f.relative_to(pkgs / pkg / srcdir)) for f in (pkgs / pkg / srcdir).rglob("*.lean") if "Demos" not in f.parts]
        pairs.append((pkgs / pkg / f"{srcdir}.lean", folder.with_suffix(".lean")))
        for f, rel in pairs:
            original = f.read_text(encoding="utf-8")
            text = seed.rewrite_imports(original, old_roots)
            if text != original and rel != Path("Tengoku.lean"):
                text = notices.stamp(text, notices.notice(pkg, manifest[pkg]["url"], manifest[pkg]["rev"], notices.describe(True, False)))
            write(out, rel.as_posix(), text)
    lines = (out / "Tengoku.lean").read_text(encoding="utf-8").rstrip("\n").split("\n")
    extra = [f"public import {seed.in_layout(v[2], False)}" for k, v in seed.PACKAGES.items() if k != "mathlib"]
    last = max(i for i, ln in enumerate(lines) if seed.IMPORT_RE.match(ln))
    header = [
        "-- Tengoku: one self-contained tree. This file imports all of it.",
        "-- Seeded from the packages listed in SEED.md; grown by verified translations.",
    ]
    root = notices.stamp(
        "\n".join(header + lines[: last + 1] + extra + lines[last + 1 :]) + "\n",
        notices.notice("mathlib", manifest["mathlib"]["url"], manifest["mathlib"]["rev"], notices.ROOT_CHANGE),
    )
    write(out, "Tengoku.lean", root)
    shutil.copytree(pkgs / "proofwidgets" / "widget" / "js", out / "Tengoku" / "widget" / "js")
    shutil.copytree(pkgs / "mathlib" / "widget", out / "widget")


def tree_files(root: Path) -> dict[str, str]:
    """Every file seed.py or restructure.py touches, by path: Tengoku.lean, Tengoku/ and the root widget/."""
    paths = [root / "Tengoku.lean"] + [p for d in ("Tengoku", "widget") for p in sorted((root / d).rglob("*")) if p.is_file()]
    return {p.relative_to(root).as_posix(): p.read_text(encoding="utf-8") for p in paths}


class AgreesWithRestructure(unittest.TestCase):
    def test_seeding_equals_the_old_layout_restructured(self):
        """The tree seed.py writes is the tree restructure.py makes of the earlier layout of the same packages."""
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        pkgs = fake_packages(tmp)
        seeded, moved = tmp / "seeded", tmp / "moved"
        seeded.mkdir()
        moved.mkdir()
        run_seed(pkgs, seeded)
        write_old_layout(pkgs, moved)
        self.assertGreater(restructure.apply(moved, set())["moved top-level entries"], 0)
        self.assertEqual(restructure.verify(moved), [])
        self.assertEqual(tree_files(seeded), tree_files(moved))


if __name__ == "__main__":
    unittest.main()
