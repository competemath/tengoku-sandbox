"""The seed move: only imports and include_str paths change, a second run changes nothing, and what it breaks is found by `verify`."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("restructure", ROOT / "scripts" / "restructure.py")
restructure = importlib.util.module_from_spec(spec)
sys.modules["restructure"] = restructure
spec.loader.exec_module(restructure)

ROOT_LEAN = "/-\nChanged for Tengoku: x.\n-/\nmodule  -- shake: keep-all\n\npublic import Std\npublic import Tengoku.Std\npublic import Tengoku.Logic.Basic\n"
LIB_HEADER = (
    "module\n\npublic import Tengoku\npublic import Tengoku.Std\npublic import Tengoku.Tactic.Aesop\npublic import Tengoku.Meta.Qq\n"
)
SEED_MD = "| mathlib | https://x | abc | `Tengoku` |\n| batteries | https://y | def | `Tengoku.Std` |\n| aesop | https://z | 123 | `Tengoku.Tactic.Aesop` |\n"
THIRD = "the aggregator modules (`Tengoku/Std.lean` and the like) are generated.\n| Batteries | u | Apache-2.0 | `Tengoku/Std/` |\n| ProofWidgets | u | Apache-2.0 | `Tengoku/Widgets/`, `widget/` |\n"
FILES = {
    "Tengoku.lean": ROOT_LEAN,
    "Tengoku/Std.lean": "module\n\npublic import Tengoku.Std.Data\n",
    "Tengoku/Std/Data.lean": "module\n\npublic import Init.Data.List\npublic import Tengoku.Logic.Basic\n\n-- import Tengoku.Std.Data in prose\n",
    "Tengoku/Logic/Basic.lean": "/- c -/\nimport Tengoku.Tactic\n",
    "Tengoku/Tactic.lean": "import Tengoku.Widgets\n",
    "Tengoku/Tactic/Aesop.lean": "module\n",
    "Tengoku/Meta/Qq.lean": "module\n",
    "Tengoku/Widgets.lean": "import Tengoku.Widgets.Component\n",
    "Tengoku/Widgets/Component.lean": 'import Lean\n\ndef js := include_str ".." / "widget" / "js" / "a.js"\n',
    "Tengoku/Tactic/Widget/Diag.lean": 'import Tengoku.Widgets\n\ndef a := include_str ".."/".."/".."/"widget"/"src"/"p.dsl"\ndef b := include_str "../../../widget/src/p.sub"\n'
    '-- include_str ".."/".."/".."/"nothing"\n',
    "Tengoku/widget/js/a.js": "// js\n",
    "widget/src/p.dsl": "dsl\n",
    "widget/src/p.sub": "sub\n",
    "Tengoku/Lib.lean": "import Tengoku.Lib.Basic\n",
    "Tengoku/Lib/Basic.lean": LIB_HEADER + "\ntheorem t : 1 = 1 := rfl\n",
    "Tengoku/Lib/Deep.lean": "module\n\npublic import Tengoku.Std.Data\npublic import Tengoku.Lib.Basic\n",
    "Tengoku/Lib/NoRoot.lean": "module\n\npublic import Tengoku.Std\npublic import Tengoku.Lib.Basic\n",
    "Tengoku/All.lean": "import Tengoku\nimport Tengoku.Lib\n",
    "SEED.md": SEED_MD,
    "LICENSE-THIRD-PARTY.md": THIRD,
    "data/trusted/lib.jsonl": "",
}


def tree(files: dict[str, str] | None = None) -> Path:
    d = Path(tempfile.mkdtemp())
    for rel, text in (files or FILES).items():
        p = d / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "w", encoding="utf-8", newline="") as f:
            f.write(text)
    return d


def read(d: Path, rel: str) -> str:
    with open(d / rel, encoding="utf-8", newline="") as f:
        return f.read()


class Libraries(unittest.TestCase):
    def test_names_come_from_files_folders_and_intake(self):
        paths = [
            "data/trusted/a-b.jsonl",
            "data/staging/c/x.jsonl",
            "data/tentative/d.jsonl",
            "data/intake/e/manifest.jsonl",
            "data/stats.json",
            "Tengoku/Z.lean",
        ]
        self.assertEqual(restructure.libs_from_paths(paths), {"a-b", "c", "d", "e"})

    def test_a_library_named_after_the_new_folders_is_refused(self):
        with self.assertRaises(SystemExit):
            restructure.apply(tree(), {"seed"})
        with self.assertRaises(SystemExit):
            restructure.apply(tree(), {"native"})


class Headers(unittest.TestCase):
    def test_header_ends_at_the_first_command_and_knows_module_with_a_comment(self):
        lines = ROOT_LEAN.split("\n") + ["theorem x : 1 = 1 := rfl", "import Tengoku.Std"]
        self.assertEqual(restructure.header_end(lines), len(ROOT_LEAN.split("\n")))

    def test_nested_block_comments_in_the_header(self):
        lines = ["/- a /- b -/ still a comment", "import Tengoku.Std", "-/", "import Tengoku.Logic.Basic", "def x := 1"]
        self.assertEqual(restructure.header_end(lines), 4)

    def test_only_seeded_modules_are_renamed(self):
        roots = {"Std", "Logic"}
        for mod, new in [
            ("Tengoku", "Tengoku"),
            ("Tengoku.Std", "Tengoku.Seed.Std"),
            ("Tengoku.Lib.Basic", "Tengoku.Lib.Basic"),
            ("Init.Data", "Init.Data"),
        ]:
            self.assertEqual(restructure.rename_import(mod, roots), new)
        self.assertEqual(restructure.rename_import("Tengoku.Logic.Basic", roots), "Tengoku.Seed.Logic.Basic")

    def test_modifiers_comments_and_line_endings_are_kept(self):
        text = "module\r\n\r\npublic meta import Tengoku.Std  -- why\r\nimport all Tengoku.Std.X\r\nprivate import Tengoku.Lib\r\n\r\ntheorem t : 1 = 1 := rfl\r\n"
        out = restructure.rewrite_header(text, restructure.seeded_name({"Std"}))
        self.assertEqual(
            out,
            "module\r\n\r\npublic meta import Tengoku.Seed.Std  -- why\r\nimport all Tengoku.Seed.Std.X\r\nprivate import Tengoku.Lib\r\n\r\ntheorem t : 1 = 1 := rfl\r\n",
        )

    def test_imports_below_the_header_are_not_touched(self):
        text = "import Tengoku.Std\n\n/-- doc\nimport Tengoku.Std.X\n-/\ndef x := 1\n"
        self.assertEqual(
            restructure.rewrite_header(text, restructure.seeded_name({"Std"})),
            text.replace("import Tengoku.Std\n", "import Tengoku.Seed.Std\n", 1),
        )

    def test_a_library_drops_what_the_root_already_exports(self):
        name = restructure.library_name({"Std", "Tactic", "Meta", "Logic"})
        self.assertIsNone(name("Tengoku.Std", ["Tengoku", "Tengoku.Std"]))
        self.assertEqual(name("Tengoku.Std", ["Tengoku.Std"]), "Tengoku.Seed.Std")  # no root import: renamed, not dropped
        self.assertEqual(
            name("Tengoku.Std.Data.Vector", ["Tengoku"]), "Tengoku.Seed.Std.Data.Vector"
        )  # a specific module is not an umbrella
        self.assertEqual(name("Tengoku", ["Tengoku"]), "Tengoku")


class IncludeStr(unittest.TestCase):
    def test_a_path_that_leaves_the_tree_gains_one_level(self):
        text = 'def a := include_str ".."/".."/".."/"widget"/"x"\n'
        self.assertEqual(restructure.fix_include_str(text, 2), 'def a := include_str ".."/".."/".."/".."/"widget"/"x"\n')
        self.assertEqual(
            restructure.fix_include_str('x include_str ".." / ".." / ".." / "w"\n', 2), 'x include_str ".." / ".." / ".." / ".." / "w"\n'
        )
        self.assertEqual(restructure.fix_include_str('x include_str "../../../w/x"\n', 2), 'x include_str "../../../../w/x"\n')

    def test_a_path_inside_the_tree_and_comments_stay(self):
        for text, depth in [
            ('x include_str ".." / ".." / "widget"\n', 2),
            ('-- include_str ".."/".."/".."/"w"\n', 2),
            ('x include_str "a.txt"\n', 0),
        ]:
            self.assertEqual(restructure.fix_include_str(text, depth), text)


class Apply(unittest.TestCase):
    def run_apply(self):
        d = tree()
        done = restructure.apply(d, restructure.libs_from_tree(d))
        return d, done

    def test_seeded_files_move_and_their_imports_follow(self):
        d, done = self.run_apply()
        self.assertEqual(done["moved top-level entries"], 9)
        self.assertEqual(
            read(d, "Tengoku/Seed/Std/Data.lean"), FILES["Tengoku/Std/Data.lean"].replace("Tengoku.Logic.Basic", "Tengoku.Seed.Logic.Basic")
        )
        self.assertEqual(read(d, "Tengoku/Seed/Logic/Basic.lean"), "/- c -/\nimport Tengoku.Seed.Tactic\n")
        self.assertEqual(read(d, "Tengoku/Seed/widget/js/a.js"), "// js\n")
        self.assertFalse((d / "Tengoku" / "Std").exists())

    def test_include_str_follows_the_move_only_where_it_leaves_the_tree(self):
        d, _ = self.run_apply()
        self.assertEqual(read(d, "Tengoku/Seed/Widgets/Component.lean"), FILES["Tengoku/Widgets/Component.lean"])
        diag = read(d, "Tengoku/Seed/Tactic/Widget/Diag.lean")
        self.assertIn('include_str ".."/".."/".."/".."/"widget"/"src"/"p.dsl"', diag)
        self.assertIn('include_str "../../../../widget/src/p.sub"', diag)
        self.assertIn('-- include_str ".."/".."/".."/"nothing"', diag)

    def test_the_root_the_documents_and_the_libraries(self):
        d, _ = self.run_apply()
        self.assertEqual(
            read(d, "Tengoku.lean"), ROOT_LEAN.replace("Tengoku.Std", "Tengoku.Seed.Std").replace("Tengoku.Logic", "Tengoku.Seed.Logic")
        )
        self.assertEqual(read(d, "Tengoku/Lib/Basic.lean"), "module\n\npublic import Tengoku\n\ntheorem t : 1 = 1 := rfl\n")
        self.assertEqual(
            read(d, "Tengoku/Lib/Deep.lean"), "module\n\npublic import Tengoku.Seed.Std.Data\npublic import Tengoku.Lib.Basic\n"
        )
        self.assertEqual(read(d, "Tengoku/Lib/NoRoot.lean"), "module\n\npublic import Tengoku.Seed.Std\npublic import Tengoku.Lib.Basic\n")
        self.assertEqual(read(d, "Tengoku/Lib.lean"), FILES["Tengoku/Lib.lean"])
        self.assertEqual(read(d, "Tengoku/All.lean"), FILES["Tengoku/All.lean"])
        self.assertEqual(
            read(d, "SEED.md"),
            "| mathlib | https://x | abc | `Tengoku.Seed` |\n| batteries | https://y | def | `Tengoku.Seed.Std` |\n| aesop | https://z | 123 | `Tengoku.Seed.Tactic.Aesop` |\n",
        )
        self.assertIn("`Tengoku/Seed/Std.lean` and the like", read(d, "LICENSE-THIRD-PARTY.md"))
        self.assertIn("`Tengoku/Seed/Std/`", read(d, "LICENSE-THIRD-PARTY.md"))
        self.assertIn("`Tengoku/Seed/Widgets/`, `widget/`", read(d, "LICENSE-THIRD-PARTY.md"))

    def test_a_second_run_changes_nothing_and_the_result_resolves(self):
        d, _ = self.run_apply()
        before = {p: read(d, p.relative_to(d).as_posix()) for p in sorted(d.rglob("*")) if p.is_file()}
        self.assertEqual(restructure.apply(d, restructure.libs_from_tree(d)), {})
        self.assertEqual(before, {p: read(d, p.relative_to(d).as_posix()) for p in sorted(d.rglob("*")) if p.is_file()})
        self.assertEqual(restructure.verify(d), [])

    def test_the_tree_before_the_move_resolves_too(self):
        self.assertEqual(restructure.verify(tree()), [])


class Verify(unittest.TestCase):
    def test_a_dangling_import_and_a_missing_include_are_found(self):
        d, _ = Apply().run_apply()
        with open(d / "Tengoku/Seed/Logic/Basic.lean", "a", encoding="utf-8") as f:
            f.write("")
        (d / "Tengoku/Seed/Logic/Basic.lean").write_text("import Tengoku.Std\n", encoding="utf-8")  # the old name: no longer a module
        (d / "widget/src/p.dsl").unlink()
        errors = restructure.verify(d)
        self.assertTrue(any("import Tengoku.Std resolves to no module" in e for e in errors), errors)
        self.assertTrue(any("p.dsl" in e and "resolves to no file" in e for e in errors), errors)

    def test_command_line(self):
        d = tree()
        self.assertEqual(restructure.main(["apply", "--root", str(d), "--libs", "lib"]), 0)
        self.assertEqual(restructure.main(["verify", "--root", str(d)]), 0)
        self.assertEqual(restructure.main(["apply", "--root", str(d), "--libs", "lib"]), 0)
        (d / "widget/src/p.sub").unlink()
        self.assertEqual(restructure.main(["verify", "--root", str(d)]), 1)


if __name__ == "__main__":
    unittest.main()
