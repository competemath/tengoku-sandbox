"""A module whose file name is not a plain identifier (`A-B.lean`, `1102.4662.lean`) is written in guillemets wherever Lean names it: `Tengoku.Lib.«A-B»`. The factory spells the
manifest, the umbrella and the imports that way (scripts/bump/bundle_layers.py, 2026-10-09: tao-analysis could not be cut), and the gates read module names from paths with
`replace("/", ".")`, so such a module was `Tengoku.Lib.A-B` to them: an import that did not resolve, a manifest module that was 'not a file of this PR'. Its own file, like test_extend.py."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import _git  # noqa: E402
import test_extend as ex  # noqa: E402  (the module, not its test class: importing the class would run its tests again here)
from test_gates import Repo  # noqa: E402


class Names(unittest.TestCase):
    def test_a_component_that_is_not_an_identifier_goes_in_guillemets(self):
        self.assertEqual(_git.module_name("Tengoku/Lib/Basic"), "Tengoku.Lib.Basic")
        self.assertEqual(_git.module_name("Tengoku/Lib/A-B"), "Tengoku.Lib.«A-B»")
        self.assertEqual(_git.module_name("Tengoku/Tao/1102.4662"), "Tengoku.Tao.«1102.4662»")
        self.assertEqual(_git.module_name("Tengoku/Lib/Foo'"), "Tengoku.Lib.Foo'")

    def test_the_file_of_a_module_is_found_again_and_a_dot_inside_guillemets_is_not_a_separator(self):
        for stem in ("Tengoku/Lib/Basic", "Tengoku/Lib/A-B", "Tengoku/Tao/1102.4662"):
            self.assertEqual(_git.module_stem(_git.module_name(stem)), stem)
        self.assertEqual(_git.module_stem("Tengoku.Tao.«1102.4662».Sub"), "Tengoku/Tao/1102.4662/Sub")


class ImportsResolve(unittest.TestCase):
    def test_an_import_of_a_guillemet_module_resolves(self):
        r = Repo()
        r.write("Tengoku/Lib/A-B.lean", "import Tengoku.Logic.Basic\n\ntheorem ab : True := trivial\n")
        r.write("Tengoku/Lib/Use.lean", "import Tengoku.Lib.«A-B»\n\ntheorem use : True := trivial\n")
        r.commit("a module with a dash and its importer")
        rc, out = r.gate("imports_resolve.py")
        self.assertEqual(rc, 0, out)

    def test_an_import_of_a_module_that_is_not_there_still_fails(self):
        r = Repo()
        r.write("Tengoku/Lib/Use.lean", "import Tengoku.Lib.«A-B»\n\ntheorem use : True := trivial\n")
        r.commit("an importer of nothing")
        rc, out = r.gate("imports_resolve.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("A-B", out)


class IntakeCheck(unittest.TestCase):
    B = "Tengoku.FxLib.Fx.«B-C»"

    def test_a_manifest_names_a_guillemet_module_and_the_part_adds_exactly_its_import(self):
        r = ex.Extend().repo()
        r.write("Tengoku/FxLib/Fx/B-C.lean", ex.module("b", f"import {ex.Extend.A}\n"))
        r.write("Tengoku/FxLib.lean", f"import {ex.Extend.A}\nimport {self.B}\n")
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
        r.write("data/intake/fx-lib/manifest.jsonl", old + ex.record("b", self.B))
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2}) + "\n")
        r.commit("part 2 with a dash in a module name")
        rc, out = r.gate("intake_check.py", "main", "pr")
        self.assertEqual(rc, 0, out)
        self.assertIn("extend ok: fx-lib: part 002, 1 modules, 1 theorems", out)

    def test_a_manifest_module_that_is_not_a_file_is_still_refused(self):
        r = ex.Extend().repo()
        r.write("Tengoku/FxLib/Fx/B-C.lean", ex.module("b", f"import {ex.Extend.A}\n"))
        r.write("Tengoku/FxLib.lean", f"import {ex.Extend.A}\nimport {self.B}\n")
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
        r.write("data/intake/fx-lib/manifest.jsonl", old + ex.record("b", "Tengoku.FxLib.Fx.«B-D»"))
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2}) + "\n")
        r.commit("part 2, manifest names another module")
        rc, out = r.gate("intake_check.py", "main", "pr")
        self.assertNotEqual(rc, 0)
        self.assertIn("is not a file of this PR", out)


if __name__ == "__main__":
    unittest.main()
