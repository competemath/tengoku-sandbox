"""A module whose file name is not a plain identifier (`A-B.lean`, `1102.4662.lean`) is written in guillemets wherever Lean names it: `Tengoku.Lib.«A-B»`. The factory spells the
manifest, the umbrella and the imports that way (scripts/bump/bundle_layers.py, 2026-10-09: tao-analysis could not be cut), and the gates read module names from paths with
`replace("/", ".")`, so such a module was `Tengoku.Lib.A-B` to them: an import that did not resolve, a manifest module that was 'not a file of this PR'. Its own file, like test_extend.py."""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
TREE = HERE.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(TREE / "scripts"))
sys.path.insert(0, str(TREE / "scripts" / "tests"))
_tempdir = tempfile.tempdir
import _git  # noqa: E402
import autotag  # noqa: E402
import isnad  # noqa: E402
import isnad_sweep  # noqa: E402
import lake_cache  # noqa: E402
import tag_check  # noqa: E402
import test_extend as ex  # noqa: E402  (the module, not its test class: importing the class would run its tests again here)
import test_tag_class as tc  # noqa: E402  (the module, as above)
from test_gates import Repo  # noqa: E402
from test_isnad_tag import fake_record, range_line, ranges_of  # noqa: E402

# lake_cache points tempfile at $RUNNER_TEMP when it is imported (its staging needs the runner's work disk); in this process that would move every other
# suite's temporary files there, and queue_comment.py refuses a facts file outside the temporary directory it was started with (CI, tooling-tests)
tempfile.tempdir = _tempdir

# The real case (formal-conjectures, tengoku#752, 7 Nov 2026): the autotag's `lake build` of the PR's modules died with
# `error: unknown target Tengoku.FormalConjectures.FormalConjecturesForMathlib.Geometry.2d`. With it, a part with a dot (an arXiv number) and one with a dash.
FC2D = "Tengoku/FormalConjectures/FormalConjecturesForMathlib/Geometry/2d.lean"
ODD = {
    FC2D: "Tengoku.FormalConjectures.FormalConjecturesForMathlib.Geometry.«2d»",
    "Tengoku/FormalConjectures/Tao/1102.4662.lean": "Tengoku.FormalConjectures.Tao.«1102.4662»",
    "Tengoku/FormalConjectures/Fx/A-B.lean": "Tengoku.FormalConjectures.Fx.«A-B»",
}


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

    def test_a_change_that_removes_a_module_checks_the_dotted_one_too(self):
        # every module of the tree is read then; the path of `1102.4662` must come back from its name as a file, not as Tengoku/Tao/1102/4662.lean (a missing path is skipped silently)
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("Tengoku/Tao/1102.4662.lean", "import Tengoku.Nope\n\ntheorem t : True := trivial\n")
        r.commit("a dotted module with a bad import is in the tree")
        r.git("checkout", "-q", "pr")
        r.git("merge", "-q", "--ff-only", "main")
        r.git("rm", "-q", "Tengoku/Lib/Basic.lean")
        r.commit("remove a module")
        rc, out = r.gate("imports_resolve.py")
        self.assertNotEqual(rc, 0, out)
        self.assertIn("Tengoku/Tao/1102.4662.lean", out)


class IntakeCheck(unittest.TestCase):
    B = "Tengoku.FxLib.Fx.«B-C»"

    def test_a_manifest_names_a_guillemet_module_and_the_part_adds_exactly_its_import(self):
        r = ex.Extend().repo()
        r.write("Tengoku/FxLib/Fx/B-C.lean", ex.module("b", f"import {ex.Extend.A}\n"))
        r.write("Tengoku/FxLib.lean", f"import {ex.Extend.A}\nimport {self.B}\n")
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
        r.write("data/intake/fx-lib/manifest.jsonl", old + ex.record("b", self.B))
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2, "gate2_unjudged": []}) + "\n")
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
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2, "gate2_unjudged": []}) + "\n")
        r.commit("part 2, manifest names another module")
        rc, out = r.gate("intake_check.py", "main", "pr")
        self.assertNotEqual(rc, 0)
        self.assertIn("is not a file of this PR", out)


class EveryPathToModule(unittest.TestCase):
    """Every place that turns a file of the tree into a module name uses the one rule (`_git.module_name`): what Lake builds, what the tagger is asked for,
    what the queue builds, what the cache check and the sweep compare with the imports."""

    def test_the_tag_gates_module_of_is_leans_spelling(self):
        for path, mod in ODD.items():
            self.assertEqual(tag_check.module_of(path), mod)

    def test_the_autotag_plan_lists_the_modules_as_lake_reads_them(self):
        # autotag.py plan writes plan.json["modules"]; the workflow passes each to `lake build` and `isnad.py tag --module`
        for path, mod in ODD.items():
            self.assertEqual(autotag.module_of(path), mod)

    def test_the_lake_cache_check_finds_the_importers_of_a_changed_guillemet_module(self):
        tmp = Path(tempfile.mkdtemp())
        files = {FC2D: "import Tengoku\n", "Tengoku/FormalConjectures/Use.lean": f"import {ODD[FC2D]}\n"}
        for rel, text in files.items():
            (tmp / rel).parent.mkdir(parents=True, exist_ok=True)
            (tmp / rel).write_text(text)
        cwd = os.getcwd()
        os.chdir(tmp)
        try:
            graph = lake_cache.import_graph()
        finally:
            os.chdir(cwd)
        changed = {lake_cache.module_of(FC2D)}
        self.assertEqual(changed, {ODD[FC2D]})
        self.assertIn("Tengoku.FormalConjectures.Use", lake_cache.downstream(changed, graph))
        # and Lake's own line for it names the same module, so it is not counted as a miss
        self.assertEqual(lake_cache.compiled(f"✔ [3/9] Built {ODD[FC2D]} (1s)\n"), changed)

    def test_the_sweep_plans_the_modules_as_lean_names_them(self):
        root = tc_tree({path: tc.PLAIN for path in ODD})
        self.assertEqual(sorted(isnad_sweep.todo(root, "libs")), sorted(ODD.values()))

    def test_the_sweep_orders_guillemet_modules_by_their_imports(self):
        # «2d» imports «1102.4662», which imports «A-B»: dependents first is 2d, 1102.4662, A-B (by name alone it would be 1102.4662, A-B, 2d)
        fx, tao, geo = (ODD[p] for p in ("Tengoku/FormalConjectures/Fx/A-B.lean", "Tengoku/FormalConjectures/Tao/1102.4662.lean", FC2D))
        root = tc_tree(
            {
                "Tengoku/FormalConjectures/Fx/A-B.lean": tc.PLAIN,
                "Tengoku/FormalConjectures/Tao/1102.4662.lean": f"import {fx}\n" + tc.PLAIN,
                FC2D: f"public import {tao}\n" + tc.PLAIN,
            }
        )
        self.assertEqual(isnad_sweep.todo(root, "libs"), [geo, tao, fx])


def tc_tree(files: dict[str, str]) -> Path:
    """a tree whose formal-conjectures library arrived as an intake bundle"""
    root = Path(tempfile.mkdtemp())
    (root / "data/intake/formal-conjectures").mkdir(parents=True)
    (root / "data/intake/formal-conjectures/manifest.jsonl").write_text("{}\n")
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text, encoding="utf-8")
    return root


class IsnadModuleFile(unittest.TestCase):
    """isnad.py gets the module as Lean prints it (`tengoku-isnad` writes `Name.toString`) and must find its file to write the tags into."""

    def test_a_guillemet_module_is_its_file(self):
        root = Path("/r")
        for path, mod in ODD.items():
            self.assertEqual(isnad.module_file(mod, root), root / path)
        self.assertEqual(isnad.module_file("Tengoku.Seed.Logic.Basic", root), root / "Tengoku/Seed/Logic/Basic.lean")

    def test_a_name_that_could_leave_the_root_is_still_refused(self):
        for bad in (
            ".etc.passwd",
            "Tengoku..A",
            "Tengoku.",
            "Tengoku.«..».etc",
            "Tengoku.«.»",
            "Tengoku.«»",
            "Tengoku.«a/b»",
            "a/b",
            "a\\b",
            "a\0b",
            "Tengoku.«2d",
        ):
            with self.assertRaises(ValueError, msg=bad):
                isnad.module_file(bad, Path("/r"))

    def test_the_tagger_writes_and_the_queue_checks_the_tags_of_the_2d_module(self):
        mod = ODD[FC2D]
        root = Path(tempfile.mkdtemp())
        path = root / FC2D
        path.parent.mkdir(parents=True)
        path.write_text(tc.PLAIN, encoding="utf-8")
        recs = [fake_record(f"t{k}", mod) for k in range(2)]
        lines = [range_line(i.name, {"range": i.rng, "sel": i.sel}, mod) for i in ranges_of(tc.PLAIN, 2)]
        plan, skipped = isnad.plan_tags(recs, lines)
        self.assertEqual(skipped, [])
        counts, why = isnad.tag_files(plan, root, write=True)
        self.assertEqual(why, [])
        text = path.read_text(encoding="utf-8")
        self.assertEqual(text.count("@isnad1 "), 2)
        lines = [range_line(i.name, {"range": i.rng, "sel": i.sel}, mod) for i in ranges_of(text, 2)]  # the build of the tagged module
        problems, summary = isnad.check_tags(recs, lines, [mod], root)
        self.assertEqual(problems, [])
        self.assertIn("2 tags right", summary)


class Queue(unittest.TestCase):
    """queue_targets.py: the merge queue builds a tag group's modules and an extend part's new modules by name; Lake must know that name."""

    def test_a_tag_group_on_guillemet_modules_is_built_by_their_lean_names(self):
        r = Repo()
        for path in ODD:
            r.write(path, tc.PLAIN)
        r.write(
            "data/intake/formal-conjectures/manifest.jsonl",
            json.dumps({"name": "x", "module": ODD[FC2D], "library": "formal-conjectures"}) + "\n",
        )
        r.commit("formal-conjectures is in the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        for path in ODD:
            r.write(path, tc.tagged(tc.PLAIN, tc.TRANSLATED))
        r.commit("tags")
        rc, out = r.gate("classify.py", env=tc.BOT)
        self.assertIn("class=tag", out)
        rc, out = r.gate("tag_check.py")
        self.assertEqual(rc, 0, out)
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(ln for ln in out.split() if ln.startswith("Tengoku.")), sorted(ODD.values()))

    def test_an_extend_part_with_guillemet_modules_is_built_by_their_lean_names(self):
        r = ex.Extend().repo()
        new = {
            "Tengoku/FxLib/Fx/Geometry/2d.lean": "Tengoku.FxLib.Fx.Geometry.«2d»",
            "Tengoku/FxLib/Fx/1102.4662.lean": "Tengoku.FxLib.Fx.«1102.4662»",
            "Tengoku/FxLib/Fx/A-B.lean": "Tengoku.FxLib.Fx.«A-B»",
        }
        for i, path in enumerate(new):
            r.write(path, ex.module(f"n{i}", f"import {ex.Extend.A}\n"))
        r.write("Tengoku/FxLib.lean", f"import {ex.Extend.A}\n" + "".join(f"import {m}\n" for m in new.values()))
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
        r.write("data/intake/fx-lib/manifest.jsonl", old + "".join(ex.record(f"n{i}", m) for i, m in enumerate(new.values())))
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2, "gate2_unjudged": []}) + "\n")
        r.commit("part 2 with a 2d, a dotted and a dashed module")
        rc, out = r.gate("intake_check.py", "main", "pr")
        self.assertEqual(rc, 0, out)
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(ln for ln in out.split() if ln.startswith("Tengoku.")), sorted(new.values()))


if __name__ == "__main__":
    unittest.main()
