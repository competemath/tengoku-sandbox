"""The `raze` class (scripts/ci/raze_check.py, docs/pr-classes.md section 8): modules of an intake library taken out of the tree, with what depends on them.
Its own file, so that tests of other gates added at the end of test_gates.py do not conflict with it."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from test_gates import Repo  # noqa: E402

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
P = "Tengoku.FxLib.Fx."
MODULES = {  # module -> (imports, odd file name)
    "A": [],
    "B": ["A"],
    "C": ["B"],
    "D": [],
    "E-F": ["D"],  # a component that is not an identifier: written in guillemets
}


def mod_name(key: str) -> str:
    return P + (f"«{key}»" if "-" in key else key)


def path_of(key: str) -> str:
    return f"Tengoku/FxLib/Fx/{key}.lean"


def text_of(key: str) -> str:
    imports = "".join(f"import {mod_name(i)}\n" for i in MODULES[key])
    return f"/-\nAuthors: Someone\n-/\nimport Tengoku\n{imports}\nnamespace Fx\n\ntheorem t{key.replace('-', '_')} : 1 + 1 = 2 := rfl\n\nend Fx\n"


def record(key: str) -> str:
    return (
        json.dumps(
            {
                "name": f"Fx.t{key.replace('-', '_')}",
                "statement": "theorem t : 1 + 1 = 2",
                "module": mod_name(key),
                "library": "fx-lib",
                "source_url": "https://x/y",
                "toolchain": TOOLCHAIN,
            }
        )
        + "\n"
    )


# stands in for scripts/generate.py: records that the queue ran it (it would rewrite Tengoku/All.lean as the real one does)
GENERATOR_STUB = "import pathlib, sys\n\nwith pathlib.Path('generated.txt').open('a') as f:\n    f.write(' '.join(sys.argv[1:]) + '\\n')\n"


def umbrella(keys) -> str:
    return "".join(f"import {mod_name(k)}\n" for k in keys)


class Raze(unittest.TestCase):
    def repo(self, other_importing=None, parts=True, ghost=False, garbage=False, corpora=()):
        r = Repo()
        r.write("lean-toolchain", TOOLCHAIN + "\n")
        r.write("schemas/sources.json", json.dumps({"corpora": {lib: {"repo": "x", "commit": "c"} for lib in corpora}}))
        if corpora:
            r.write("scripts/generate.py", GENERATOR_STUB)
        r.write("Tengoku.lean", "")  # the roots every module imports
        r.write("Tengoku/Lib.lean", "import Tengoku.Lib.Basic\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        for k in MODULES:
            r.write(path_of(k), text_of(k))
        r.write("Tengoku/FxLib.lean", umbrella(MODULES))
        r.write(
            "data/intake/fx-lib/manifest.jsonl",
            "".join(record(k) for k in MODULES)
            + (json.dumps({"name": "Fx.ghost", "module": P + "Ghost"}) + "\n" if ghost else "")
            + ('not json at all "source_url"\n' if garbage else ""),
        )
        r.write("data/intake/fx-lib/report.json", json.dumps({"library": "fx-lib", "part": 1, "gate2_unjudged": []}) + "\n")
        if parts:
            r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2, "gate2_unjudged": []}) + "\n")
        if other_importing:
            r.write("Tengoku/OtherLib/Use.lean", f"import Tengoku\nimport {mod_name(other_importing)}\n\ntheorem u : True := trivial\n")
            r.write("Tengoku/OtherLib.lean", "import Tengoku.OtherLib.Use\n")
        r.commit("the tree: an intake library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def raze(self, r, keys, *, marker=None, keep_files=(), keep_umbrella=(), keep_records=(), extra=None, name="fx-1"):
        """Write the PR that razes `keys`; the keyword arguments break one rule at a time."""
        keys = list(keys)
        for k in keys:
            if k not in keep_files:
                (r.dir / path_of(k)).unlink()
        left = [k for k in MODULES if k not in keys or k in keep_umbrella]
        r.write("Tengoku/FxLib.lean", umbrella(left))
        r.write("data/intake/fx-lib/manifest.jsonl", "".join(record(k) for k in MODULES if k not in keys or k in keep_records))
        body = {
            "library": "fx-lib",
            "modules": [mod_name(k) for k in keys],
            "reason": "the first pruner cut declarations that later parts name",
        }
        body.update(marker or {})
        r.write(f"data/raze/{name}.json", json.dumps(body))
        for p, s in (extra or {}).items():
            r.write(p, s)
        r.commit("raze")

    def raze_all(self, r, marker=None, all_line=True, name="fx-all"):
        """Write the PR that razes the whole library."""
        for k in MODULES:
            (r.dir / path_of(k)).unlink()
        (r.dir / "Tengoku/FxLib.lean").unlink()
        for p in ("manifest.jsonl", "report.json", "parts/002.json"):
            if (r.dir / "data/intake/fx-lib" / p).exists():
                (r.dir / "data/intake/fx-lib" / p).unlink()
        if all_line:
            r.write("Tengoku/All.lean", "import Tengoku.Lib\n")
        body = {"library": "fx-lib", "all": True, "reason": "the library is cut again from a corrected bundle"}
        body.update(marker or {})
        r.write(f"data/raze/{name}.json", json.dumps(body))
        r.commit("raze the library")

    def judge(self, r, script="raze_check.py"):
        rc, out = r.gate("classify.py")
        if rc != 0:
            return rc, out
        self.assertIn("class=raze", out)
        return r.gate(script)

    # --- the class

    def test_a_leaf_raze_passes_every_gate_and_comes_from_any_author(self):
        r = self.repo()
        self.raze(r, ["C"])
        rc, out = self.judge(r)  # no PR_ACTOR: not the bot's
        self.assertEqual(rc, 0, out)
        self.assertIn("raze OK: 1 module(s) of fx-lib", out)
        for s in ("credits.py", "imports_resolve.py", "dco.py"):
            args = ("main", "pr", "--raze") if s == "credits.py" else ("main", "pr")
            rc, out = r.gate(s, *args)
            self.assertEqual(rc, 0, f"{s}: {out}")

    def test_a_chain_is_razed_together_and_a_module_with_a_guillemet_name_is_named_either_way(self):
        r = self.repo()
        self.raze(r, ["B", "C"])
        self.assertEqual(self.judge(r)[0], 0)
        r = self.repo()
        self.raze(r, ["E-F"], marker={"modules": ["Tengoku.FxLib.Fx.E-F"]})  # written without the guillemets
        rc, out = self.judge(r)
        self.assertEqual(rc, 0, out)

    def test_a_pr_that_edits_an_existing_marker_is_not_a_raze_pr(self):
        r = self.repo()
        r.write(
            "data/raze/old.json", json.dumps({"library": "fx-lib", "modules": [mod_name("C")], "reason": "an old one that already merged"})
        )
        r.commit("a marker in the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        r.write("data/raze/old.json", json.dumps({"library": "fx-lib", "modules": [mod_name("D")], "reason": "rewritten after the fact"}))
        r.commit("edit the record")
        rc, out = r.gate("classify.py")
        self.assertNotIn("class=raze", out)

    # --- the dependencies go with it

    def test_a_module_that_remains_and_imports_a_razed_one_fails(self):
        r = self.repo()
        self.raze(r, ["B"])  # C imports B
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/FxLib/Fx/C.lean remains but imports", out)

    def test_a_module_of_another_library_that_imports_a_razed_one_fails_in_the_import_gate(self):
        r = self.repo(other_importing="D")
        self.raze(r, ["D", "E-F"])
        self.assertEqual(self.judge(r)[0], 0)  # raze_check reads the library; the rest of the tree is imports_resolve's
        rc, out = r.gate("imports_resolve.py")
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/OtherLib/Use.lean", out)

    def test_a_record_that_remains_may_not_name_a_module_that_does_not(self):
        r = self.repo()
        self.raze(r, ["C"])
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
        r.write("data/intake/fx-lib/manifest.jsonl", old + record("C"))  # the razed module's record is still there
        r.commit("keep a record")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("records of razed modules remain", out)

    def test_a_record_of_a_module_the_library_never_had_is_not_left_dangling(self):
        r = self.repo(ghost=True)  # the base manifest already has a record whose module is no file of the library
        self.raze(r, ["C"])
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
        r.write(
            "data/intake/fx-lib/manifest.jsonl", old + json.dumps({"name": "Fx.ghost", "module": P + "Ghost"}) + "\n"
        )  # the raze leaves it where it is
        r.commit("keep the ghost record")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("records that remain name modules that do not remain", out)

    # --- nothing but the removal

    def test_the_files_deleted_are_exactly_the_marker_modules(self):
        r = self.repo()
        self.raze(r, ["C"], keep_files=["C"])  # named, not deleted
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("razes files the PR does not delete", out)
        r = self.repo()
        self.raze(r, ["C"], marker={"modules": [mod_name("C")]})
        (r.dir / path_of("D")).unlink()  # a second file deleted that the marker does not name
        r.write("Tengoku/FxLib.lean", umbrella(["A", "B", "E-F"]))
        r.commit("one more")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("deletes files the marker does not name", out)

    def test_a_module_the_marker_names_must_be_a_module_of_the_library(self):
        r = self.repo()
        self.raze(r, ["C"], marker={"modules": [mod_name("C"), P + "Nope"]})
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("not modules of fx-lib at the base", out)

    def test_the_umbrella_loses_the_import_lines_of_the_razed_modules_and_nothing_else(self):
        r = self.repo()
        self.raze(r, ["C"], keep_umbrella=["C"])  # C's line stays
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/FxLib.lean: must lose exactly", out)
        r = self.repo()
        self.raze(r, ["C"])
        r.write("Tengoku/FxLib.lean", umbrella(["A", "B", "D", "E-F"]) + "import Tengoku.FxLib.Fx.Extra\n")  # a line gained
        r.commit("add an import")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/FxLib.lean: must lose exactly", out)

    def test_the_manifest_loses_exactly_the_razed_records_in_place(self):
        r = self.repo()
        self.raze(r, ["C"])
        r.write("data/intake/fx-lib/manifest.jsonl", "".join(record(k) for k in ["A", "B", "E-F"]))  # D's record went too
        r.commit("one record too many")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("must lose exactly the lines of the records of the razed modules", out)
        r = self.repo()
        self.raze(r, ["C"])
        r.write("data/intake/fx-lib/manifest.jsonl", "".join(record(k) for k in ["B", "A", "D", "E-F"]))  # reordered
        r.commit("reorder")
        self.assertEqual(self.judge(r)[0], 1)

    def test_nothing_else_may_change(self):
        r = self.repo()
        self.raze(r, ["C"], extra={"README.md": "# changed\n"})
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("README.md: a raze PR changes nothing but", out)
        r = self.repo()
        self.raze(r, ["C"], extra={"Tengoku/FxLib/Fx/D.lean": text_of("D") + "-- a note\n"})  # a module that stays, edited
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/FxLib/Fx/D.lean", out)

    # --- the marker

    def test_the_marker_has_a_reason_and_names_modules_or_the_whole_library(self):
        for bad in (
            {"reason": "short"},
            {"all": True},  # both
            {"extra": 1},
            {"modules": [mod_name("C"), mod_name("C")]},  # a module twice
            {"modules": {mod_name("C"): 1}},  # not a list (a dict iterates over the same names)
            {"library": ""},
        ):
            r = self.repo()
            self.raze(r, ["C"], marker=bad)
            rc, out = self.judge(r)
            self.assertEqual(rc, 1, bad)
        r = self.repo()
        self.raze(r, [], marker={"modules": []})  # neither modules nor all: an empty raze that would otherwise be a valid no-op
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("not both and not neither", out)

    def test_a_marker_that_is_not_json_is_refused(self):
        r = self.repo()
        self.raze(r, ["C"])
        r.write("data/raze/fx-1.json", "{not json")
        r.commit("break the marker")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("not JSON", out)

    def test_a_library_with_a_manifest_but_no_module_at_the_base_is_refused(self):
        r = self.repo()
        r.write("data/intake/zz-lib/manifest.jsonl", "")
        r.commit("a manifest with no module")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        r.write(
            "data/raze/zz.json",
            json.dumps({"library": "zz-lib", "modules": ["Tengoku.ZzLib.A"], "reason": "a library that has no module at all"}),
        )
        r.commit("raze")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("has no module at the base", out)

    def test_the_umbrella_and_the_manifest_must_survive_a_partial_raze(self):
        r = self.repo()
        self.raze(r, ["C"])
        (r.dir / "Tengoku/FxLib.lean").unlink()
        r.commit("delete the umbrella")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/FxLib.lean: not readable at the base and the head", out)
        r = self.repo()
        self.raze(r, ["C"])
        (r.dir / "data/intake/fx-lib/manifest.jsonl").unlink()
        r.commit("delete the manifest")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("manifest.jsonl: not readable at the head", out)

    def test_only_a_library_that_arrived_as_an_intake_bundle_can_be_razed(self):
        r = self.repo()
        self.raze(r, ["C"], marker={"library": "lib"})  # Tengoku/Lib/ is generated from records: no manifest
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("is not a library of the tree at the base", out)

    def test_two_markers_are_not_one_raze(self):
        r = self.repo()
        self.raze(r, ["C"], extra={"data/raze/other.json": json.dumps({"library": "fx-lib", "modules": [], "reason": "a second marker"})})
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("adds exactly one marker", out)

    def test_a_partial_raze_is_capped(self):
        r = Repo()
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        keys = [f"M{i}" for i in range(801)]
        for k in keys:
            r.write(f"Tengoku/FxLib/Fx/{k}.lean", "import Tengoku\n")
        r.write("Tengoku/FxLib/Fx/Keep.lean", "import Tengoku\n")
        r.write("Tengoku/FxLib.lean", "".join(f"import {P}{k}\n" for k in keys) + f"import {P}Keep\n")
        r.write("data/intake/fx-lib/manifest.jsonl", "".join(json.dumps({"name": f"Fx.{k}", "module": P + k}) + "\n" for k in keys))
        r.commit("a big library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        for k in keys:
            (r.dir / f"Tengoku/FxLib/Fx/{k}.lean").unlink()
        r.write("Tengoku/FxLib.lean", f"import {P}Keep\n")
        r.write("data/intake/fx-lib/manifest.jsonl", "")
        r.write(
            "data/raze/big.json",
            json.dumps({"library": "fx-lib", "modules": [P + k for k in keys], "reason": "too many for one partial raze"}),
        )
        r.commit("raze 801")
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("at most 800 modules", out)

    # --- the whole library

    def test_a_whole_library_raze_deletes_the_folder_the_data_and_the_all_line(self):
        r = self.repo()
        self.raze_all(r)
        rc, out = self.judge(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("(the whole library)", out)
        rc, out = r.gate("credits.py", "main", "pr", "--raze")
        self.assertEqual(rc, 0, out)
        rc, out = r.gate("imports_resolve.py")
        self.assertEqual(rc, 0, out)

    def test_a_whole_library_raze_that_leaves_its_all_line_fails(self):
        r = self.repo()
        self.raze_all(r, all_line=False)
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("Tengoku/All.lean", out)

    def test_a_marker_gives_modules_or_all_not_both(self):
        r = self.repo()
        self.raze_all(r, marker={"modules": [mod_name("C")]})  # a whole-library PR whose marker also lists modules
        rc, out = self.judge(r)
        self.assertEqual(rc, 1)
        self.assertIn("not both and not neither", out)

    # --- credits and the queue

    def test_credit_lines_go_only_with_what_is_deleted(self):
        r = self.repo()
        self.raze(r, ["C"])
        rc, out = r.gate("credits.py", "main", "pr")  # without --raze the deleted module's `Authors:` line is a removed credit
        self.assertEqual(rc, 1)
        self.assertIn("Authors", out)
        self.assertEqual(r.gate("credits.py", "main", "pr", "--raze")[0], 0)
        r = self.repo()
        self.raze(r, ["C"], extra={"Tengoku/FxLib/Fx/D.lean": text_of("D").replace("Authors: Someone", "Authors: Nobody")})
        rc, out = r.gate("credits.py", "main", "pr", "--raze")  # a credit changed in a module that stays
        self.assertEqual(rc, 1)
        self.assertIn("D.lean", out)
        r = self.repo()
        self.raze(r, ["C"])
        lines = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text().splitlines(keepends=True)
        r.write(
            "data/intake/fx-lib/manifest.jsonl", "".join(ln for ln in lines if '"Fx.tD"' not in ln)
        )  # the record of a module that STAYS loses its source_url line
        r.commit("a kept record goes")
        self.assertEqual(r.gate("credits.py", "main", "pr", "--raze")[0], 1)

    def test_a_removed_manifest_line_that_is_not_json_is_a_credit_that_goes_with_nothing(self):
        r = self.repo(garbage=True)
        self.raze(r, ["C"])  # the manifest is rewritten from the modules: the line that names no module goes with the rest
        rc, out = r.gate("credits.py", "main", "pr", "--raze")
        self.assertEqual(rc, 1)
        self.assertIn("source_url", out)

    def test_the_queue_builds_the_library_without_the_modules_and_has_no_root_for_a_whole_raze(self):
        r = self.repo()
        self.raze(r, ["C"])
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.splitlines() if ln.startswith("Tengoku.")], ["Tengoku.FxLib"])
        r = self.repo(parts=False)  # a library that arrived in one part: no part report masks the manifest's deletion
        self.raze_all(r)
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.splitlines() if ln.startswith("Tengoku.")], [])

    # --- the queue regenerates the derived files of the libraries a group touches, and a library that is also registered with a corpus (navier-stokes-euler) must not be one of them

    def regenerated(self, r, corpora):
        for lib in corpora:
            (r.dir / "corpora" / lib / ".git").mkdir(parents=True)  # the corpus is already 'cloned'
        rc, out = r.gate("queue_targets.py", "main", "pr", "--regenerate")
        gen = r.dir / "generated.txt"
        return rc, out, (gen.read_text() if gen.exists() else "")

    def test_a_whole_library_raze_does_not_regenerate_the_library_it_removes(self):
        # 2026-10-16, tengoku#579: navier-stokes-euler is an intake bundle AND has a corpus; the manifest the raze deletes took it out of the intake set, so the modules the raze
        # deletes made the queue regenerate it, and the generator rewrote Tengoku/All.lean as it writes it ("regenerated derived files differ from the PR")
        r = self.repo(parts=False, corpora=("fx-lib",))
        self.raze_all(r)
        rc, out, generated = self.regenerated(r, ("fx-lib",))
        self.assertEqual(rc, 0, out)
        self.assertEqual(generated, "", "the generator ran for a library that was razed whole")

    def test_a_partial_raze_does_not_regenerate_either(self):
        r = self.repo(corpora=("fx-lib",))
        self.raze(r, ["C"])
        rc, out, generated = self.regenerated(r, ("fx-lib",))
        self.assertEqual(rc, 0, out)
        self.assertEqual(generated, "")

    def test_a_derived_module_edited_by_hand_still_regenerates_its_library(self):
        # the rule the exclusion must not break: a library with a corpus and no intake bundle is regenerated for the modules a group touches
        r = self.repo(corpora=("fx-lib", "lib"))
        r.write("Tengoku/Lib/Basic.lean", "/-\nAuthors: Someone\n-/\ntheorem Lib.old : 1 + 1 = 2 := by decide\n")
        r.commit("edit a derived module")
        rc, out, generated = self.regenerated(r, ("fx-lib", "lib"))
        self.assertEqual(rc, 0, out)
        self.assertIn("--libraries lib", generated)
        self.assertNotIn("fx-lib", generated)

    def test_a_whole_raze_next_to_a_hand_edited_library_regenerates_only_the_latter(self):
        r = self.repo(parts=False, corpora=("fx-lib", "lib"))
        self.raze_all(r)
        r.write("Tengoku/Lib/Basic.lean", "/-\nAuthors: Someone\n-/\ntheorem Lib.old : 1 + 1 = 2 := by decide\n")
        r.commit("and an edit")
        rc, out, generated = self.regenerated(r, ("fx-lib", "lib"))
        self.assertEqual(rc, 0, out)
        self.assertEqual(generated.count("--libraries"), 1)
        self.assertIn("--libraries lib", generated)
        self.assertNotIn("fx-lib", generated)  # one run for `lib` alone, not `--libraries lib fx-lib`


if __name__ == "__main__":
    unittest.main()
