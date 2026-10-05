"""The `extend` class: the next part of a library that arrived in parts (scripts/bump/bundle_layers.py in the factory). Its own file, so that tests of other gates
added at the end of test_gates.py do not conflict with it."""

from __future__ import annotations

import json
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from bundle_tar import write_tar  # noqa: E402
from test_gates import Repo  # noqa: E402

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
BOT = {"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"}


def module(name: str, imports: str = "") -> str:
    return f"import Tengoku\n{imports}\nnamespace Fx\n\ntheorem {name} : 1 + 1 = 2 := rfl\n\nend Fx\n"


def record(name: str, mod: str, **over) -> str:
    return (
        json.dumps(
            {
                "name": f"Fx.{name}",
                "statement": f"theorem {name} : 1 + 1 = 2",
                "module": mod,
                "library": "fx-lib",
                "toolchain": TOOLCHAIN,
                "via": "equal",
                **over,
            }
        )
        + "\n"
    )


class Extend(unittest.TestCase):
    """Part 1 is in the tree (an intake PR); part 2 is the PR."""

    A, B = "Tengoku.FxLib.Fx.A", "Tengoku.FxLib.Fx.B"

    def repo(self, with_library=True):
        r = Repo()
        r.write("lean-toolchain", TOOLCHAIN + "\n")
        r.write("schemas/sources.json", json.dumps({"corpora": {}}))  # the queue reads it; no corpus is needed for an intake library
        r.write("Tengoku/All.lean", "import Tengoku.Lib\n" + ("import Tengoku.FxLib\n" if with_library else ""))
        if with_library:
            r.write("Tengoku/FxLib/Fx/A.lean", module("a"))
            r.write("Tengoku/FxLib.lean", f"import {self.A}\n")
            r.write("data/intake/fx-lib/manifest.jsonl", record("a", self.A))
            r.write("data/intake/fx-lib/report.json", json.dumps({"library": "fx-lib", "part": 1}) + "\n")
        r.commit("the tree, part 1 in it")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def part2(self, r, mod=None, umbrella=None, manifest=None, report=None, extra=None):
        r.write("Tengoku/FxLib/Fx/B.lean", mod if mod is not None else module("b", f"import {self.A}\n"))
        r.write("Tengoku/FxLib.lean", umbrella if umbrella is not None else f"import {self.A}\nimport {self.B}\n")
        old = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text() if (r.dir / "data/intake/fx-lib/manifest.jsonl").exists() else ""
        r.write("data/intake/fx-lib/manifest.jsonl", old + (manifest if manifest is not None else record("b", self.B)))
        r.write("data/intake/fx-lib/parts/002.json", report if report is not None else json.dumps({"library": "fx-lib", "part": 2}) + "\n")
        for p, s in (extra or {}).items():
            r.write(p, s)
        r.commit("part 2 of fx-lib")

    def check(self, r, *args):
        return r.gate("intake_check.py", "main", "pr", *args)

    def test_the_next_part_is_class_extend_and_passes(self):
        r = self.repo()
        self.part2(r)
        rc, out = r.gate("classify.py", env=BOT)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=extend", out)
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("extend ok: fx-lib: part 002, 1 modules, 1 theorems", out)

    def test_the_queue_builds_and_scans_the_new_modules_not_the_whole_library(self):
        r = self.repo()
        self.part2(r)
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.split() if ln.startswith("Tengoku.")], [self.B])

    def test_the_queue_still_builds_the_root_of_an_intake_library(self):
        r = self.repo(with_library=False)
        r.write("Tengoku/FxLib/Fx/A.lean", module("a"))
        r.write("Tengoku/FxLib.lean", f"import {self.A}\n")
        r.write("data/intake/fx-lib/manifest.jsonl", record("a", self.A))
        r.write("data/intake/fx-lib/report.json", json.dumps({"library": "fx-lib", "part": 1}) + "\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("part 1")
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("Tengoku.FxLib", out.split())

    def test_the_first_part_is_still_an_intake_pr(self):
        r = self.repo(with_library=False)
        r.write("Tengoku/FxLib/Fx/A.lean", module("a"))
        r.write("Tengoku/FxLib.lean", f"import {self.A}\n")
        r.write("data/intake/fx-lib/manifest.jsonl", record("a", self.A))
        r.write("data/intake/fx-lib/report.json", json.dumps({"library": "fx-lib", "part": 1}) + "\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("part 1")
        rc, out = r.gate("classify.py", env=BOT)
        self.assertIn("class=intake", out)
        self.assertEqual(self.check(r)[0], 0)

    def test_only_the_factory_account_may_send_one(self):
        r = self.repo()
        self.part2(r)
        rc, out = r.gate("classify.py", env={"PR_ACTOR": "someone", "TENGOKU_BOT": "tengoku-bot"})
        self.assertNotEqual(rc, 0)
        self.assertIn("factory's account", out)

    def test_the_archive_is_the_parts_own_files_as_the_factory_built_them(self):
        r = self.repo()
        self.part2(r)
        tar = Path(tempfile.mkdtemp()) / "part.tar"
        rc, out = self.check(r, "--tar", str(tar))
        self.assertEqual(rc, 0, out)
        want = {
            "Tengoku/FxLib/Fx/B.lean": module("b", f"import {self.A}\n").encode(),
            "Tengoku/FxLib.lean": f"import {self.A}\nimport {self.B}\n".encode(),
            "manifest.jsonl": record("b", self.B).encode(),  # the part's lines only, not the tree's
            "report.json": (json.dumps({"library": "fx-lib", "part": 2}) + "\n").encode(),
        }
        with tarfile.open(tar) as t:
            self.assertEqual(sorted(t.getnames()), sorted(want))
        self.assertIn(write_tar(want, str(Path(tempfile.mkdtemp()) / "x.tar")), out)

    def test_a_library_that_is_not_in_the_tree_cannot_arrive_as_a_part(self):
        r = self.repo(with_library=False)
        r.write("Tengoku/FxLib/Fx/B.lean", module("b"))
        r.write("Tengoku/FxLib.lean", f"import {self.B}\n")
        r.write("data/intake/fx-lib/manifest.jsonl", record("b", self.B))
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2}) + "\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("a new library claiming to be part 2")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("is not in the tree", out)

    def test_parts_merge_in_order(self):
        r = self.repo()
        self.part2(r)
        r.git("mv", "data/intake/fx-lib/parts/002.json", "data/intake/fx-lib/parts/003.json")
        r.commit("part 3 before part 2")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("the next one is 002", out)

    def test_a_part_already_in_the_tree_cannot_come_again(self):
        r = self.repo()
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2}) + "\n")
        r.write("Tengoku/FxLib/Fx/B.lean", module("b", f"import {self.A}\n"))
        r.write("Tengoku/FxLib.lean", f"import {self.A}\nimport {self.B}\n")
        r.write("data/intake/fx-lib/manifest.jsonl", record("a", self.A) + record("b", self.B))
        r.commit("part 2 merged")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "-b", "pr2")
        r.write("Tengoku/FxLib/Fx/C.lean", module("c"))
        r.write("Tengoku/FxLib.lean", f"import {self.A}\nimport {self.B}\nimport Tengoku.FxLib.Fx.C\n")
        r.write("data/intake/fx-lib/manifest.jsonl", record("a", self.A) + record("b", self.B) + record("c", "Tengoku.FxLib.Fx.C"))
        r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2}) + "\n")  # modified, not added
        r.commit("part 2 again")
        rc, out = r.gate("intake_check.py", "main", "pr2")
        self.assertNotEqual(rc, 0)

    def test_the_report_names_its_part_and_library(self):
        for report, why in (
            (json.dumps({"library": "fx-lib", "part": 3}) + "\n", "says part 3"),
            (json.dumps({"library": "other", "part": 2}) + "\n", "of 'other'"),
            ("not json\n", "not a JSON report"),
        ):
            with self.subTest(report=report):
                r = self.repo()
                self.part2(r, report=report)
                rc, out = self.check(r)
                self.assertNotEqual(rc, 0)
                self.assertIn(why, out)

    def test_all_lean_is_left_alone(self):
        r = self.repo()
        self.part2(r, extra={"Tengoku/All.lean": "import Tengoku.Lib\nimport Tengoku.FxLib\nimport Tengoku.FxLib\n"})
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("not part of fx-lib's part", out)

    def test_an_existing_module_is_never_rewritten(self):
        r = self.repo()
        self.part2(r, extra={"Tengoku/FxLib/Fx/A.lean": module("a") + "\n-- edited\n"})
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("status M", out)

    def test_the_root_file_gains_the_new_modules_imports_and_nothing_else(self):
        for umbrella, why in (
            (f"import {self.A}\n", "must import each new module exactly once"),
            (f"import {self.A}\nimport {self.B}\nimport {self.B}\n", "must import each new module exactly once"),
            (f"import {self.B}\n", "may only gain"),  # drops part 1's import
            (f"import {self.A}\nimport {self.B}\n-- a comment\n", "may only gain"),
            (
                f"import {self.A}\nimport {self.B}\nimport Tengoku.FxLib.Fx.Z\n",
                "may only gain",
            ),  # an import of a module that is not in the PR
        ):
            with self.subTest(umbrella=umbrella):
                r = self.repo()
                self.part2(r, umbrella=umbrella)
                rc, out = self.check(r)
                self.assertNotEqual(rc, 0)
                self.assertIn(why, out)

    def test_a_public_import_in_the_root_file_is_accepted(self):
        r = self.repo()
        self.part2(r, umbrella=f"import {self.A}\npublic import {self.B}\n")
        self.assertEqual(self.check(r)[0], 0)

    def test_the_manifest_only_gains_lines_at_its_end(self):
        r = self.repo()
        self.part2(r)
        r.write("data/intake/fx-lib/manifest.jsonl", record("b", self.B) + record("a", self.A))  # reordered: the tree's line is not first
        r.commit("reorder")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("only gain lines at its end", out)
        r2 = self.repo()
        self.part2(r2)
        r2.write("data/intake/fx-lib/manifest.jsonl", record("a", self.A, statement="theorem a : 2 + 2 = 4") + record("b", self.B))
        r2.commit("edit an old line")
        self.assertIn("only gain lines at its end", self.check(r2)[1])

    def test_a_part_with_no_new_theorem_is_empty(self):
        r = self.repo()
        self.part2(r, manifest="\n")  # the manifest changes by a blank line only
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("a part that carries none is empty", out)
        r2 = self.repo()
        self.part2(r2, manifest="")  # not changed at all: the PR is not an extend PR
        rc, out = self.check(r2)
        self.assertNotEqual(rc, 0)
        self.assertIn("exactly one data/intake/<library>/manifest.jsonl", out)

    def test_a_name_the_library_already_has_is_not_declared_again(self):
        r = self.repo()
        self.part2(r, manifest=record("a", self.B))  # Fx.a again, this time in B
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("twice", out)

    def test_the_new_lines_name_modules_of_this_part_and_the_trees_toolchain(self):
        r = self.repo()
        self.part2(r, manifest=record("b", self.A))  # a module of part 1, not of this PR
        rc, out = self.check(r)
        self.assertIn("not a file of this PR", out)
        r2 = self.repo()
        self.part2(r2, manifest=record("b", self.B, toolchain="leanprover/lean4:v4.29.1"))
        self.assertIn("toolchain", self.check(r2)[1])

    def test_the_lint_judges_the_new_modules(self):
        r = self.repo()
        self.part2(r, mod=module("b", f"import {self.A}\n") + '\n#eval IO.println "x"\n')
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("no # commands", out)
        r2 = self.repo()
        self.part2(r2, mod="import Mathlib.Data.Nat.Basic\n" + module("b", f"import {self.A}\n"))
        self.assertIn("not the tree", self.check(r2)[1])

    def sized(self, total):
        """A part of `total` modules: B and total - 1 more."""
        r = self.repo()
        many = {f"Tengoku/FxLib/Fx/M{i:03d}.lean": module(f"m{i}") for i in range(total - 1)}
        imports = f"import {self.A}\nimport {self.B}\n" + "".join(f"import Tengoku.FxLib.Fx.M{i:03d}\n" for i in range(total - 1))
        self.part2(r, umbrella=imports, extra=many)
        return self.check(r)

    def test_a_part_has_a_size_limit(self):
        rc, out = self.sized(400)  # exactly the cap
        self.assertEqual(rc, 0, out)
        rc, out = self.sized(401)  # one over
        self.assertNotEqual(rc, 0)
        self.assertIn("cut the bundle into smaller parts", out)

    def test_an_extend_pr_is_nothing_but_the_part(self):
        r = self.repo()
        self.part2(r, extra={"scripts/x.py": "print(2)\n"})
        rc, out = r.gate("classify.py", env=BOT)
        self.assertNotEqual(rc, 0)
        self.assertIn("nothing else", out)

    def test_two_parts_in_one_pr_are_refused(self):
        r = self.repo()
        self.part2(r, extra={"data/intake/fx-lib/parts/003.json": json.dumps({"library": "fx-lib", "part": 3}) + "\n"})
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("adds one part", out)


if __name__ == "__main__":
    unittest.main()
