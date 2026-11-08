"""The queue's regeneration check and a scope-fix PR.

2026-10-18, tengoku#601 (lean-pool and zflean notation made scoped): ejected by "regenerated derived files differ from the PR", 64 files, every line a deletion. lean-pool and zflean are
intake bundles AND registered with a corpus; the check regenerates the library of every Tengoku/ module a group touches unless the group's manifests name it as an intake library, and a
scope-fix PR edits modules in place and touches no manifest. The generator, with no records for an intake library, wrote nothing. Earlier scope-fix PRs were of libraries without a corpus.
Its own file, so that tests of other gates do not conflict with it."""

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
# stands in for scripts/generate.py: records that the queue ran it
GENERATOR_STUB = "import pathlib, sys\n\nwith pathlib.Path('generated.txt').open('a') as f:\n    f.write(' '.join(sys.argv[1:]) + '\\n')\n"
BASIC = 'import Tengoku\n\nnamespace Fx\n\nprefix:80 "-" => neg\n\ntheorem good : 1 + 1 = 2 := rfl\n\nend Fx\n'


class Regenerate(unittest.TestCase):
    def repo(self, corpora=("fx-lib",)):
        r = Repo()
        r.write("lean-toolchain", TOOLCHAIN + "\n")
        r.write("schemas/sources.json", json.dumps({"corpora": {lib: {"repo": "x", "commit": "c"} for lib in corpora}}))
        r.write("scripts/generate.py", GENERATOR_STUB)
        r.write("Tengoku/FxLib/Fx/Basic.lean", BASIC)
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.Basic\n")
        r.write("data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "Fx.good", "library": "fx-lib"}) + "\n")
        r.commit("an intake library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def regenerated(self, r, corpora):
        for lib in corpora:
            (r.dir / "corpora" / lib / ".git").mkdir(parents=True)  # the corpus is already 'cloned'
        rc, out = r.gate("queue_targets.py", "main", "pr", "--regenerate")
        gen = r.dir / "generated.txt"
        return rc, out, (gen.read_text() if gen.exists() else "")

    def test_a_scope_fix_pr_does_not_regenerate_an_intake_library_that_also_has_a_corpus(self):
        r = self.repo()
        r.write("Tengoku/FxLib/Fx/Basic.lean", BASIC.replace("prefix:80", "scoped prefix:80"))
        r.commit("scope fix")
        rc, out, generated = self.regenerated(r, ("fx-lib",))
        self.assertEqual(rc, 0, out)
        self.assertEqual(generated, "", "the generator ran for an intake library edited in place")

    def test_a_library_that_is_no_intake_bundle_is_still_regenerated_when_a_group_edits_its_module(self):
        r = self.repo()
        r.write("Tengoku/Other/Basic.lean", "import Tengoku\n\ntheorem o : True := trivial\n")
        r.write(
            "schemas/sources.json", json.dumps({"corpora": {"fx-lib": {"repo": "x", "commit": "c"}, "other": {"repo": "x", "commit": "c"}}})
        )
        r.commit("a derived library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        r.write("Tengoku/Other/Basic.lean", "import Tengoku\n\ntheorem o : True := by trivial\n")  # a hand edit of a generated file
        r.commit("a hand edit")
        rc, out, generated = self.regenerated(r, ("fx-lib", "other"))
        self.assertEqual(rc, 0, out)
        self.assertIn("--libraries other", generated)  # caught the way it always was
        self.assertNotIn("--libraries fx-lib", generated)

    def test_a_group_of_another_shape_is_regenerated_whatever_it_edits_in_an_intake_library(self):
        # Gitar on tengoku#613: the skip is for the scope-fix shape, not for every class that can carry a Tengoku/ path
        for extra in (
            (
                "Tengoku/FxLib/Fx/Extra.lean",
                "import Tengoku\n\ntheorem e : True := trivial\n",
            ),  # a module ADDED (an extend or a promotion adds)
            ("Tengoku/FxLib/NOTES.md", "a file that is no module\n"),
            (
                "data/staging/fx-lib.jsonl",
                json.dumps({"name": "Fx.n", "library": "fx-lib"}) + "\n",
            ),  # a promotion-shaped group: a record beside the edit
        ):
            r = self.repo()
            r.write("Tengoku/FxLib/Fx/Basic.lean", BASIC.replace("prefix:80", "scoped prefix:80"))
            r.write(*extra)
            r.commit("a group that is not a scope-fix")
            rc, out, generated = self.regenerated(r, ("fx-lib",))
            self.assertEqual(rc, 0, out)
            self.assertIn("--libraries fx-lib", generated, f"{extra[0]}: the library was not regenerated")

    def test_the_queue_still_builds_the_library_of_a_scope_fix(self):
        r = self.repo()
        r.write("Tengoku/FxLib/Fx/Basic.lean", BASIC.replace("prefix:80", "scoped prefix:80"))
        r.commit("scope fix")
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.splitlines() if ln.startswith("Tengoku.")], ["Tengoku.FxLib"])


if __name__ == "__main__":
    unittest.main()
