"""The `tag` class: isnad tags written into modules that are already in the tree (scripts/ci/tag_check.py, tag_verify.py; docs/pr-classes.md, section 7). Its own
file, so that tests of other gates added at the end of test_gates.py do not conflict with it."""

from __future__ import annotations

import json
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
import isnad  # noqa: E402
import isnad_tag as tg  # noqa: E402
import tag_check  # noqa: E402
from test_gates import Repo  # noqa: E402
from test_isnad_tag import fake_record, range_line, ranges_of  # noqa: E402

BOT = {"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"}
TAG = "@isnad1 id=eq.0h2v.s4.05598c1b76c4 from=seed src=0 shape=900bc7c0 vocab=fc0e7020"
OLDTAG = TAG.replace("05598c1b76c4", "111111111111")
NOVEL = TAG.replace("from=seed", "from=novel")
TRANSLATED = TAG.replace("from=seed", "from=translated").replace("src=0", "src=-")
PLAIN = "import Tengoku\n\n/-- Addition is commutative. -/\ntheorem t0 : 1 + 1 = 2 := rfl\n\ntheorem t1 : 2 + 2 = 4 := rfl\n"
SEED = "Tengoku/Seed/Logic/Fx.lean"
MULTILINE = "import Tengoku\n\n/-- First line.\nSecond line. -/\ntheorem t0 : 1 + 1 = 2 := rfl\n"
LIB = "Tengoku/FxLib/Fx/A.lean"


def tagged(text: str, tag: str = TAG) -> str:
    """what the tagger writes: the tag as the last line of each theorem's docstring, a new docstring for a theorem that has none"""
    n = text.count("theorem t")
    new, _, skipped = tg.tag_text(text, [tg.Item(i.name, i.rng, i.sel, tag) for i in ranges_of(text, n)])
    assert not skipped, skipped
    return new


class Setup(unittest.TestCase):
    def repo(self):
        r = Repo()
        r.write(SEED, PLAIN)
        r.write(LIB, PLAIN)
        r.write("Tengoku/Native/Fx.lean", PLAIN)
        r.write(
            "Tengoku/Seed.lean", PLAIN
        )  # a root file: a theorem in it would be taggable text, but it is not a module a tag PR may touch
        r.write("Tengoku/Lib/Basic.lean", PLAIN)  # `Lib` has data/trusted/lib.jsonl: its modules are generated
        r.write(
            "data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "Fx.a", "module": "Tengoku.FxLib.Fx.A", "library": "fx-lib"}) + "\n"
        )
        r.commit("the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def tag_pr(self, r, files=None, tag=TAG):
        for path in files or (SEED,):
            r.write(path, tagged(PLAIN, tag))
        r.commit("tags")

    def classify(self, r, env=BOT):
        return r.gate("classify.py", env=env)

    def check(self, r):
        return r.gate("tag_check.py")


class Gate(Setup):
    def test_tags_in_the_seed_are_a_tag_pr_and_pass(self):
        r = self.repo()
        self.tag_pr(r)
        rc, out = self.classify(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=tag (1 modules)", out)
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("tag ok: 1 modules, only tags", out)

    def test_an_intake_library_and_native_are_tagged_with_their_own_origin(self):
        r = self.repo()
        r.write(LIB, tagged(PLAIN, TRANSLATED))
        r.write("Tengoku/Native/Fx.lean", tagged(PLAIN, NOVEL))
        r.commit("tags")
        self.assertIn("class=tag (2 modules)", self.classify(r)[1])
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)

    def test_only_the_factory_account_may_send_one(self):
        r = self.repo()
        self.tag_pr(r)
        rc, out = self.classify(r, {"PR_ACTOR": "someone", "TENGOKU_BOT": "tengoku-bot"})
        self.assertNotEqual(rc, 0)
        self.assertIn("a tag PR comes from the factory's account", out)

    def test_in_the_merge_queue_the_gate_that_checked_the_actor_is_enough(self):
        r = self.repo()
        self.tag_pr(r)
        rc, out = self.classify(r, {"TENGOKU_ACTOR_CHECKED": "1", "PR_ACTOR": ""})
        self.assertEqual(rc, 0, out)
        self.assertIn("class=tag", out)

    def test_a_code_change_next_to_the_tag_is_not_a_tag_pr(self):
        r = self.repo()
        r.write(SEED, tagged(PLAIN).replace("1 + 1 = 2", "1 + 1 = 3"))
        r.commit("tags and a statement")
        self.assertNotIn("class=tag", self.classify(r)[1])
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("changes more than tags", out)

    def test_one_changed_file_among_tag_files_makes_it_not_a_tag_pr(self):
        r = self.repo()
        r.write(SEED, tagged(PLAIN))
        r.write(LIB, PLAIN.replace("rfl", "by rfl"))
        r.commit("tags and a proof change")
        self.assertNotIn("class=tag", self.classify(r)[1])
        self.assertIn("changes more than tags", self.check(r)[1])

    def test_a_changed_docstring_word_is_not_a_tag(self):
        r = self.repo()
        r.write(SEED, tagged(PLAIN).replace("commutative", "associative"))
        r.commit("tags and a docstring")
        self.assertNotIn("class=tag", self.classify(r)[1])
        self.assertIn("changes more than tags", self.check(r)[1])

    def test_a_change_without_a_tag_is_not_a_tag_pr(self):
        r = self.repo()
        r.write(
            SEED, PLAIN.replace("/-- Addition is commutative. -/", "/-- Addition is commutative.   -/")
        )  # whitespace before the closing only
        r.commit("whitespace")
        self.assertNotIn("class=tag", self.classify(r)[1])
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("writes no tag", out)

    def test_a_change_that_leaves_the_tags_as_they_were_writes_no_tag(self):
        r = self.repo()
        r.write(SEED, tagged(PLAIN))
        r.commit("the tree, tagged")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        r.write(SEED, tagged(PLAIN).replace(f"{TAG}\n-/", f"{TAG}\n\n-/", 1))  # a blank line before the closing: equivalent, no tag written
        r.commit("whitespace in a tagged docstring")
        self.assertNotIn("class=tag", self.classify(r)[1])
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("writes no tag", out)

    def test_replacing_a_tag_is_a_tag_pr(self):
        r = self.repo()
        r.write(SEED, tagged(PLAIN, OLDTAG))
        r.commit("the tree, tagged")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        self.tag_pr(r)
        self.assertIn("class=tag", self.classify(r)[1])
        self.assertEqual(self.check(r)[0], 0)

    def test_a_new_file_or_a_removed_one_is_not_a_tag_pr(self):
        r = self.repo()
        r.write("Tengoku/Seed/Logic/New.lean", tagged(PLAIN))
        r.commit("a new file")
        self.assertNotIn("class=tag", self.classify(r)[1])
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("only modifies existing modules", out)

    def test_a_generated_library_and_the_root_files_are_not_tagged_by_a_pr(self):
        r = self.repo()
        r.write("Tengoku/Lib/Basic.lean", tagged(PLAIN))
        r.commit("tags on a generated module")
        self.assertNotIn("class=tag", self.classify(r)[1])
        self.assertNotEqual(self.check(r)[0], 0)
        r2 = self.repo()
        r2.write("Tengoku/Seed.lean", tagged(PLAIN))
        r2.commit("tags on a root file")
        self.assertNotIn("class=tag", self.classify(r2)[1])
        self.assertNotEqual(self.check(r2)[0], 0)

    def test_a_file_that_is_not_utf8_is_not_a_tag_pr(self):
        r = self.repo()
        (r.dir / SEED).write_bytes(PLAIN.encode() + b"-- \xff\xfe\n")
        r.commit("bad bytes")
        self.assertNotIn("class=tag", self.classify(r)[1])

    def test_a_malformed_tag_is_refused(self):
        for bad in (
            TAG.replace("id=eq.0h2v.s4.05598c1b76c4", "id=nonsense"),
            TAG.replace(" vocab=fc0e7020", ""),
            TAG.replace("@isnad1", "@isnad2"),
            TAG + " extra=1",
            TAG.replace("shape=900bc7c0", "shape=zz"),
        ):
            r = self.repo()
            self.tag_pr(r, tag=bad)
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, bad)
            self.assertIn("tag PR:", out)

    def test_a_tag_that_claims_another_origin_is_refused(self):
        for path, tag in ((SEED, TRANSLATED), (SEED, NOVEL), (LIB, TAG), ("Tengoku/Native/Fx.lean", TAG)):
            r = self.repo()
            self.tag_pr(r, [path], tag)
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, (path, tag))
            self.assertIn("but the module is", out)

    def test_two_tags_in_one_docstring_are_refused(self):
        r = self.repo()
        r.write(SEED, tagged(PLAIN).replace(TAG, TAG + "\n" + TAG))
        r.commit("two tags")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("2 tag lines", out)

    def test_the_tag_is_the_last_line_of_its_docstring(self):
        r = self.repo()
        r.write(SEED, MULTILINE)
        r.commit("a two-line docstring in the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        r.write(SEED, MULTILINE.replace("First line.\n", f"First line.\n{TAG}\n"))
        r.commit("the tag in the middle")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("not the last line", out)

    def test_at_most_400_modules(self):
        r = self.repo()
        for i in range(401):
            r.write(f"Tengoku/Seed/Many/M{i}.lean", PLAIN)
        r.commit("401 modules in the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        for i in range(401):
            r.write(f"Tengoku/Seed/Many/M{i}.lean", tagged(PLAIN))
        r.commit("tags")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("at most 400", out)
        for i in range(400, 401):
            r.write(f"Tengoku/Seed/Many/M{i}.lean", PLAIN)
        r.commit("one less")
        self.assertEqual(self.check(r)[0], 0)

    def test_the_queue_builds_exactly_the_changed_modules(self):
        r = self.repo()
        self.tag_pr(r, [SEED, LIB])
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(ln for ln in out.split() if ln.startswith("Tengoku.")), ["Tengoku.FxLib.Fx.A", "Tengoku.Seed.Logic.Fx"])

    def test_a_tag_group_has_nothing_to_regenerate(self):
        r = self.repo()
        self.tag_pr(r)
        rc, out = r.gate("queue_targets.py", "main", "pr", "--regenerate")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.split() if ln.startswith("Tengoku.")], [])

    def test_the_gate_reads_main_not_the_pr(self):
        """tag_check imports isnad_tag from the checkout it lives in; a PR cannot supply a copy that makes anything equivalent (the gate runs on the base checkout)."""
        text = Path(tag_check.__file__).read_text()
        self.assertIn("Path(__file__).resolve().parent.parent", text)
        self.assertNotIn("TENGOKU_CI_ROOT", text)


class Verify(Setup):
    """tag_verify.py: a group that is not a tag group passes at once (it needs no Lean)."""

    def test_a_group_that_is_not_a_tag_group_is_left_alone(self):
        r = self.repo()
        r.write("scripts/x.py", "print(2)\n")
        r.commit("tooling")
        rc, out = r.gate("tag_verify.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("not a tag group", out)


class CheckTags(unittest.TestCase):
    """isnad.py check-tags: tagging the built modules again must change nothing (recs and ranges are what `tengoku-isnad` would print)."""

    MODULE = "Tengoku.Seed.Fx"

    def inputs(self, text, n=2):
        recs = [fake_record(f"t{k}", self.MODULE) for k in range(n)]
        lines = [range_line(i.name, {"range": i.rng, "sel": i.sel}, self.MODULE) for i in ranges_of(text, n)]
        return recs, lines

    def run_check(self, text):
        root = Path(tempfile.mkdtemp())
        path = isnad.module_file(self.MODULE, root)
        path.parent.mkdir(parents=True)
        path.write_text(text, encoding="utf-8")
        recs, lines = self.inputs(text)
        return isnad.check_tags(recs, lines, [self.MODULE], root)

    def right(self):
        """the module as the tagger leaves it, tags computed from the records themselves"""
        root = Path(tempfile.mkdtemp())
        path = isnad.module_file(self.MODULE, root)
        path.parent.mkdir(parents=True)
        path.write_text(PLAIN, encoding="utf-8")
        recs, lines = self.inputs(PLAIN)
        plan, _ = isnad.plan_tags(recs, lines)
        isnad.tag_files(plan, root, write=True)
        return path.read_text(encoding="utf-8")

    def test_a_module_tagged_with_the_builds_tags_passes(self):
        problems, summary = self.run_check(self.right())
        self.assertEqual(problems, [])
        self.assertIn("2 tags right", summary)

    def test_a_theorem_without_a_tag_is_reported(self):
        text = self.right()
        recs, lines = self.inputs(text)
        first = isnad.format_tag(recs[0], "seed")
        problems, _ = self.run_check(text.replace(first + "\n", "", 1).replace("\n-/\ntheorem t0", "\n-/\ntheorem t0", 1))
        self.assertTrue(any("have no tag" in p or "tag line(s)" in p for p in problems), problems)

    def test_a_tag_that_is_not_the_builds_is_reported(self):
        text = self.right()
        recs, _ = self.inputs(text)
        first = isnad.format_tag(recs[0], "seed")
        wrong = first.replace("id=", "id=x", 1) if False else first[:-1] + ("0" if first[-1] != "0" else "1")
        problems, _ = self.run_check(text.replace(first, wrong, 1))
        self.assertTrue(any("not the one the build computes" in p for p in problems), problems)

    def test_a_tag_on_something_that_is_no_theorem_is_reported(self):
        text = self.right() + "\n/-- A definition.\n" + TAG + "\n-/\ndef d := 1\n"
        problems, _ = self.run_check(text)
        self.assertTrue(any("belongs to no theorem" in p for p in problems), problems)

    def test_an_untagged_module_is_reported_as_missing_every_tag(self):
        problems, _ = self.run_check(PLAIN)
        self.assertTrue(any("have no tag" in p or "no docstring" in p for p in problems), problems)


if __name__ == "__main__":
    unittest.main()
