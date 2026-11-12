"""Born tagged: the lanes that put new theorems into the tree by themselves (studied, intake) carry their isnad tags in the PR itself
(scripts/ci/born_tagged.py, tag_verify.py; docs/isnad.md, "Born tagged"). Its own file, like test_studied_class.py."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
TREE = HERE.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(TREE / "scripts"))
import isnad_tag as tg  # noqa: E402
import test_studied_class as sct  # noqa: E402
from test_gates import Repo  # noqa: E402

NOVEL = "@isnad1 id=eq.0h2v.s4.05598c1b76c4 from=novel src=0 shape=900bc7c0 vocab=fc0e7020"
SEED = NOVEL.replace("from=novel", "from=seed")
TRANSLATED = NOVEL.replace("from=novel", "from=translated").replace("src=0", "src=-")


def tagged_lean(n: int, tag: str = NOVEL, doc: str = "Adds a numeral on either side.") -> str:
    """a studied module as the tagger leaves it: the tag is the last line of the theorem's docstring"""
    return sct.lean(n, f"/--\n{doc}\n{tag}\n-/\ntheorem lemma_{n} (a : Nat) : a + {n} = {n} + a := by\n  omega\n")


class Studied(unittest.TestCase):
    base = sct.Studied.base
    bundle = sct.Studied.bundle

    def tag_all(self, r: Repo, ns: list[int], tag: str = NOVEL) -> None:
        for n in ns:
            r.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(n)[:12]}.lean", tagged_lean(n, tag))
        r.commit("tags")

    def run_gate(self, r: Repo, env: dict | None = None):
        return r.gate("born_tagged.py", env=env)

    def test_an_untagged_studied_pr_is_refused_and_a_tagged_one_passes(self):
        r = self.base()
        self.bundle(r)
        rc, out = self.run_gate(r)
        self.assertNotEqual(rc, 0, out)
        self.assertIn("is not born tagged", out)
        self.assertIn("has no isnad tag", out)
        self.tag_all(r, [1, 2])
        rc, out = self.run_gate(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("born tagged ok: 2 module(s) of a studied PR", out)

    def test_the_autotag_workflow_runs_the_lanes_gate_with_the_tags_pending(self):
        r = self.base()
        self.bundle(r)
        rc, out = self.run_gate(r, env={"ISNAD_TAGS_PENDING": "1"})
        self.assertEqual(rc, 0, out)
        self.assertIn("tags pending", out)

    def test_every_module_needs_its_own_tags(self):
        r = self.base()
        self.bundle(r)
        r.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean", tagged_lean(1))
        r.commit("one tagged")
        rc, out = self.run_gate(r)
        self.assertNotEqual(rc, 0, out)
        self.assertIn(f"S{sct.entry_id(2)[:12]}.lean", out)
        self.assertNotIn(f"S{sct.entry_id(1)[:12]}.lean: the theorem", out)

    def test_the_theorem_the_manifest_names_carries_the_tag(self):
        r = self.base()
        self.bundle(r, [1])
        helper_tagged = sct.lean(
            1,
            f"/--\nA helper.\n{NOVEL}\n-/\ntheorem helper_1 : True := trivial\n\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n",
        )
        r.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean", helper_tagged)
        r.commit("a tag on the helper only")
        rc, out = self.run_gate(r)
        self.assertNotEqual(rc, 0, out)
        self.assertIn("the theorem lemma_1 has no isnad tag", out)

    def test_a_tag_must_be_well_formed_from_the_modules_place_and_last_in_its_docstring(self):
        for tag, why in (
            (SEED, "from=seed but the module is novel content"),
            ("@isnad1 id=eq.0h2v.s4 from=novel", "exactly the fields"),
            (NOVEL.replace("@isnad1", "@isnad9"), "isnad format 9"),
        ):
            r = self.base()
            self.bundle(r, [1])
            self.tag_all(r, [1], tag)
            rc, out = self.run_gate(r)
            self.assertNotEqual(rc, 0, f"{tag}: {out}")
            self.assertIn(why, out)
        r = self.base()
        self.bundle(r, [1])
        r.write(
            f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean",
            sct.lean(1, f"/--\n{NOVEL}\nAnd then some words.\n-/\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n"),
        )
        r.commit("the tag is not last")
        rc, out = self.run_gate(r)
        self.assertNotEqual(rc, 0, out)
        self.assertIn("not the last line of its docstring", out)

    def test_two_tags_in_one_docstring_are_refused(self):
        r = self.base()
        self.bundle(r, [1])
        r.write(
            f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean",
            sct.lean(1, f"/--\nWords.\n{NOVEL}\n{NOVEL}\n-/\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n"),
        )
        r.commit("two tags")
        rc, out = self.run_gate(r)
        self.assertNotEqual(rc, 0, out)
        self.assertIn("2 tag lines", out)

    def test_other_prs_are_not_judged(self):
        r = Repo()
        r.write("scripts/x.py", "print(2)\n")
        r.commit("tooling")
        rc, out = self.run_gate(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("not a lane PR", out)

    # ---- the provenance of the bundle is the content, not the tags ----------------------------------------------------------------------------

    def archive(self, r: Repo) -> str:
        rc, out = r.gate("studied_check.py", "main", "pr", "--tar", str(Path(r.dir) / "bundle.tar"))
        self.assertEqual(rc, 0, out)
        m = re.search(r"archive rebuilt: \S+ sha256 ([0-9a-f]{64})", out)
        self.assertTrue(m, out)
        return m.group(1)

    def test_the_archive_the_intake_job_attested_is_the_pr_in_its_canonical_form(self):
        plain = self.base()
        self.bundle(plain, [1, 2])
        for n in (1, 2):  # the same words as the tagged module's docstring, without the tag
            plain.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(n)[:12]}.lean", tagged_lean(n).replace(f"{NOVEL}\n", ""))
        plain.commit("docstrings")
        tagged = self.base()
        self.bundle(tagged, [1, 2])
        self.tag_all(tagged, [1, 2])
        # the tagged PR is not the plain one's bytes, and its archive is
        self.assertNotEqual(
            (Path(plain.dir) / f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean").read_text(),
            (Path(tagged.dir) / f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean").read_text(),
        )
        self.assertEqual(self.archive(plain), self.archive(tagged))

    def test_a_changed_theorem_still_changes_the_archive(self):
        a = self.base()
        self.bundle(a, [1])
        b = self.base()
        self.bundle(b, [1])
        r = b
        r.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean", tagged_lean(1).replace("omega", "simp [Nat.add_comm]"))
        r.commit("a different proof, tagged")
        self.assertNotEqual(self.archive(a), self.archive(b))


class Intake(unittest.TestCase):
    """The intake lane is judged only when TENGOKU_ISNAD_REQUIRED is 1 (its tagging stage is live)."""

    def repo(self, tagged: bool, umbrella: bool = True) -> Repo:
        r = Repo()
        body = "theorem t0 : 1 + 1 = 2 := rfl\n"
        if tagged:
            body = f"/--\nOne and one.\n{TRANSLATED}\n-/\n" + body
        r.write("Tengoku/FxLib/Fx/A.lean", "import Tengoku\n\n" + body)
        if umbrella:
            r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.A\n")
        r.write(
            "data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "Fx.a", "module": "Tengoku.FxLib.Fx.A", "library": "fx-lib"}) + "\n"
        )
        r.commit("a library arrives")
        return r

    def test_not_required_until_the_variable_says_so(self):
        rc, out = self.repo(False).gate("born_tagged.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("not required yet", out)

    def test_required_an_untagged_module_is_refused_and_a_tagged_one_passes(self):
        rc, out = self.repo(False).gate("born_tagged.py", env={"TENGOKU_ISNAD_REQUIRED": "1"})
        self.assertNotEqual(rc, 0, out)
        self.assertIn("declares theorems and carries no isnad tag", out)
        self.assertNotIn("FxLib.lean", out, "the umbrella file only imports: it is not judged")
        rc, out = self.repo(True).gate("born_tagged.py", env={"TENGOKU_ISNAD_REQUIRED": "1"})
        self.assertEqual(rc, 0, out)
        self.assertIn("1 module(s) of a intake PR", out)

    def test_a_translated_module_may_not_claim_another_origin(self):
        r = self.repo(True)
        r.write("Tengoku/FxLib/Fx/A.lean", "import Tengoku\n\n" + f"/--\nOne and one.\n{SEED}\n-/\ntheorem t0 : 1 + 1 = 2 := rfl\n")
        r.commit("claims the seed")
        rc, out = r.gate("born_tagged.py", env={"TENGOKU_ISNAD_REQUIRED": "1"})
        self.assertNotEqual(rc, 0, out)
        self.assertIn("from=seed but the module is translated content", out)

    def test_a_module_whose_theorems_the_tagger_leaves_out_by_name_needs_no_tag(self):
        """TengokuIsnad.lean okName leaves out eq_*, proof_*, match_*, sizeOf_*, _* and injEq: `UInt64.eq_of_toNat_eq` is a lemma the tagger never sees (azurite part 1)"""

        def verdict(body: str):
            r = Repo()
            r.write("Tengoku/FxLib/Fx/A.lean", "import Tengoku\n\n" + body)
            r.write(
                "data/intake/fx-lib/manifest.jsonl",
                json.dumps({"name": "Fx.a", "module": "Tengoku.FxLib.Fx.A", "library": "fx-lib"}) + "\n",
            )
            r.commit("a library arrives")
            return r.gate("born_tagged.py", env={"TENGOKU_ISNAD_REQUIRED": "1"})

        rc, out = verdict("lemma UInt64.eq_of_toNat_eq (x y : Nat) (h : x = y) : x = y := h\n")
        self.assertEqual(rc, 0, out)
        rc, out = verdict("theorem eq_two : 1 + 1 = 2 := rfl\ntheorem proof_x : True := trivial\n")
        self.assertEqual(rc, 0, out)
        rc, out = verdict("theorem eq_two : 1 + 1 = 2 := rfl\ntheorem add_two : 1 + 1 = 2 := rfl\n")
        self.assertNotEqual(rc, 0, out)
        self.assertIn("declares theorems and carries no isnad tag", out)
        rc, out = verdict("theorem «a.eq_x» : 1 + 1 = 2 := rfl\n")
        self.assertNotEqual(rc, 0, "«a.eq_x» is one component named a.eq_x: the tagger sees it, so it needs a tag")
        rc, out = verdict("theorem _root_.foo : 1 + 1 = 2 := rfl\n")
        self.assertNotEqual(rc, 0, "_root_.foo declares foo, which the tagger sees: it needs a tag")
        rc, out = verdict("theorem _root_.eq_foo : 1 + 1 = 2 := rfl\n")
        self.assertEqual(rc, 0, out)
        rc, out = verdict("theorem Foo._bar.baz : 1 + 1 = 2 := rfl\n")
        self.assertEqual(rc, 0, out)  # a component starting with an underscore makes the name internal
        rc, out = verdict("theorem equal_two : 1 + 1 = 2 := rfl\n")
        self.assertNotEqual(rc, 0, "a name that only starts like eq (equal_two) is a real theorem")

    def test_a_module_without_theorems_needs_no_tag(self):
        r = Repo()
        r.write("Tengoku/FxLib/Fx/A.lean", "import Tengoku\n\ndef one : Nat := 1\n")
        r.write(
            "data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "Fx.a", "module": "Tengoku.FxLib.Fx.A", "library": "fx-lib"}) + "\n"
        )
        r.commit("a library of definitions")
        rc, out = r.gate("born_tagged.py", env={"TENGOKU_ISNAD_REQUIRED": "1"})
        self.assertEqual(rc, 0, out)


class Verify(unittest.TestCase):
    """The queue's step (tag_verify.py) asks for the tags of the same groups."""

    def modules(self, r: Repo, env: dict | None = None) -> list[str]:
        import os

        code = "import tag_verify; print('\\n'.join(tag_verify.group_modules('main', 'pr')))"
        p = subprocess.run(
            [sys.executable, "-c", code],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "PYTHONPATH": str(HERE.parent), "TENGOKU_CI_ROOT": str(r.dir), **(env or {})},
        )
        self.assertEqual(p.returncode, 0, p.stderr)
        return [ln for ln in p.stdout.splitlines() if ln]

    def test_a_studied_group_is_verified_always(self):
        s = Studied()
        r = s.base()
        s.bundle(r, [1, 2])
        self.assertEqual(self.modules(r), [sct.mod_of(1), sct.mod_of(2)])

    def test_an_intake_group_only_when_required(self):
        r = Intake().repo(True)
        self.assertEqual(self.modules(r), [])
        self.assertEqual(self.modules(r, {"TENGOKU_ISNAD_REQUIRED": "1"}), ["Tengoku.FxLib.Fx.A"])

    def test_other_groups_are_left_alone(self):
        r = Repo()
        r.write("scripts/x.py", "print(3)\n")
        r.commit("tooling")
        self.assertEqual(self.modules(r), [])


class Canonical(unittest.TestCase):
    def test_a_module_and_the_same_module_with_its_tags_have_one_canonical_form(self):
        """the tagger moves a one-line docstring's closing `-/` onto its own line, which stripping the tag cannot undo; the canonical form does not see the difference"""
        for doc in ("/-- Words. -/", "/--\nWords.\n-/", "/--   Words.   -/", "/-- Two\nlines. -/", "/-- Words.-/"):
            new, _ = tg.with_tag(doc, NOVEL, "")
            old_text, new_text = f"{doc}\ntheorem a : True := trivial\n", f"{new}\ntheorem a : True := trivial\n"
            self.assertEqual(tg.canonical_text(old_text), tg.canonical_text(new_text), doc)
            self.assertTrue(tg.equivalent(old_text, new_text))
        self.assertNotEqual(
            tg.canonical_text("/-- Words. -/\ntheorem a : True := trivial\n"),
            tg.canonical_text("/-- Other words. -/\ntheorem a : True := trivial\n"),
        )
        self.assertNotEqual(tg.canonical_text("theorem a : True := trivial\n"), tg.canonical_text("theorem a : 1 = 1 := rfl\n"))

    def test_canonical_equality_is_what_equivalent_judges(self):
        a = "/-- Words. -/\ntheorem a : True := trivial\n"
        for b in (a, a.replace("Words. ", "Words.\n"), a.replace("trivial", "by trivial"), a.replace("Words", "Other")):
            self.assertEqual(tg.equivalent(a, b), tg.canonical_text(a) == tg.canonical_text(b), b)


class Strip(unittest.TestCase):
    def test_taking_the_tags_out_of_a_tagger_made_module_gives_back_the_original_bytes(self):
        original = sct.lean(1)
        self.assertEqual(tg.strip_text(tagged_lean(1)), tagged_lean(1).replace(f"{NOVEL}\n", ""))
        self.assertEqual(tg.strip_text(original), original)
        created = original.replace(
            "theorem lemma_1", f"/--\n{NOVEL}\n-/\ntheorem lemma_1"
        )  # the tagger's own docstring, made for a theorem that had none
        self.assertEqual(tg.strip_text(created), original)


if __name__ == "__main__":
    unittest.main()
