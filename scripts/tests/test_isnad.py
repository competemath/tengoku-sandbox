"""scripts/isnad.py: the pure half of the identity (hashing, ids, tags, explanations, the golden file) and the commands around the Lean program
(with a stand-in for it). The Lean half is tested by `isnad.py laws` and `isnad.py selftest`, which need a Lean toolchain (CI: pr-tests, job isnad)."""

import hashlib
import importlib.util
import os
import re
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location("isnad", ROOT / "scripts" / "isnad.py")
isnad = importlib.util.module_from_spec(spec)
sys.modules["isnad"] = isnad
spec.loader.exec_module(isnad)

# What `tengoku-isnad` printed on Leak IV for Nat.add_comm (Lean 4.34.0-rc2): the canonical forms are the real ones
ADD_COMM_CANON = (
    '(Π "Nat" (Π "Nat" ("Eq"{(S 0)} "Nat" ("HAdd.hAdd"{0 0 0} "Nat" "Nat" "Nat" ("instHAdd"{0} "Nat" "instAddNat") v1 v0) '
    '("HAdd.hAdd"{0 0 0} "Nat" "Nat" "Nat" ("instHAdd"{0} "Nat" "instAddNat") v0 v1))))'
)
ADD_COMM_SHAPE = "(Π c0/0 (Π c0/0 (c0/3 c0/0 (c1/5 c0/0 c0/0 c0/0 v1 v0) (c2/5 c0/0 c0/0 c0/0 v0 v1))))"
ADD_COMM_VOCAB = '"HAdd.hAdd","Nat"'
ADD_COMM_LINE = "\t".join(
    ["isnad1", "Nat.add_comm", "Init.Data.Nat.Basic", "eq", "0", "2", "24", ADD_COMM_CANON, ADD_COMM_SHAPE, ADD_COMM_VOCAB]
)


class Hashing(unittest.TestCase):
    def test_sha_is_sha256_of_utf8(self):
        self.assertEqual(isnad.sha("abc", 12), hashlib.sha256(b"abc").hexdigest()[:12])
        self.assertEqual(isnad.sha("⊢", 8), hashlib.sha256("⊢".encode()).hexdigest()[:8])

    def test_the_golden_hash_of_a_real_canonical_form(self):
        # the canonical string of Nat.add_comm, hashed here, is the id that the golden file pins: Lean and Python agree
        r = isnad.Record(ADD_COMM_LINE)
        self.assertEqual(r.id, "eq.0h2v.s4.05598c1b76c4")

    def test_size_classes(self):
        self.assertEqual([isnad.size_class(n) for n in (1, 2, 3, 4, 15, 16, 24, 31, 32, 0)], [0, 1, 1, 2, 3, 4, 4, 4, 5, 0])

    def test_empty_vocabulary_is_the_hash_of_nothing(self):
        self.assertEqual(isnad.sha("", 8), "e3b0c442")  # the golden file has this vocab on every statement that names no object


class Record(unittest.TestCase):
    def test_fields(self):
        r = isnad.Record(ADD_COMM_LINE)
        self.assertEqual((r.name, r.module, r.kind, r.hyps, r.vars, r.nodes), ("Nat.add_comm", "Init.Data.Nat.Basic", "eq", 0, 2, 24))
        self.assertEqual((r.shape, r.vocab), ("900bc7c0", "fc0e7020"))  # the golden file's shape.vocab of Nat.add_comm

    def test_an_empty_last_field_is_kept(self):
        r = isnad.Record(ADD_COMM_LINE.rsplit("\t", 1)[0] + "\t")
        self.assertEqual(r.vocab, "e3b0c442")

    def test_refused(self):
        for bad in ("", "isnad2\ta\tb\tc\t0\t0\t1\tx\ty\tz", "isnad1\tonly\tfour", ADD_COMM_LINE + "\textra"):
            with self.assertRaises(ValueError, msg=bad):
                isnad.Record(bad)


class Tags(unittest.TestCase):
    TAG = "@isnad1 id=eq.1h3v.s4.01215b3d171d from=translated src=- shape=3fa9c1d2 vocab=b27e40a1"

    def test_roundtrip(self):
        r = isnad.Record(ADD_COMM_LINE)
        line = isnad.format_tag(r, "seed")
        self.assertEqual(line, f"@isnad1 id={r.id} from=seed src=0 shape={r.shape} vocab={r.vocab}")
        self.assertEqual(isnad.parse_tag(line)["id"], r.id)
        self.assertEqual(isnad.format_tag(r, "translated", "0123456789ab").split()[3], "src=0123456789ab")
        self.assertEqual(isnad.format_tag(r, "translated").split()[3], "src=-")  # a translation's source side is unknown unless said
        self.assertEqual(isnad.format_tag(r, "novel").split()[3], "src=0")

    def test_parse(self):
        t = isnad.parse_tag(self.TAG)
        self.assertEqual((t["version"], t["from"], t["src"]), ("1", "translated", "-"))

    def test_every_malformation_is_refused(self):
        bad = [
            self.TAG.replace("from=translated", "from=imported"),
            self.TAG.replace("src=-", "src=xyz"),
            self.TAG.replace("src=-", "src=0123456789a"),  # 11 digits
            self.TAG.replace("src=-", "src=0"),  # a translation has a source side
            self.TAG.replace("from=translated", "from=seed"),  # a seed theorem has none: src must be 0
            self.TAG.replace("from=translated", "from=novel"),
            self.TAG.replace("@isnad1", "@isnad2"),  # a recipe this tool does not implement
            self.TAG.replace("shape=3fa9c1d2", "shape=3fa9c1"),  # the 6-digit shape of the first sketch
            self.TAG.replace("id=eq.1h3v.s4.01215b3d171d", "id=eq.1h3v.s4.01215b3d171"),
            self.TAG.replace("id=eq.1h3v.s4.01215b3d171d", "id=Dvd.dvd.4h4v.s6.48e3ca7ba3f0"),  # a dot in the kind: the lab's old form
            self.TAG + " axioms=cpq",  # axioms are not in the tag
            self.TAG.replace(" vocab=b27e40a1", ""),
            self.TAG + " id=eq.1h3v.s4.01215b3d171d",
            "@isnad id=x",
            "isnad1 id=eq.1h3v.s4.01215b3d171d",
            self.TAG + "\n@isnad1 id=eq.1h3v.s4.01215b3d171d from=seed src=0 shape=3fa9c1d2 vocab=b27e40a1",
        ]
        for line in bad:
            with self.assertRaises(ValueError, msg=line):
                isnad.parse_tag(line)

    def test_a_tag_cannot_close_the_docstring(self):
        # the tag is one line of [a-z0-9=. -] and hex: no `-/`, no `/-`
        r = isnad.Record(ADD_COMM_LINE)
        line = isnad.format_tag(r, "translated", "-")
        self.assertNotIn("-/", line)
        self.assertNotIn("/-", line)
        self.assertRegex(line, r"^[ -~]+$")


class CraftedTags(unittest.TestCase):
    """A tag is read from a docstring, so it is untrusted text. Regression (SonarCloud, 2026-10-05): the first parser was a regex with nested repetition,
    `(?:[a-z]+=\\S+ ?)+`, and `@isnad1 id=x ` + `a=b` * 20 + a vertical tab took 3 s, `* 22` about 17 s, and sixty characters would hang the tool."""

    def parse_in_a_child(self, text: str, seconds: int = 5) -> str:
        code = "import sys; sys.path.insert(0, sys.argv[1]); import isnad\ntry:\n    isnad.parse_tag(sys.argv[2]); print('parsed')\nexcept ValueError: print('refused')"
        try:
            r = subprocess.run(
                [sys.executable, "-c", code, str(ROOT / "scripts"), text], capture_output=True, text=True, timeout=seconds, check=False
            )
        except subprocess.TimeoutExpired:
            self.fail(f"parse_tag did not finish in {seconds} s on a crafted tag of {len(text)} characters")
        return r.stdout.strip()

    def test_a_crafted_tag_is_refused_quickly(self):
        for n in (20, 64, 5000):
            self.assertEqual(self.parse_in_a_child("@isnad1 id=x " + "a=b" * n + "\x0bx=y"), "refused", n)

    def test_other_shapes_that_make_a_backtracking_parser_work_hard(self):
        for text in (
            "@isnad1 " + "a=" * 4000 + "!",
            "@isnad1 " + "a=b " * 4000 + "\t",
            "@isnad1 " + "=" * 100000,
            "@isnad1" + " " * 100000 + "x",
            "@isnad" + "9" * 100000,
            "@isnad1 id=" + "é" * 50000,
        ):
            self.assertEqual(self.parse_in_a_child(text), "refused", text[:30])

    def test_every_crafted_shape_is_refused_with_a_reason(self):
        good = Tags.TAG
        for bad in (
            good.replace(" ", "  ", 1),  # two spaces
            good + " ",  # a trailing space survives only strip(): still a tag
            "\t" + good.replace(" id=", "\tid=", 1),  # a tab inside
            good.replace("id=", "id=\x00"),  # a control character
            good.replace("from=translated", "from=translatéd"),  # non-ASCII
            "@isnad " + good.split(" ", 1)[1],  # no digits after @isnad
            "@isnad1",  # nothing after
            good + " extra",  # a token that is not key=value
            good.replace("id=", "id="),  # unchanged: control, must parse
        ):
            if bad.strip() == good:
                self.assertEqual(isnad.parse_tag(bad)["id"], "eq.1h3v.s4.01215b3d171d")
                continue
            with self.assertRaises(ValueError, msg=repr(bad)):
                isnad.parse_tag(bad)


class Explain(unittest.TestCase):
    def test_id(self):
        text = isnad.explain_id("eq.1h3v.s4.01215b3d171d")
        for part in ("an equation", "1 hypothesis ", "3 variables", "16 to 31", "01215b3d171d"):
            self.assertIn(part, text)

    def test_an_unknown_kind_is_a_head_name(self):
        self.assertIn("`dvd…`", isnad.explain_id("dvd.4h4v.s6.48e3ca7ba3f0"))

    def test_tag(self):
        text = isnad.explain_tag(Tags.TAG)
        for part in ("verified translation", "source side is not available", "shape=3fa9c1d2", "vocab=b27e40a1"):
            self.assertIn(part, text)
        same = isnad.explain_tag(Tags.TAG.replace("src=-", "src=01215b3d171d"))
        self.assertIn("kept exactly", same)
        self.assertIn("not available", isnad.explain_tag(Tags.TAG))
        self.assertIn("not a translation", isnad.explain_tag(Tags.TAG.replace("from=translated src=-", "from=novel src=0")))

    def test_garbage(self):
        with self.assertRaises(ValueError):
            isnad.explain_id("hello")


class Golden(unittest.TestCase):
    def test_the_file_is_well_formed(self):
        rows = isnad.golden()
        self.assertGreaterEqual(len(rows), 10)
        names = [r[1] for r in rows]
        self.assertEqual(len(names), len(set(names)))
        for mod, name, ident, sv in rows:
            self.assertRegex(mod, r"^Init(\.\w+)*$", "core modules only: the golden file must not depend on Mathlib or the tree")
            self.assertRegex(ident, isnad.ID_RE.pattern)
            self.assertRegex(sv, r"^[0-9a-f]{8}\.[0-9a-f]{8}$")

    def test_add_comm_is_pinned_to_the_hash_of_its_real_canonical_form(self):
        r = isnad.Record(ADD_COMM_LINE)
        row = next(x for x in isnad.golden() if x[1] == "Nat.add_comm")
        self.assertEqual(row[2], r.id)


class Commands(unittest.TestCase):
    """verify, id and selftest, with a stand-in for the Lean program (`lake env <exe>` is replaced by a script behind a fake `lake`)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        exe = self.dir / "fake-isnad"
        exe.write_text("#!/bin/sh\nprintf '%s\\n' \"$FAKE_OUT\"\n")
        lake = self.dir / "lake"
        lake.write_text('#!/bin/sh\nshift\nexec "$@"\n')  # `lake env <exe> args`
        for f in (exe, lake):
            f.chmod(f.stat().st_mode | stat.S_IEXEC)
        self.env = {**os.environ, "PATH": f"{self.dir}:{os.environ['PATH']}", "FAKE_OUT": ADD_COMM_LINE}
        self.exe = str(exe)

    def tearDown(self):
        self.tmp.cleanup()

    def run_cli(self, *args):
        return subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "isnad.py"), *args], capture_output=True, text=True, env=self.env, check=False
        )

    def test_id_prints_the_id_and_the_hashes(self):
        r = self.run_cli("id", "--module", "Init.Data.Nat.Basic", "--exe", self.exe)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("Nat.add_comm\teq.0h2v.s4.05598c1b76c4\tshape=", r.stdout)

    def test_verify_accepts_the_right_tag_and_refuses_a_forged_one(self):
        rec = isnad.Record(ADD_COMM_LINE)
        good = isnad.format_tag(rec, "seed")
        ok = self.run_cli("verify", good, "--module", "Init.Data.Nat.Basic", "--name", "Nat.add_comm", "--exe", self.exe)
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        self.assertIn("matches the compiled statement", ok.stdout)
        forged = good.replace(rec.id, "eq.0h2v.s4.000000000000")
        bad = self.run_cli("verify", forged, "--module", "Init.Data.Nat.Basic", "--name", "Nat.add_comm", "--exe", self.exe)
        self.assertEqual(bad.returncode, 1)
        self.assertIn("recomputed " + rec.id, bad.stdout)
        shape = self.run_cli(
            "verify", good.replace(f"shape={rec.shape}", "shape=00000000"), "--module", "M", "--name", "N", "--exe", self.exe
        )
        self.assertEqual(shape.returncode, 1)
        self.assertIn("shape:", shape.stdout)

    def test_explain_runs_offline(self):
        r = self.run_cli("explain", "eq.1h3v.s4.01215b3d171d")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("an equation", r.stdout)
        self.assertEqual(self.run_cli("explain", "garbage").returncode != 0, True)

    def test_selftest_reports_a_changed_recipe(self):
        # the stand-in answers every golden row with Nat.add_comm's record: the row of Nat.add_comm passes, every other one is reported
        r = self.run_cli("selftest", "--exe", self.exe)
        self.assertEqual(r.returncode, 1)
        self.assertIn("FAIL Nat.mul_comm", r.stdout)
        self.assertNotIn("FAIL Nat.add_comm", r.stdout)
        self.assertIn("the recipe or the toolchain changed", r.stdout)


class CiJob(unittest.TestCase):
    """The pr-tests job `isnad` runs only when a file of the recipe changes: the list must cover every file the job depends on, the workflow file included
    (CodeRabbit, 2026-10-05: a later PR that changed only the job's steps would have set run=no and never run them)."""

    def trigger(self) -> re.Pattern:
        text = (ROOT / ".github" / "workflows" / "pr-tests.yml").read_text(encoding="utf-8")
        m = re.search(r"grep -qE '(\^\(.*?\))' <<< \"\$files\"", text)
        self.assertIsNotNone(m, "the touched step of the isnad job was not found")
        return re.compile(m.group(1))

    def test_every_file_the_job_depends_on_triggers_it(self):
        rx = self.trigger()
        for path in (
            "TengokuIsnad.lean",
            "lakefile.toml",
            "lean-toolchain",
            "scripts/isnad.py",
            "scripts/isnad_tag.py",
            "tools/isnad/golden.tsv",
            "tools/isnad/tagger/Fixture.lean",
            "tools/isnad/tagger/ranges.json",
            "tools/isnad/laws_body.lean",
            "docs/isnad.md",
            ".github/workflows/pr-tests.yml",
        ):
            self.assertRegex(path, rx, path)

    def test_unrelated_files_do_not_trigger_it(self):
        rx = self.trigger()
        for path in (
            "scripts/seed.py",
            "Tengoku/Seed/Logic/Basic.lean",
            "data/staging/x.jsonl",
            ".github/workflows/pr-gate.yml",
            "docs/testing.md",
        ):
            self.assertNotRegex(path, rx, path)


class LawsCommand(unittest.TestCase):
    """`laws` hands the script to Lean on stdin (no file, no path: a path built from anything is what a security scan flags), and says so when it fails."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        d = Path(self.tmp.name)
        lake = d / "lake"
        # a stand-in for `lake env lean --stdin`: it succeeds, and reports, only when the script arrives on stdin
        lake.write_text(
            '#!/bin/sh\nif [ "$3" = "--stdin" ] && grep -q "#isnad_laws" -; then echo "isnad laws: 21 checks passed"; else echo "no script on stdin" >&2; exit 1; fi\n'
        )
        lake.chmod(lake.stat().st_mode | stat.S_IEXEC)
        self.env = {**os.environ, "PATH": f"{d}:{os.environ['PATH']}"}

    def tearDown(self):
        self.tmp.cleanup()

    def test_the_script_arrives_on_stdin(self):
        r = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "isnad.py"), "laws"], capture_output=True, text=True, env=self.env, check=False
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("21 checks passed", r.stdout)

    def test_a_failure_of_lean_is_a_failure_of_the_command(self):
        (Path(self.tmp.name) / "lake").write_text("#!/bin/sh\necho 'error: boom' >&2; exit 1\n")
        r = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "isnad.py"), "laws"], capture_output=True, text=True, env=self.env, check=False
        )
        self.assertEqual(r.returncode, 1)
        self.assertIn("boom", r.stdout)


class Laws(unittest.TestCase):
    def test_the_laws_script_embeds_the_canonicaliser_itself(self):
        script = isnad.laws_script()
        self.assertTrue(script.startswith("import Lean\n"))
        self.assertIn("partial def ser ", script)
        self.assertIn("#isnad_laws", script)
        self.assertNotIn("def main", script)  # the executable's entry point is not part of the checked code
        self.assertNotIn("importModules", script)


if __name__ == "__main__":
    unittest.main()
