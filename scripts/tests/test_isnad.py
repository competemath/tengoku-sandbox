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
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

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
        # the isnad job's own block: other jobs of the file have a trigger step of their own (the first one in the file is not necessarily this job's)
        job = re.search(r"^  isnad:\n(.*?)(?=^  \S|\Z)", text, re.S | re.M)
        self.assertIsNotNone(job, "the isnad job was not found")
        m = re.search(r"grep -qE '(\^\(.*?\))' <<< \"\$files\"", job.group(1))
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


class Batches(unittest.TestCase):
    """One `tengoku-isnad` process over a whole 400-module tag part held the import closure of every module and the hosted runner was shut down for memory
    (exit 143, 'The runner has received a shutdown signal', three tag runs on 2026-10-15/16): the facts of a part come from one process per batch."""

    MODULES = [f"Tengoku.Lib.M{i}" for i in range(7)]

    def run_facts(self, batch, names=()):
        calls = []

        def fake_exe(args, exe=None, **_):
            calls.append(("recs", list(args)))
            return [f"rec:{a}" for a in args if a.startswith("Tengoku.")]

        def fake_lines(args, exe=None, **_):
            calls.append(("ranges", list(args)))
            return [f"range:{a}" for a in args if a.startswith("Tengoku.")]

        with mock.patch.object(isnad, "run_exe", fake_exe), mock.patch.object(isnad, "run_exe_lines", fake_lines):
            recs, ranges = isnad.facts(self.MODULES, list(names), None, batch)
        return recs, ranges, calls

    def test_seven_modules_in_batches_of_three_make_three_processes_per_kind(self):
        _, _, calls = self.run_facts(3)
        sizes = [sum(1 for a in args if a == "--module") for kind, args in calls if kind == "recs"]
        self.assertEqual(sizes, [3, 3, 1])
        self.assertEqual([k for k, _ in calls], ["recs", "ranges"] * 3)

    def test_the_batches_together_give_what_one_process_gives(self):
        recs, ranges, _ = self.run_facts(3)
        one_recs, one_ranges, _ = self.run_facts(100)
        self.assertEqual((recs, ranges), (one_recs, one_ranges))
        self.assertEqual(recs, [f"rec:{m}" for m in self.MODULES])
        self.assertEqual(ranges, [f"range:{m}" for m in self.MODULES])

    def test_the_names_filter_goes_to_every_batch_and_ranges_asks_for_the_same_modules(self):
        _, _, calls = self.run_facts(4, names=["foo"])
        self.assertTrue(all(args.count("--name") == 1 for _, args in calls))
        for (k1, a1), (k2, a2) in zip(calls[::2], calls[1::2]):
            self.assertEqual((k1, k2, a2[0], a2[1:]), ("recs", "ranges", "--ranges", a1))

    def test_a_batch_of_zero_or_less_means_one_process(self):
        for batch in (0, -5):
            _, _, calls = self.run_facts(batch)
            self.assertEqual(len(calls), 2)

    def test_both_commands_hand_their_batch_option_to_facts(self):
        seen = []

        def fake_facts(modules, names, exe, batch=None, exact=False, jobs=None):
            seen.append((list(modules), list(names), batch, exact, jobs))
            return [], []

        ap = isnad.build_parser()
        with (
            mock.patch.object(isnad, "facts", fake_facts),
            mock.patch.object(isnad, "plan_tags", lambda *a, **k: ({}, [])),
            mock.patch.object(isnad, "tag_files", lambda *a, **k: ({"added": 0, "replaced": 0, "same": 0, "created": 0}, [])),
            mock.patch.object(isnad, "check_tags", lambda *a, **k: ([], "")),
            mock.patch("builtins.print"),
        ):
            isnad.cmd_tag(ap.parse_args(["tag", "--module", "A", "--module", "B", "--name", "n", "--batch", "7"]))
            isnad.cmd_check_tags(ap.parse_args(["check-tags", "--module", "A", "--batch", "9", "--jobs", "2"]))
        self.assertEqual(
            seen,
            [(["A", "B"], ["n"], 7, True, isnad.JOBS), (["A"], [], 9, True, 2)],
            "the PR's modules are exactly the modules, and the batches run --jobs at a time (JOBS by default)",
        )

    def test_the_lane_runs_batches_in_parallel_by_default(self):
        self.assertGreater(isnad.JOBS, 1)
        for cmd in ("tag", "check-tags"):
            a = isnad.build_parser().parse_args([cmd, "--module", "A"])
            self.assertEqual(a.jobs, isnad.JOBS, cmd)

    # `--module A.B` selects by prefix: it reports the theorems of `A.B.C` too (derived-alg-geo-lean part 2, 3 Nov 2026: `Exponential.lean` beside `Exponential/Kernel.lean`)
    PARENT, CHILD = "Tengoku.Lib.Dir", "Tengoku.Lib.Dir.Kid"

    def prefix_selecting_exe(self):
        """A `tengoku-isnad` that selects by prefix as the real one does: the records and ranges of every theorem whose module has a listed module as a prefix."""
        theorems = {self.PARENT: ["p1"], self.CHILD: ["c1", "c2"], "Tengoku.Lib.Other": ["o1"]}

        def chosen(args):
            listed = [a for i, a in enumerate(args) if i and args[i - 1] == "--module"]
            return [(m, n) for m, ns in theorems.items() for n in ns if any(m == x or m.startswith(x + ".") for x in listed)]

        def fake_exe(args, exe=None, **_):
            return [isnad.Record("\t".join(["isnad1", n, m, "thm", "0", "0", "1", "c", "s", "v"])) for m, n in chosen(args)]

        def fake_lines(args, exe=None, **_):
            return ["\t".join(["isnad1-range", n, m, "1:0", "2:0", "1:8", "1:10"]) for m, n in chosen(args)]

        return fake_exe, fake_lines

    def facts_of(self, modules, batch, exact):
        fake_exe, fake_lines = self.prefix_selecting_exe()
        with mock.patch.object(isnad, "run_exe", fake_exe), mock.patch.object(isnad, "run_exe_lines", fake_lines):
            return isnad.facts(modules, [], None, batch, exact)

    def test_a_module_that_is_a_prefix_of_another_made_the_theorems_of_the_other_come_twice(self):
        recs, ranges = self.facts_of([self.PARENT, self.CHILD], 1, exact=False)
        self.assertEqual(sorted(r.name for r in recs).count("c1"), 2)
        self.assertEqual(sum(1 for ln in ranges if "\tc1\t" in ln), 2)

    def test_with_exact_every_theorem_comes_once_from_the_batch_that_lists_its_module(self):
        for batch in (1, 2, 100):
            recs, ranges = self.facts_of([self.PARENT, self.CHILD], batch, exact=True)
            want = sorted([(self.PARENT, "p1"), (self.CHILD, "c1"), (self.CHILD, "c2")])
            self.assertEqual(sorted((r.module, r.name) for r in recs), want, batch)
            self.assertEqual(len(ranges), 3, batch)

    def test_a_theorem_is_planned_for_tagging_when_its_module_has_a_parent_module_in_the_pr(self):
        recs, ranges = self.facts_of([self.PARENT, self.CHILD], 1, exact=True)
        plan, skipped = isnad.plan_tags(recs, ranges)
        self.assertEqual(sorted(plan), [self.PARENT, self.CHILD])
        self.assertEqual([it.name for it in plan[self.CHILD]], ["c1", "c2"])
        self.assertEqual(skipped, [])
        recs2, ranges2 = self.facts_of([self.PARENT, self.CHILD], 1, exact=False)
        plan2, skipped2 = isnad.plan_tags(recs2, ranges2)
        self.assertNotIn(
            self.CHILD, plan2, "main's behaviour: the child's theorems are 'the same name for two theorems' and the module is left untagged"
        )
        self.assertEqual(sorted(n for n, _ in skipped2), ["c1", "c1", "c2", "c2"])

    def test_a_listed_parent_alone_reports_only_its_own_theorems_with_exact(self):
        recs, _ = self.facts_of([self.PARENT], 100, exact=True)
        self.assertEqual([(r.module, r.name) for r in recs], [(self.PARENT, "p1")])

    # a theorem that two modules of one environment declare (same name and type, which Lean accepts) belongs to only one of them in that environment: grothendieck-riemann-roch
    # part 1, 3 Nov 2026, `Chow/ReesDepth.lean` has three theorems the tree's Seed has too, and in a batch it came out with no record
    SHADOWED, PARTLY, PLAIN, EMPTY = "Tengoku.Lib.Dup", "Tengoku.Lib.Part", "Tengoku.Lib.Plain", "Tengoku.Lib.Defs"
    DECLARED = {SHADOWED: {"s1", "s2"}, PARTLY: {"own", "dup"}, PLAIN: {"p1"}, EMPTY: set()}

    def shadowing_exe(self):
        calls = []

        def listed(args):
            return [a for i, a in enumerate(args) if i and args[i - 1] == "--module"]

        def rows(args):
            mods, alone = listed(args), len(listed(args)) == 1
            out = [(self.PLAIN, "p1")] if self.PLAIN in mods else []
            if self.SHADOWED in mods and alone:  # in a batch the other module of the environment holds these theorems
                out += [(self.SHADOWED, "s1"), (self.SHADOWED, "s2")]
            if self.PARTLY in mods:
                out += [(self.PARTLY, "own")] + ([(self.PARTLY, "dup")] if alone else [])
            return out

        def fake_exe(args, exe=None, **_):
            calls.append(("recs", listed(args)))
            return [isnad.Record("\t".join(["isnad1", n, m, "thm", "0", "0", "1", "c", "s", "v"])) for m, n in rows(args)]

        def fake_lines(args, exe=None, **_):
            calls.append(("ranges", listed(args)))
            return ["\t".join(["isnad1-range", n, m, "1:0", "2:0", "1:8", "1:10"]) for m, n in rows(args)]

        return fake_exe, fake_lines, calls

    def shadowed_facts(self, exact, declared=None):
        fake_exe, fake_lines, calls = self.shadowing_exe()
        mods = [self.SHADOWED, self.PARTLY, self.PLAIN, self.EMPTY]
        declared = self.DECLARED if declared is None else declared
        with (
            mock.patch.object(isnad, "run_exe", fake_exe),
            mock.patch.object(isnad, "run_exe_lines", fake_lines),
            mock.patch.object(isnad, "declared_theorem_names", lambda m, root=None: declared[m]),
        ):
            recs, ranges = isnad.facts(mods, [], None, 100, exact)
        return recs, ranges, calls

    def test_a_module_with_a_declared_theorem_and_no_record_in_the_batch_is_asked_again_alone(self):
        recs, ranges, calls = self.shadowed_facts(exact=True)
        got = sorted((r.module, r.name) for r in recs)
        self.assertIn((self.SHADOWED, "s1"), got)
        self.assertIn((self.SHADOWED, "s2"), got)
        self.assertEqual(sum(1 for ln in ranges if f"\t{self.SHADOWED}\t" in ln), 2)
        self.assertIn(("recs", [self.SHADOWED]), calls)
        self.assertIn(("ranges", [self.SHADOWED]), calls)

    def test_a_module_with_only_some_of_its_theorems_recorded_is_asked_again_and_gets_each_once(self):
        recs, ranges, calls = self.shadowed_facts(exact=True)
        part = sorted(r.name for r in recs if r.module == self.PARTLY)
        self.assertEqual(part, ["dup", "own"], "the retry replaces the batch's records of the module, it does not add to them")
        self.assertEqual(sum(1 for ln in ranges if f"\t{self.PARTLY}\t" in ln), 2)
        plan, skipped = isnad.plan_tags(recs, ranges)
        self.assertEqual(skipped, [])
        self.assertEqual(sorted(it.name for it in plan[self.PARTLY]), ["dup", "own"])

    def test_a_module_whose_declared_theorems_all_have_records_is_not_asked_again(self):
        _, _, calls = self.shadowed_facts(exact=True)
        alone = [m[0] for _, m in calls if len(m) == 1]
        self.assertNotIn(self.PLAIN, alone)
        self.assertNotIn(self.EMPTY, alone, "and a module that declares no theorem neither")

    def test_without_exact_the_batch_is_all_there_is(self):
        recs, _, calls = self.shadowed_facts(exact=False)
        self.assertEqual(sorted((r.module, r.name) for r in recs), sorted([(self.PLAIN, "p1"), (self.PARTLY, "own")]))
        self.assertEqual(len(calls), 2)

    def test_declared_theorem_names_reads_the_commands_of_the_source(self):
        import tempfile

        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Tengoku" / "Lib").mkdir(parents=True)
            cases = {
                "A": "import X\n/-- doc -/\ntheorem Foo.foo : True := trivial\nlemma bar (n : Nat) : True := trivial\n",
                "B": "@[simp] public theorem pub : True := trivial\nprotected noncomputable lemma nc : True := trivial\n",
                "C": "def f := 1\n-- a theorem in a comment\n/- theorem baz -/\nprivate lemma hidden : True := trivial\n",
                "D": "theorem eq_1 : True := trivial\ntheorem _aux : True := trivial\ntheorem «odd.name» : True := trivial\n",
            }
            for name, text in cases.items():
                (root / "Tengoku" / "Lib" / f"{name}.lean").write_text(text, encoding="utf-8")
            got = {n: isnad.declared_theorem_names(f"Tengoku.Lib.{n}", root) for n in (*cases, "Missing")}
        self.assertEqual(got, {"A": {"foo", "bar"}, "B": {"pub", "nc"}, "C": set(), "D": {"name"}, "Missing": set()})

    def test_a_module_or_theorem_name_that_is_not_a_lean_name_is_refused_before_any_process_runs(self):
        for bad in ("--import", "-x", "A B", "A;rm", "$(x)", "A\nB", "", ".A"):
            for modules, names in (([bad], []), (["Tengoku.Lib.M"], [bad])):
                fake = mock.Mock()
                with mock.patch.object(isnad, "run_exe", fake), mock.patch.object(isnad, "run_exe_lines", fake):
                    with self.assertRaises(SystemExit, msg=repr(bad)):
                        isnad.facts(modules, names, None, 25, True)
                fake.assert_not_called()

    def test_the_names_of_the_tree_pass_the_check(self):
        for ok in (
            "Tengoku.Lib.Foo",
            "Tengoku.Lib.«A-B».C",
            "Tengoku.Azurite.Azurite.UInt64.Equiv.Basic",
            "Nat.add_comm",
            "Foo.bar'",
            "Foo._private.x",
            "_root_.foo",
            "δ_apply",
            "ι_total_d",
            "ω₂_ne_zero",
        ):
            self.assertEqual(isnad.lean_name(ok), ok)

    def test_both_commands_take_a_batch_option_with_the_default(self):
        ap = isnad.build_parser()
        for cmd in ("tag", "check-tags"):
            self.assertEqual(ap.parse_args([cmd, "--module", "A"]).batch, isnad.BATCH)
            self.assertEqual(ap.parse_args([cmd, "--module", "A", "--batch", "7"]).batch, 7)


class BatchesInParallel(unittest.TestCase):
    """The batches of a part are independent processes: `jobs` of them run at a time (214 modules took 18 minutes one batch after the other on a 4-core runner), and the
    result is the one the serial run gives, in the order of the batches, whatever order they finish in."""

    MODULES = [f"Tengoku.Lib.M{i}" for i in range(10)]

    def facts_with(self, jobs, batch=2, delays=None, boom=None, exact=False):
        """`facts` over ten modules in batches of `batch`, through stand-ins for the two `tengoku-isnad` calls; returns (records, ranges, most processes at once, calls)."""
        lock = threading.Lock()
        state = {"now": 0, "most": 0, "calls": 0}
        delays = delays or {}

        def call(args):
            mods = [a for i, a in enumerate(args) if i and args[i - 1] == "--module"]
            with lock:
                state["now"] += 1
                state["calls"] += 1
                state["most"] = max(state["most"], state["now"])
            try:
                time.sleep(delays.get(mods[0], 0))
                if boom == mods[0]:
                    raise SystemExit(f"stand-in: {mods[0]} killed")
            finally:
                with lock:
                    state["now"] -= 1
            return mods

        def fake_exe(args, exe=None, **_):
            return [isnad.Record("\t".join(["isnad1", "t", m, "thm", "0", "0", "1", "c", "s", "v"])) for m in call(args)]

        def fake_lines(args, exe=None, **_):
            return ["\t".join(["isnad1-range", "t", m, "1:0", "2:0", "1:8", "1:10"]) for m in call(args[1:])]

        with mock.patch.object(isnad, "run_exe", fake_exe), mock.patch.object(isnad, "run_exe_lines", fake_lines):
            recs, ranges = isnad.facts(self.MODULES, [], None, batch, exact=exact, jobs=jobs)
        return [(r.module, r.name) for r in recs], ranges, state["most"], state["calls"]

    def test_the_result_is_the_serial_result_even_when_the_first_batches_finish_last(self):
        serial = self.facts_with(1)
        # the first batch is the slowest: a run that appended results as they came would put it last
        slow_first = self.facts_with(3, delays={self.MODULES[0]: 0.15, self.MODULES[2]: 0.08})
        self.assertEqual(serial[:2], slow_first[:2])
        self.assertEqual([m for m, _ in slow_first[0]], self.MODULES)
        self.assertEqual(serial[3], slow_first[3], "the same number of processes")

    def test_with_exact_the_parallel_result_is_the_serial_result_too(self):
        self.assertEqual(self.facts_with(1, exact=True)[:2], self.facts_with(4, exact=True)[:2])

    def test_batches_do_run_at_the_same_time_and_never_more_than_jobs(self):
        delays = {m: 0.05 for m in self.MODULES}  # every call waits a little, so that batches that run together overlap in time
        self.assertEqual(self.facts_with(1, delays=delays)[2], 1, "jobs=1 is one after the other")
        self.assertEqual(self.facts_with(3, delays=delays)[2], 3, "five batches, three at a time")
        self.assertEqual(self.facts_with(50, delays=delays)[2], 5, "never more than there are batches")

    def test_a_batch_that_stops_the_run_stops_it(self):
        for jobs in (1, 3):
            with self.assertRaises(SystemExit) as c:
                self.facts_with(jobs, boom=self.MODULES[4])
            self.assertIn(self.MODULES[4], str(c.exception))

    def test_one_batch_is_one_process_pair_whatever_jobs_says(self):
        self.assertEqual(self.facts_with(8, batch=100)[2:], (1, 2))


if __name__ == "__main__":
    unittest.main()
