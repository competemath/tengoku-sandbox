"""scripts/lake_cache.py: which deltas a group restores, which mappings it stages, which modules it compiled without being asked to.

The fixtures are the shapes seen on a runner (sandbox runs 38454271037, 38455481612, 2026-10-13): a mappings file whose line 1 is the header
`"2026-03-17"`, a build log with `✔ [8804/8804] Built Tengoku.Probe.Hello (3.5s)` and `⚠ [8802/9938] Replayed Tengoku.X` lines."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "lake_cache.py"
sys.path.insert(0, str(SCRIPT.parent))

import lake_cache as lc  # noqa: E402

A, B, C, D = ("a" * 40, "b" * 40, "c" * 40, "d" * 40)
HEADER = '"2026-03-17"'


def run(*args: str, files: dict[str, str] | None = None, cwd: str | None = None) -> subprocess.CompletedProcess:
    """The CLI in a scratch workspace that holds `files` under the workspace's fixed names (the CLI takes no path)."""
    with tempfile.TemporaryDirectory() as d:
        for name, text in (files or {}).items():
            p = Path(d) / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return subprocess.run([sys.executable, str(SCRIPT), *args], capture_output=True, text=True, cwd=cwd or d)


class Plan(unittest.TestCase):
    def test_the_deltas_of_the_merges_since_the_base_come_oldest_first(self):
        assets = [f"d-{A}.tar.zst", f"d-{B}.tar.zst", f"d-{C}.tar.zst"]  # the release lists them in any order
        # the order of the history, not of the names: commit ids carry no order
        self.assertEqual(lc.plan([C, A, B], assets), [f"d-{C}.tar.zst", f"d-{A}.tar.zst", f"d-{B}.tar.zst"])

    def test_a_merge_that_published_nothing_is_skipped_not_an_error(self):
        # a tooling-only group has no new mapping, a failed upload leaves none: Lake compiles what it cannot restore
        self.assertEqual(lc.plan([A, B, C], [f"d-{A}.tar.zst", f"d-{C}.tar.zst"]), [f"d-{A}.tar.zst", f"d-{C}.tar.zst"])

    def test_a_delta_of_a_commit_that_is_not_between_base_and_head_is_never_applied(self):
        # an orphan of a group that was rebuilt, or of a branch that never reached main
        self.assertEqual(lc.plan([A], [f"d-{A}.tar.zst", f"d-{D}.tar.zst"]), [f"d-{A}.tar.zst"])

    def test_only_asset_names_of_the_delta_shape_count(self):
        names = [
            "base.jsonl",
            f"d-{A}.tar.zst.sig",
            f"d-{A[:-1]}.tar.zst",
            f"d-{A.upper()}.tar.zst",
            "d-" + A + ".tar.zst/../x",
            f"x-d-{A}.tar.zst",
        ]
        self.assertEqual(lc.plan([A], names), [])


class Diff(unittest.TestCase):
    def test_the_header_stays_line_one_and_known_mappings_go(self):
        out = [HEADER, '{"i":1}', '{"i":2}', '{"i":3}']
        self.assertEqual(lc.diff(out, {HEADER, '{"i":1}', '{"i":3}'}), [HEADER, '{"i":2}'])

    def test_the_header_is_kept_even_when_the_base_has_it(self):
        # the first version of the workflow dropped it with the other known lines: stage warned "invalid header on line 1: expected date" and staged nothing
        self.assertEqual(lc.diff([HEADER, '{"i":9}'], {HEADER})[0], HEADER)

    def test_nothing_new_leaves_only_the_header(self):
        self.assertEqual(lc.diff([HEADER, '{"i":1}'], {'{"i":1}'}), [HEADER])

    def test_a_mapping_listed_twice_is_staged_once(self):
        self.assertEqual(lc.diff([HEADER, '{"i":5}', '{"i":5}'], set()), [HEADER, '{"i":5}'])

    def test_an_empty_file_is_an_error_not_an_empty_delta(self):
        with self.assertRaises(ValueError):
            lc.diff([], set())

    def test_the_command_reads_the_fixed_files_and_ignores_blank_lines_and_crlf(self):
        files = {
            "out-all.jsonl": f'{HEADER}\r\n{{"i":1}}\r\n\r\n{{"i":2}}\r\n{{"i":3}}\r\n',
            ".lake/deltas-had.jsonl": f'{HEADER}\n{{"i":1}}\n',
        }
        with tempfile.TemporaryDirectory() as d:
            for name, text in files.items():
                p = Path(d) / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(text)
            r = subprocess.run([sys.executable, str(SCRIPT), "diff"], cwd=d, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual(json.loads(r.stdout), {"build": 3, "known": 1, "new": 2})
            self.assertEqual((Path(d) / "out-new.jsonl").read_text(), f'{HEADER}\n{{"i":2}}\n{{"i":3}}\n')

    def test_a_workspace_without_a_store_yet_knows_nothing(self):
        r = run("diff", files={"out-all.jsonl": f'{HEADER}\n{{"i":1}}\n'})
        self.assertEqual((r.returncode, json.loads(r.stdout)["new"]), (0, 1), r.stderr)


class NoPaths(unittest.TestCase):
    """Nothing typed on the command line becomes a path or a process argument: the CLI refuses every path-like option."""

    def test_every_option_that_used_to_take_a_path_is_refused(self):
        for args in (
            ["diff", "--out", "x"],
            ["diff", "--had", "x"],
            ["diff", "--to", "x"],
            ["diff", "--with-computed-base"],
            ["check", "--targets", "x"],
            ["check", "--log", "x"],
            ["pack", "--out", "x"],
            ["pack", "--new", "x"],
            ["pack", "--rev", "a" * 40],
            ["plan"],
        ):
            r = run(*args)
            self.assertEqual(r.returncode, 2, (args, r.stdout, r.stderr))
            self.assertIn("usage:", r.stderr)


class Check(unittest.TestCase):
    LOG = (
        "✔ [8803/8804] Built Tengoku.Pfr.Basic (1.2s)\n"
        "⚠ [8802/9938] Replayed Tengoku.LerayHopf.LerayHopf.Bochner.StepFunctionCompactness\n"
        "⚠ [8804/8804] Built Tengoku.Probe.Hello (4.1s)\n"
        "Build completed successfully (8804 jobs).\n"
    )

    def test_a_replayed_module_is_not_a_compiled_one(self):
        self.assertEqual(lc.compiled(self.LOG), {"Tengoku.Pfr.Basic", "Tengoku.Probe.Hello"})

    def test_modules_compiled_without_being_asked_to_are_the_misses(self):
        r = run("check", files={"targets-only.txt": "Tengoku.Probe.Hello\n", "build.log": self.LOG})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(json.loads(r.stdout), {"targets": 1, "changed": 0, "compiled": 2, "misses": 1, "first": ["Tengoku.Pfr.Basic"]})

    def test_fail_makes_a_miss_an_error_and_a_clean_build_is_not(self):
        bad = run("check", "--fail", files={"targets-only.txt": "Tengoku.Probe.Hello\n", "build.log": self.LOG})
        ok = run("check", "--fail", files={"targets-only.txt": "Tengoku.Probe.Hello\nTengoku.Pfr.Basic\n", "build.log": self.LOG})
        self.assertEqual((bad.returncode, ok.returncode), (1, 0))

    def test_a_log_that_built_nothing_is_a_clean_build(self):
        r = run(
            "check",
            "--fail",
            files={"targets-only.txt": "Tengoku.Probe.Hello\n", "build.log": "Build completed successfully (8804 jobs).\n"},
        )
        self.assertEqual((r.returncode, json.loads(r.stdout)["compiled"]), (0, 0))


def git(cwd, *args):
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()


class CheckChangedModules(unittest.TestCase):
    """A module the group changed is compiled legitimately, and so is every module that imports it: only a compile of anything else is a restore
    that missed. The first version counted every module outside the targets: on the first real group (a promotion, 2026-10-14) the changed module
    itself was the 'miss', and strict mode would have removed the group from the queue."""

    def test_the_module_a_file_is_(self):
        self.assertEqual(lc.module_of("Tengoku/A/B.lean"), "Tengoku.A.B")
        self.assertEqual(lc.module_of("Tengoku.lean"), "Tengoku")
        self.assertIsNone(lc.module_of("scripts/x.lean"))
        self.assertIsNone(lc.module_of("Tengoku/A/B.md"))

    def test_downstream_is_the_changed_modules_and_everything_that_imports_them_however_far(self):
        graph = {"T.B": ["T.A"], "T.C": ["T.B"], "T.D": ["T.Other"], "T.A": []}
        self.assertEqual(lc.downstream({"T.A"}, graph), {"T.A", "T.B", "T.C"})
        self.assertEqual(lc.downstream(set(), graph), set())

    def test_imports_are_read_from_the_import_lines_of_the_files(self):
        self.assertEqual(
            lc.imports_of("import Mathlib\nimport Tengoku.A\n  import Not.Counted\n/- import In.Comment -/\nimport Tengoku.B  -- x\n"),
            ["Mathlib", "Tengoku.A", "Tengoku.B"],
        )

    def repo(self, d):
        git(d, "init", "-q", "-b", "main")
        git(d, "config", "user.email", "t@example.invalid")
        git(d, "config", "user.name", "t")
        for name, text in {
            "Tengoku/A.lean": "import Mathlib\n",
            "Tengoku/B.lean": "import Tengoku.A\n",
            "Tengoku/C.lean": "import Mathlib\n",
            "Tengoku.lean": "import Tengoku.B\nimport Tengoku.C\n",
        }.items():
            (Path(d) / name).parent.mkdir(parents=True, exist_ok=True)
            (Path(d) / name).write_text(text)
        git(d, "add", "-A")
        git(d, "commit", "-qm", "base")
        base = git(d, "rev-parse", "HEAD")
        (Path(d) / "Tengoku/A.lean").write_text("import Mathlib\n-- changed\n")
        git(d, "commit", "-qam", "group")
        return base

    def check(self, d, base, built, targets="Tengoku\n", *args):
        (Path(d) / "targets-only.txt").write_text(targets)
        (Path(d) / "build.log").write_text("".join(f"✔ [1/2] Built {m} (1.0s)\n" for m in built))
        env = {**__import__("os").environ, "BASE": base} if base else {k: v for k, v in __import__("os").environ.items() if k != "BASE"}
        return subprocess.run([sys.executable, str(SCRIPT), "check", *args], cwd=d, capture_output=True, text=True, env=env)

    def test_the_changed_module_and_its_importers_are_not_misses_and_an_unrelated_compile_is(self):
        with tempfile.TemporaryDirectory() as d:
            base = self.repo(d)
            ok = self.check(d, base, ["Tengoku.A", "Tengoku.B", "Tengoku"], "Tengoku\n", "--fail")
            self.assertEqual((ok.returncode, json.loads(ok.stdout)["misses"]), (0, 0), ok.stdout + ok.stderr)
            bad = self.check(d, base, ["Tengoku.A", "Tengoku.B", "Tengoku.C"], "Tengoku\n", "--fail")
            self.assertEqual(bad.returncode, 1)
            self.assertEqual(json.loads(bad.stdout)["first"], ["Tengoku.C"])

    def test_without_the_groups_base_every_compile_outside_the_targets_is_a_miss(self):
        with tempfile.TemporaryDirectory() as d:
            self.repo(d)
            r = self.check(d, "", ["Tengoku.A"], "Tengoku\n")
            self.assertEqual(json.loads(r.stdout)["first"], ["Tengoku.A"])

    def test_a_base_that_is_not_a_commit_id_is_refused_not_passed_to_git(self):
        with tempfile.TemporaryDirectory() as d:
            self.repo(d)
            r = self.check(d, "--output=x", ["Tengoku.A"], "Tengoku\n")
            self.assertEqual(r.returncode, 2, r.stdout + r.stderr)
            self.assertFalse((Path(d) / "x").exists())


if __name__ == "__main__":
    unittest.main()
