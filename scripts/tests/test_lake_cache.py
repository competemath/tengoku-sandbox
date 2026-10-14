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
        self.assertEqual(json.loads(r.stdout), {"targets": 1, "compiled": 2, "misses": 1, "first": ["Tengoku.Pfr.Basic"]})

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


if __name__ == "__main__":
    unittest.main()
