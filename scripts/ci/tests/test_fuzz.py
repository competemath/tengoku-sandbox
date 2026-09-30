"""The fuzz targets (scripts/ci/fuzz): each holds on its seeds and seeded mutations of them, each catches the bug
it was written against, and run.py picks exactly the targets a change covers."""

from __future__ import annotations

import importlib
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

CI = Path(__file__).resolve().parents[1]
FUZZ = CI / "fuzz"
sys.path[:0] = [str(FUZZ), str(CI)]
import run  # noqa: E402
from _harness import replay, seeds  # noqa: E402


def target(name: str):
    return importlib.import_module(f"fuzz_{name}")


class Targets(unittest.TestCase):
    def test_every_target_holds_on_its_seeds_and_their_mutations(self):
        for name in run.targets():
            with self.subTest(name):
                t = target(name)
                inputs = seeds(name, getattr(t, "SEEDS", []))
                self.assertTrue(inputs, f"fuzz_{name} has no seeds")
                self.assertEqual(replay(t.TestOneInput, inputs, mutations=500), len(inputs) + 500)

    def test_every_target_names_what_it_covers_and_how_long_it_runs(self):
        for name, c in run.targets().items():
            with self.subTest(name):
                self.assertTrue(c.get("COVERS"), name)
                self.assertTrue(all((CI.parents[1] / p).exists() for p in c["COVERS"]), c["COVERS"])
                self.assertIsInstance(c.get("RUNS"), int)

    def test_the_log_target_catches_a_run_of_colons_the_old_plain_let_through(self):
        t = target("log_text")
        old = lambda text: text.replace("\r", "").replace("::", ": :")  # noqa: E731 — plain before the fuzzer
        with mock.patch.object(t._git, "plain", old), self.assertRaises(AssertionError):
            t.TestOneInput(b"Lib.x\n:::stop-commands::t")
        t.TestOneInput(b"Lib.x\n:::stop-commands::t")

    def test_the_record_target_catches_a_traceback(self):
        t = target("records")
        t.TestOneInput(b'data/staging/mathlib.jsonl\n5\n[1]\n"tombstone"')  # refused with a message, not a traceback
        code = compile("x = {}['missing']", "validate_records.py", "exec")
        with mock.patch.object(t, "SCRIPTS", [("validate_records.py", code)]), self.assertRaises(KeyError):
            t.TestOneInput(b"data/staging/mathlib.jsonl\n{}")

    def test_the_workflow_target_catches_a_command_in_a_yaml_error(self):
        t = target("workflow_rules")
        broken = b"on: [push\n::stop-commands::t\npermissions: {}\n"
        old = lambda path, line, rule, msg: (f"{path}:{line}: [{rule}] {msg}", f"::error file={path}::{msg}")  # noqa: E731
        with mock.patch.object(t.wr, "report", old), self.assertRaises(AssertionError):
            t.TestOneInput(broken)
        t.TestOneInput(broken)
        readable, annotation = t.wr.report(".github/workflows/a,b:c.yml", 3, "yaml", "bad\n::add-mask::x")
        self.assertIn("file=.github/workflows/a%2Cb%3Ac.yml,line=3", annotation)
        self.assertNotRegex(readable, r"(?m)^\s*::")


class Selection(unittest.TestCase):
    def test_a_change_runs_the_targets_that_cover_it_and_nothing_else(self):
        self.assertEqual(run.selected(["data/staging/mathlib.jsonl", "README.md"]), [])
        self.assertEqual(run.selected(["scripts/ci/lean_lex.py"]), ["lean_lex"])
        self.assertEqual(run.selected(["scripts/ci/workflow_rules.py"]), ["workflow_rules"])
        self.assertEqual(run.selected(["schemas/sources.json"]), ["records"])
        self.assertEqual(run.selected(["scripts/ci/fuzz/corpus/log_text/new"]), ["log_text"])
        self.assertEqual(run.selected(["scripts/ci/fuzz/fuzz_records.py"]), ["records"])
        self.assertEqual(sorted(run.selected(["scripts/ci/_git.py"])), ["lean_lex", "log_text", "records", "workflow_rules"])
        self.assertEqual(run.selected(["scripts/ci/requirements/fuzz.txt"]), list(run.targets()))

    def test_the_runner_lists_and_replays_without_atheris(self):
        r = subprocess.run([sys.executable, str(FUZZ / "run.py"), "--all", "--list"], capture_output=True, text=True)
        self.assertEqual(r.stdout.split(), list(run.targets()))
        r = subprocess.run([sys.executable, str(FUZZ / "run.py"), "--all", "--replay"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(r.stdout.count("inputs replayed"), len(run.targets()))


if __name__ == "__main__":
    unittest.main()
