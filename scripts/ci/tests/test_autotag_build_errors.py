"""autotag-build's rebuild of the tagged modules shows the build's errors when it fails.

The real case: competemath/tengoku#780 (lean-operads, 12 Nov 2026, autotag-build run 43315053031): after tagging 547 theorems and creating 1,158 docstrings,
`lake build` of the tagged modules failed, and the step's `| tail -3` printed only

    - Tengoku.LeanOperads.Operad.ShuffleTree
    - Tengoku.LeanOperads.Operad.SymTreeConv
    error: build failed

so what the tagger broke could not be read, and the artifact with the tagged files is not uploaded on a failure.

Invariants (the step's own shell text, run as GitHub runs it: bash -e -o pipefail, in a directory with plan.json and a fake `lake`):
  1. A failing build fails the step, and its output holds every error line of the build with the lines after it, and the build's last lines.
  2. A passing build still runs the tag check and fails or passes with it.
  2b. A build killed with no error line, or with more than 200 lines of them, still shows its last lines (Gitar on #782).
  3. Mutant: the step as it was (`| tail -3`) hides the error line (the reason for this change).
"""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[3]
WF = ROOT / ".github" / "workflows" / "autotag-build.yml"
STEP = "The tagged modules build, and every tag is the build's"
MODULES = ["Tengoku.LeanOperads.Operad.ShuffleTree", "Tengoku.LeanOperads.Operad.SymTreeConv"]
REAL_TAIL = "- Tengoku.LeanOperads.Operad.ShuffleTree\n- Tengoku.LeanOperads.Operad.SymTreeConv\nerror: build failed\n"
# an error in the shape Lake prints one (the real one was not kept: that is the bug)
ERROR = (
    "✖ [8771/8773] Building Tengoku.LeanOperads.Operad.SymTreeConv\n"
    "trace: .> LEAN_PATH=./.lake/build/lib/lean lean ./Tengoku/LeanOperads/Operad/SymTreeConv.lean\n"
    "error: ./Tengoku/LeanOperads/Operad/SymTreeConv.lean:978:0: unexpected token '/--'; expected 'lemma'\n"
    "error: ./Tengoku/LeanOperads/Operad/SymTreeConv.lean:978:0: unexpected token '/--'; expected 'theorem'\n"
)


def step_text(text: str) -> str:
    steps = next(j for j in yaml.safe_load(text)["jobs"].values() if any(s.get("name") == STEP for s in j.get("steps", [])))["steps"]
    return next(s["run"] for s in steps if s.get("name") == STEP)


def run(text: str, lake_out: str, lake_code: int, check_code: int = 0):
    with tempfile.TemporaryDirectory() as d:
        b = Path(d)
        (b / "plan.json").write_text(json.dumps({"modules": MODULES}))
        (b / "bin").mkdir()
        (b / "bin" / "lake").write_text(f"#!/bin/sh\ncat <<'EOF'\n{lake_out}EOF\nexit {lake_code}\n")
        os.chmod(b / "bin" / "lake", 0o755)
        (b / "scripts").mkdir()
        (b / "scripts" / "isnad.py").write_text(f"import sys\nprint('check-tags', *sys.argv[1:])\nsys.exit({check_code})\n")
        r = subprocess.run(
            ["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", "-c", text],
            cwd=d,
            capture_output=True,
            text=True,
            env={**os.environ, "PATH": f"{b / 'bin'}:{os.environ['PATH']}"},
        )
        return r.returncode, r.stdout + r.stderr


class AutotagBuildErrors(unittest.TestCase):
    TEXT = step_text(WF.read_text())

    def test_a_failed_build_shows_its_errors(self):
        code, out = run(self.TEXT, ERROR + REAL_TAIL, 1)
        self.assertNotEqual(code, 0)
        self.assertIn("SymTreeConv.lean:978:0: unexpected token '/--'; expected 'lemma'", out)
        self.assertIn("SymTreeConv.lean:978:0: unexpected token '/--'; expected 'theorem'", out)
        self.assertIn("error: build failed", out)
        self.assertNotIn("check-tags", out)  # nothing after a failed build

    def test_a_passing_build_runs_the_tag_check(self):
        code, out = run(self.TEXT, "Build completed successfully (4 jobs).\n", 0)
        self.assertEqual(code, 0, out)
        self.assertIn("check-tags --module Tengoku.LeanOperads.Operad.ShuffleTree --module Tengoku.LeanOperads.Operad.SymTreeConv", out)
        code, out = run(self.TEXT, "Build completed successfully (4 jobs).\n", 0, check_code=1)
        self.assertNotEqual(code, 0)

    def test_many_errors_are_all_shown_up_to_the_cap(self):
        many = "".join(f"error: ./Tengoku/LeanOperads/Operad/ShuffleTree.lean:{i}:0: unknown identifier 'x{i}'\n" for i in range(30))
        code, out = run(self.TEXT, many + REAL_TAIL, 1)
        self.assertNotEqual(code, 0)
        self.assertEqual(sum(1 for i in range(30) if f"unknown identifier 'x{i}'" in out), 30)

    def test_a_killed_build_with_no_error_line_still_shows_its_last_lines(self):
        # Lake killed for memory prints no `error` line at all (Gitar on #782): grep finding nothing must not end the step first
        killed = "".join(f"\u2714 [{i}/8773] Built Tengoku.Module{i}\n" for i in range(8700, 8760)) + "Killed\n"
        code, out = run(self.TEXT, killed, 137)
        self.assertNotEqual(code, 0)
        self.assertIn("(no error line: the last 40 lines follow)", out)
        self.assertIn("Killed", out)
        self.assertIn("Built Tengoku.Module8759", out)

    # 3,000 error lines (about 250 KB, more than a pipe holds): `head` closes the pipe while grep still writes, so grep ends with SIGPIPE (exit 141) and,
    # under `-o pipefail`, the step would stop there without the `|| true`
    FLOOD = (
        "".join(f"error: ./Tengoku/LeanOperads/Operad/ShuffleTree.lean:{i}:0: unknown identifier 'y{i}'\n" for i in range(3000)) + REAL_TAIL
    )

    @staticmethod
    def flood_problems(code: int, out: str) -> list[str]:
        shown = out.count("unknown identifier 'y")
        problems = []
        if code == 0:
            problems.append("the step passed")
        if not 200 <= shown <= 240:  # the capped error lines, then the last 40 lines (39 of them errors, plus the tail of the build)
            problems.append(f"{shown} error lines shown, not 200 to 240")
        if not out.rstrip().endswith("error: build failed"):
            problems.append("the last lines of the build were not shown")
        return problems

    def test_more_than_two_hundred_error_lines_are_capped_and_the_last_lines_still_come(self):
        self.assertEqual(self.flood_problems(*run(self.TEXT, self.FLOOD, 1)), [])

    def test_mutants_of_the_cap_are_caught(self):
        # Gitar on #783: the first version of this test passed with the cap or the `|| true` removed
        no_cap = self.TEXT.replace(" | head -200 || true", " || true")
        no_true = self.TEXT.replace(" | head -200 || true", " | head -200")
        for label, text in (("no cap", no_cap), ("no || true", no_true)):
            self.assertNotEqual(text, self.TEXT, label)
            self.assertNotEqual(self.flood_problems(*run(text, self.FLOOD, 1)), [], label)

    def test_mutant_the_first_version_shows_nothing_for_a_killed_build(self):
        # the version Gitar flagged on #782: grep finding nothing ends the step under -e before anything is printed
        lines = self.TEXT.splitlines(keepends=True)
        a = next(i for i, ln in enumerate(lines) if ln.lstrip().startswith("{ grep"))
        b = next(i for i, ln in enumerate(lines) if ln.strip() == "tail -40 tagged-build.log")
        pad = lines[a][: len(lines[a]) - len(lines[a].lstrip())]
        first = "".join(
            lines[:a]
            + [f"{pad}grep -E -A4 '(^|: )error' tagged-build.log | head -200\n", f"{pad}tail -3 tagged-build.log\n"]
            + lines[b + 1 :]
        )
        self.assertNotEqual(first, self.TEXT)
        killed = "".join(f"\u2714 [{i}/8773] Built Tengoku.Module{i}\n" for i in range(8700, 8760)) + "Killed\n"
        code, out = run(first, killed, 137)
        self.assertNotEqual(code, 0)
        self.assertNotIn("Killed", out)  # nothing of the build reached the log
        code, out = run(self.TEXT, killed, 137)  # and the step as it is now shows it
        self.assertIn("Killed", out)

    def test_mutant_the_step_as_it_was_hides_the_error(self):
        old = self.TEXT
        start = (
            old.index("          # the build's whole output")
            if "          # the build's whole output" in old
            else old.index("# the build's whole output")
        )
        end = old.index("python3 scripts/isnad.py check-tags")
        as_it_was = old[:start] + 'lake build "${mods[@]}" 2>&1 | tail -3\n' + old[end:]
        code, out = run(as_it_was, ERROR + REAL_TAIL, 1)
        self.assertNotEqual(code, 0)
        self.assertNotIn("unexpected token", out)
        self.assertIn("error: build failed", out)  # what #780's log showed, and all of it


if __name__ == "__main__":
    unittest.main()
