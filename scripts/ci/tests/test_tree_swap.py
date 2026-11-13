"""Every workflow that builds the compiled tree adds swap after the cache is unpacked and before its first build (scripts/ci/add_swap.sh).

The real case (fixtures/tree_swap_2026-11-12.json): competemath/tengoku#779 (prime-gaps-186, one module of 166,723 lines) left the merge queue on 12 Nov 2026,
queue-gate runs 43306897671 and 43313465453: 92 GB free after seeding, `building: Tengoku.PrimeGaps186`, and 16 and 13 minutes later the runner was shut
down (exit 143), no error of its own, both times. The same module built in 1,279 s and 1,244 s in autotag-build, on the same kind of runner and also without swap; the factory's verify of it lost its
runner twice without swap and passed with 48 GB, using 2.6 GB of it while free memory fell to 2.7 GB. So the module sits at the edge of the runner's 16 GB.

Invariants:
  1. add_swap.sh: the swap is min(MAX, free - KEEP) whole GB, or none (exit 0, said) when under 8 GB can be spared; a failing command removes the file and
     exits 1; malformed arguments exit 2. Checked on the real free space of the queue after seeding (92 GB -> 48) and of the nightly build at its pack
     (78 GB -> 38), and on 2,000 generated (free, keep, max) cases against the formula.
  2. Each workflow that holds the tree (the four of test_free_disk.py) calls `scripts/ci/add_swap.sh 48 40` exactly once, in the job that seeds the cache:
     after `scripts/cache.sh get`, after the Free disk step (which turns swap off), and before every `lake build` of that job; in the queue, only for a
     merge group, as the seeding is. Broken versions (no call, before the seeding, after a build, swap turned off after it) are each caught.
"""

import json
import os
import random
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = ROOT / ".github" / "workflows"
SCRIPT = ROOT / "scripts" / "ci" / "add_swap.sh"
FX = json.loads((Path(__file__).parent / "fixtures" / "tree_swap_2026-11-12.json").read_text())
HOLD_THE_TREE = ("build.yml", "queue-gate.yml", "isnad-tag.yml", "independent-check.yml")
CALL = "scripts/ci/add_swap.sh 48 40"
GB = 1073741824


_FAKES = None


def fakes() -> str:
    """one directory of fake df/sudo for every case: df prints FAKE_AVAIL_GB, sudo logs to FAKE_SUDO_LOG and fails the command named in FAKE_FAIL"""
    global _FAKES
    if _FAKES is None:
        d = tempfile.mkdtemp(prefix="fake-swap-")
        Path(d, "df").write_text("#!/bin/sh\necho Avail\necho $((FAKE_AVAIL_GB * 1073741824))\n")
        Path(d, "sudo").write_text('#!/bin/sh\necho "$*" >> "$FAKE_SUDO_LOG"\n[ "$1" = "$FAKE_FAIL" ] && exit 1\nexit 0\n')
        for f in ("df", "sudo"):
            os.chmod(Path(d, f), 0o755)
        _FAKES = d
    return _FAKES


def run_script(args, avail_gb, fail=""):
    """add_swap.sh with fake df/sudo: (exit code, output, the sudo commands it ran)"""
    with tempfile.NamedTemporaryFile(prefix="sudo-", suffix=".log", delete=False) as f:
        log_path = f.name
    try:
        env = {
            **os.environ,
            "PATH": f"{fakes()}:{os.environ['PATH']}",
            "FAKE_AVAIL_GB": str(avail_gb),
            "FAKE_SUDO_LOG": log_path,
            "FAKE_FAIL": fail or "__none__",
        }
        r = subprocess.run(["bash", str(SCRIPT), *map(str, args)], capture_output=True, text=True, env=env)
        log = Path(log_path).read_text().splitlines()
    finally:
        os.unlink(log_path)
    return r.returncode, r.stdout + r.stderr, log


def expected(free, keep, mx):
    room = free - keep
    return None if room < 8 else min(room, mx)


class Script(unittest.TestCase):
    def test_the_real_queue_after_seeding(self):
        seeded = next(l for l in FX["queue_build_log"] if "after seeding: /dev/root" in l)
        free = int(re.search(r"\s(\d+)G\s+\d+%", seeded).group(1))
        self.assertEqual(free, 92)
        code, out, log = run_script([48, 40], free)
        self.assertEqual(code, 0, out)
        self.assertIn("add_swap.sh: 48 GB of swap (92 GB were free, 40 kept, at most 48)", out)
        self.assertIn("fallocate -l 48G /swapfile", log)
        self.assertEqual(log[-1], "swapon /swapfile")

    def test_the_real_nightly_at_its_pack(self):
        free = int(re.search(r"\s(\d+)G\s+\d+%", FX["nightly_pack"][-1]).group(1))
        self.assertEqual(free, 78)
        code, out, _ = run_script([48, 40], free)
        self.assertIn("38 GB of swap", out)

    def test_no_room_is_no_swap_and_no_failure(self):
        for free in (0, 14, 40, 47):
            code, out, log = run_script([48, 40], free)
            self.assertEqual(code, 0)
            self.assertIn("under 8 GB to spare, no swap", out)
            self.assertFalse(any(l.startswith("fallocate") for l in log))

    def test_a_failing_command_removes_the_file_and_fails(self):
        for step in ("fallocate", "chmod", "mkswap", "swapon"):
            code, out, log = run_script([48, 40], 92, fail=step)
            self.assertEqual(code, 1, step)
            self.assertIn(f"{step} failed; the swap file is removed", out)
            self.assertEqual(log[-1], "rm -f /swapfile")

    def test_bad_arguments(self):
        for args in ([], ["x", "40"], ["0", "40"], ["48", "-1"], ["48", "4.5"], ["48;rm", "40"]):
            self.assertEqual(run_script(args, 92)[0], 2, args)

    def test_generated(self):
        rng = random.Random(20261112)
        for _ in range(2000):  # 2,000 runs of the real script
            free, keep, mx = rng.randint(0, 200), rng.randint(0, 80), rng.randint(1, 64)
            code, out, log = run_script([mx, keep], free)
            want = expected(free, keep, mx)
            self.assertEqual(code, 0)
            if want is None:
                self.assertIn("no swap", out)
                self.assertFalse(any(l.startswith("fallocate") for l in log))
            else:
                self.assertIn(f"fallocate -l {want}G /swapfile", log, (free, keep, mx))
                self.assertLessEqual(want, mx)
                self.assertGreaterEqual(free - want, keep)


def lines_of(job):
    """(step index, step, line) for every non-comment shell line of the job, in order"""
    out = []
    for i, step in enumerate(job.get("steps", [])):
        for line in (step.get("run") or "").splitlines():
            s = line.strip()
            if s and not s.startswith("#"):
                out.append((i, step, s))
    return out


def problems(name: str, text: str) -> list[str]:
    jobs = yaml.safe_load(text)["jobs"]
    seeding = [j for j in jobs.values() if any("scripts/cache.sh get" in l for _, _, l in lines_of(j))]
    if len(seeding) != 1:
        return [f"{name}: {len(seeding)} jobs seed the cache"]
    job = seeding[0]
    lines = lines_of(job)
    at = [k for k, (_, _, l) in enumerate(lines) if CALL in l]
    seed = [k for k, (_, _, l) in enumerate(lines) if "scripts/cache.sh get" in l]
    builds = [k for k, (_, _, l) in enumerate(lines) if re.search(r"\blake build\b", l)]
    off = [k for k, (_, _, l) in enumerate(lines) if "swapoff -a" in l]
    out = []
    if len(at) != 1:
        return [f"{name}: the swap is added {len(at)} times"]
    k = at[0]
    if k < max(seed):
        out.append(f"{name}: the swap is sized before the cache is unpacked")
    if builds and k > min(builds):
        out.append(f"{name}: a lake build runs before the swap is there")
    if any(o > k for o in off):
        out.append(f"{name}: swap is turned off after it is added")
    step = lines[k][1]
    if (
        name == "queue-gate.yml"
        and step.get("if") != "github.event_name == 'merge_group'"
        and "cache.sh get" not in (step.get("run") or "")
    ):
        out.append(f"{name}: the swap step does not run exactly when the seeding does")
    return out


class Workflows(unittest.TestCase):
    def test_the_real_workflows(self):
        for name in HOLD_THE_TREE:
            self.assertEqual(problems(name, (WORKFLOWS / name).read_text()), [], name)

    def test_mutants_are_caught(self):
        q = (WORKFLOWS / "queue-gate.yml").read_text()
        i = (WORKFLOWS / "isnad-tag.yml").read_text()
        b = (WORKFLOWS / "build.yml").read_text()
        step_q = q[
            q.index("      - name: Swap for the modules near the runner's memory") : q.index(
                "      - name: Is this group only the pipeline's staging PRs?"
            )
        ]
        mutants = {
            "queue: no swap (main before this change)": ("queue-gate.yml", q.replace(step_q, "")),
            "queue: swap before the seeding": (
                "queue-gate.yml",
                q.replace(step_q, "").replace(
                    "      - name: Seed from the newest published cache", step_q + "      - name: Seed from the newest published cache"
                ),
            ),
            "queue: swap on every event": (
                "queue-gate.yml",
                q.replace(step_q, step_q.replace("        if: github.event_name == 'merge_group'\n", "")),
            ),
            "isnad: build before the swap": (
                "isnad-tag.yml",
                i.replace(
                    f"          {CALL}\n          lake build Tengoku.All",
                    f"          lake build Tengoku.All 2>&1 | tail -1\n          {CALL}\n          lake build Tengoku.All",
                ),
            ),
            "build: swap turned off after it": (
                "build.yml",
                b.replace(f"        run: {CALL}\n", f"        run: |\n          {CALL}\n          sudo swapoff -a\n"),
            ),
            "build: swap added twice": (
                "build.yml",
                b.replace(f"        run: {CALL}\n", f"        run: |\n          {CALL}\n          {CALL}\n"),
            ),
        }
        for label, (name, text) in mutants.items():
            self.assertNotEqual(text, (WORKFLOWS / name).read_text(), label)
            self.assertNotEqual(problems(name, text), [], label)

    def test_the_real_case_is_what_the_fixture_says(self):
        for log in (FX["queue_build_log"], FX["queue_build_log_second"]):  # the queue lost its runner on the module both times
            self.assertTrue(any("building: Tengoku.PrimeGaps186" in l for l in log))
            self.assertTrue(any("received a shutdown signal" in l for l in log))
        self.assertTrue(all("(12" in l for l in FX["autotag_built"]))  # 1279 s and 1244 s: it fits, just
        self.assertTrue(any("swap_used_kb=2600" in l for l in FX["factory_verify_with_swap"]))


if __name__ == "__main__":
    unittest.main()
