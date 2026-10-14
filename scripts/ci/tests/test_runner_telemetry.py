"""scripts/ci/runner_telemetry.py: what a failed job leaves behind about the runner (no space left, killed for memory)."""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "runner_telemetry.py"
sys.path.insert(0, str(SCRIPT.parent))
import runner_telemetry as rt  # noqa: E402


def row(t, used, free, mem=None, top=("lean=900",)):
    r = {"t": t, "disk_used_gb": used, "disk_free_gb": free, "top": list(top)}
    if mem:
        r.update(mem_used_mb=mem[0], mem_avail_mb=mem[1], swap_used_mb=mem[2])
    return r


def run(*args, cwd, env=None):
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args], cwd=cwd, capture_output=True, text=True, env={**os.environ, **(env or {})}, check=False
    )


class Summary(unittest.TestCase):
    def test_the_extremes_and_what_was_biggest_when_the_disk_was_fullest(self):
        rows = [row(0, 25.0, 120.0), row(600, 140.5, 4.5, top=("lean=8000", "lake=300")), row(1200, 60.0, 85.0)]
        s = rt.summarize(rows, [])
        self.assertIn("3 samples over 20 min", s)
        self.assertIn("the most used was 140.5 GB, the least free 4.5 GB (biggest then: lean=8000, lake=300)", s)

    def test_memory_extremes_and_the_kernels_kills_are_listed(self):
        rows = [row(0, 25.0, 120.0, mem=(1000, 15000, 0)), row(60, 30.0, 115.0, mem=(15800, 200, 2048))]
        s = rt.summarize(rows, ["Out of memory: Killed process 4242 (lean) total-vm:1234kB"])
        self.assertIn("the most used was 15800 MB, the least available 200 MB, swap at most 2048 MB", s)
        self.assertIn("out-of-memory kills in the kernel log: 1", s)
        self.assertIn("Killed process 4242 (lean)", s)

    def test_no_samples_is_said_not_an_error(self):
        self.assertIn("no samples were taken", rt.summarize([], []))

    def test_the_oom_pattern_matches_the_kernels_wording_and_nothing_else(self):
        for ln in (
            "Out of memory: Killed process 12 (lean)",
            "oom-kill:constraint=CONSTRAINT_NONE",
            "Memory cgroup out of memory: Killed process 7",
            "Killed process 4242 (lean) total-vm:9876kB, anon-rss:4096kB",
        ):
            self.assertTrue(rt.OOM.search(ln), ln)
        self.assertFalse(rt.OOM.search("usb 1-1: new high-speed USB device"))


class Command(unittest.TestCase):
    def test_a_sample_has_the_numbers_a_failure_is_diagnosed_from(self):
        s = rt.sample()
        self.assertIsInstance(s["disk_used_gb"], float)
        self.assertIsInstance(s["disk_free_gb"], float)
        self.assertIsInstance(s["top"], list)
        self.assertLessEqual(len(s["top"]), 3)

    def test_watch_appends_one_line_per_sample_and_stops_at_the_limit(self):
        with tempfile.TemporaryDirectory() as d:
            r = run("watch", "--max", "3", cwd=d, env={"TELEMETRY_INTERVAL": "0.05"})
            self.assertEqual(r.returncode, 0, r.stderr)
            lines = (Path(d) / "telemetry.jsonl").read_text().splitlines()
            self.assertEqual(len(lines), 3)
            self.assertTrue(all("disk_free_gb" in json.loads(ln) for ln in lines))

    def test_summary_reads_what_watch_wrote_and_survives_a_cut_short_last_line(self):
        with tempfile.TemporaryDirectory() as d:
            run("watch", "--max", "2", cwd=d, env={"TELEMETRY_INTERVAL": "0.05"})
            with (Path(d) / "telemetry.jsonl").open("a") as f:
                f.write('{"t": 1, "disk_us')
            r = run("summary", cwd=d)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn("2 samples over", r.stdout)

    def test_summary_without_a_log_succeeds(self):
        with tempfile.TemporaryDirectory() as d:
            r = run("summary", cwd=d)
            self.assertEqual((r.returncode, "no samples" in r.stdout), (0, True))

    def test_no_command_takes_a_path(self):
        with tempfile.TemporaryDirectory() as d:
            for args in (["summary", "x.jsonl"], ["watch", "--out", "x"], ["watch", "x"]):
                r = run(*args, cwd=d)
                self.assertEqual(r.returncode, 2, (args, r.stderr))
                self.assertIn("usage:", r.stderr)


if __name__ == "__main__":
    unittest.main()
