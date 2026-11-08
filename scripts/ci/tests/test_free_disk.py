"""Every workflow that holds the compiled tree frees what a build does not use, and the heavy steps say how full the disk is.

2026-10-13, within twelve hours: both nightly cache builds (at "Pack the cache"), the merge queue's last step for lean-pool part 10 and a factory verify job of the
tree's own build ended as `failure` with a step that never completed, no error and no log. A runner whose disk fills cannot even write its log. The runner has 145 GB,
34 GB of it used before anything runs, and the tree's unpacked cache (several GB packed, about ten times that unpacked) takes most of the rest. build.yml freed four
directories where queue-gate.yml freed eight.
"""

import re
import unittest
from pathlib import Path

WORKFLOWS = Path(__file__).resolve().parents[3] / ".github" / "workflows"
HOLD_THE_TREE = ("build.yml", "queue-gate.yml", "isnad-tag.yml", "independent-check.yml")
FREED = (
    "/usr/share/dotnet",
    "/usr/local/lib/android",
    "/opt/ghc",
    "/usr/local/.ghcup",
    "/opt/hostedtoolcache",
    "/usr/local/share/boost",
    "/usr/share/swift",
    "/usr/lib/jvm",
    "/usr/share/miniconda",
)
NEEDED = ("/usr/bin", "/usr/lib/x86_64-linux-gnu", "/usr/local/bin", "/home/runner", "$HOME", "/usr/sbin", "/etc", "/var/lib")


def free_disk_step(text: str) -> str:
    m = re.search(r"- name: Free disk[^\n]*\n(?:\s+if:[^\n]*\n)?\s+run: \|\n((?:\s{10,}[^\n]*\n)+)", text)
    assert m, "no Free disk step"
    return m.group(1)


class FreeDisk(unittest.TestCase):
    def test_every_workflow_that_holds_the_tree_frees_the_same_directories(self):
        for name in HOLD_THE_TREE:
            step = free_disk_step((WORKFLOWS / name).read_text())
            for path in FREED:
                self.assertIn(path, step, f"{name} does not free {path}")
            self.assertIn("docker image prune --all --force", step, name)
            self.assertIn("swapoff -a", step, name)

    def test_what_the_build_needs_is_never_removed(self):
        for name in HOLD_THE_TREE:
            rm = " ".join(ln for ln in free_disk_step((WORKFLOWS / name).read_text()).splitlines() if "rm -rf" in ln or "rm -f" in ln)
            for path in NEEDED:
                self.assertIsNone(re.search(rf"(^|\s){re.escape(path)}(\s|$)", rm), f"{name} removes {path}")

    def test_the_nightly_build_says_how_full_the_disk_is_around_the_pack(self):
        text = (WORKFLOWS / "build.yml").read_text()
        pack = text[text.index("- name: Pack the cache") :]
        pack = pack[: pack.index("upload-artifact")]
        self.assertIn("before pack:", pack)
        self.assertIn("du -sh .lake/build", pack)
        self.assertIn("after pack:", pack)
        self.assertLess(pack.index("before pack:"), pack.index("cache.sh"))
        self.assertLess(pack.index("cache.sh"), pack.index("after pack:"))

    def test_the_queue_says_how_full_the_disk_is_after_seeding(self):
        text = (WORKFLOWS / "queue-gate.yml").read_text()
        seed = text[text.index("- name: Seed from the newest published cache") :]
        seed = seed[: seed.index("- name:", 10)]
        self.assertIn("scripts/cache.sh get", seed)
        self.assertIn("after seeding:", seed)
        self.assertIn("du -sh .lake/build", seed)

    def test_no_job_that_holds_the_tree_needs_the_tool_cache_it_removes(self):
        for name in HOLD_THE_TREE:
            text = (WORKFLOWS / name).read_text()
            self.assertNotRegex(text, r"uses:\s*actions/setup-(python|node|go|java)", name)


if __name__ == "__main__":
    unittest.main()
