#!/usr/bin/env python3
"""tag_verify.py <base> <head> — the merge queue's check of a TAG group, after it built the group's modules (queue-gate.yml).

The gate (tag_check.py) saw that the PR changes nothing but tags; this recomputes them. It builds `tengoku-isnad`, runs it over the group's modules and has
`scripts/isnad.py check-tags` compare: every taggable theorem carries exactly the tag the build computes, no tag is stale, none belongs to no theorem. A group
that is not a tag group is left alone (exit 0), so the step can run for every group.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _git import ROOT, changed_files  # noqa: E402
from tag_check import is_tag, module_of  # noqa: E402


def main(argv: list[str]) -> int:
    base, head = argv[1], argv[2]
    if not is_tag(base, head):
        print("not a tag group: nothing to verify")
        return 0
    modules = [module_of(p) for _, p in changed_files(base, head)]
    build = subprocess.run(["lake", "build", "tengoku-isnad"], cwd=ROOT, capture_output=True, text=True, check=False)
    if build.returncode != 0:
        print("error: tengoku-isnad does not build\n" + (build.stdout + build.stderr)[-1500:])
        return 1
    cmd = [sys.executable, str(ROOT / "scripts" / "isnad.py"), "check-tags"] + [x for m in modules for x in ("--module", m)]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, check=False)
    print((r.stdout + r.stderr).strip())
    if r.returncode != 0:
        print(f"error: the tags of {len(modules)} module(s) are not the build's")
    return r.returncode


if __name__ == "__main__":
    sys.exit(main(sys.argv))
