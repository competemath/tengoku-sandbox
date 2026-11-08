#!/usr/bin/env python3
"""tag_verify.py <base> <head> — the merge queue's check of a TAG group or a born-tagged lane group, after it built the group's modules (queue-gate.yml).

The gate (tag_check.py) saw that the PR changes nothing but tags; this recomputes them. The same goes for the modules of a studied PR, and of an intake PR once
TENGOKU_ISNAD_REQUIRED is 1 (scripts/ci/born_tagged.py): the lane's PR carries its tags, and the build has the last word on every one of them. It builds `tengoku-isnad`, runs it over the group's modules and has
`scripts/isnad.py check-tags` compare: every taggable theorem carries exactly the tag the build computes, no tag is stale, none belongs to no theorem. A group
that is not a tag group is left alone (exit 0), so the step can run for every group.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _git import ROOT, changed_files  # noqa: E402
from born_tagged import lane_modules, lane_of, required  # noqa: E402
from tag_check import is_tag, module_of  # noqa: E402


def group_modules(base: str, head: str) -> list[str]:
    """The modules whose tags the build must confirm: a tag group's, or those of a lane group that is born tagged (the studied lane always; the intake
    lane when TENGOKU_ISNAD_REQUIRED is 1, scripts/ci/born_tagged.py). Empty: nothing to verify."""
    if is_tag(base, head):
        return [module_of(p) for _, p in changed_files(base, head)]
    lane = lane_of(base, head)
    if required(lane):
        return [module_of(p) for p in lane_modules(base, head, lane)]
    return []


def main(argv: list[str]) -> int:
    base, head = argv[1], argv[2]
    modules = group_modules(base, head)
    if not modules:
        print("not a tag group, nor a lane group that is born tagged: nothing to verify")
        return 0
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
