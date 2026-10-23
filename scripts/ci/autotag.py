#!/usr/bin/env python3
"""autotag.py plan <base> <head> — what the autotag-build workflow may tag in a lane PR (docs/isnad.md, "Born tagged").

The lanes that open pull requests by themselves (the studied lane, the intake lane) used to leave the isnad tags to the sweep: one more PR to approve for every PR
the lane opened. Now the lane's PR gets its tags before anyone looks at it. Two workflows do it, split so that no job both runs the PR's Lean and holds a token:

  autotag-build  (pull_request, no secret)   on the compiled tree: builds the PR's modules, tags them (`isnad.py tag`), builds them again and has `check-tags`
                                             recompute every tag; uploads the tagged modules as an artifact
  autotag-push   (workflow_run, main's code) takes that artifact as DATA, checks every file against the PR's own (scripts/ci/autotag_push.py: only tags
                                             changed, the bytes without the tags are the PR's, the tags are well formed), and adds one commit to the PR's branch

This is the first step of the build: it decides whether there is anything to tag, and refuses before any Lean runs unless the content already passed the lane's own gate
(the allow-list and the shape rules), run with the tags pending: the build elaborates the PR's modules, which only the content rules make safe to do before an approval.

  plan   prints one JSON line {"lane": "studied"|"intake"|"", "modules": [...], "paths": [...], "refused": "", "tagged": bool}
         lane ""        not a lane PR, or its author is not one of the lane's Apps (AUTOTAG_ACTORS): nothing to do
         tagged true    the PR already carries its tags (the lane's own tagging stage ran): nothing to do
         refused        the content did not pass its gate, or the PR is too large: why
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))  # scripts/ of the checkout this file is in
from _git import blob  # noqa: E402
from born_tagged import lane_modules, lane_of, module_errors  # noqa: E402
from tag_check import module_of  # noqa: E402

HERE = Path(__file__).resolve().parent
MAX_MODULES = 400  # what a queue entry builds in its time (the tag class has the same cap)
GATES = {"studied": "studied_check.py", "intake": "intake_check.py"}
DEFAULT_ACTORS = "tengoku-supervisor[bot],tengoku-intake[bot]"


def actors(env: dict[str, str] | None = None) -> set[str]:
    return {a.strip() for a in ((env or os.environ).get("AUTOTAG_ACTORS") or DEFAULT_ACTORS).split(",") if a.strip()}


def lane_gate(lane: str, base: str, head: str, env: dict[str, str] | None = None) -> tuple[bool, str]:
    """The lane's own gate on the PR, with the tags pending: (passed, the end of its output)."""
    e = {**os.environ, **(env or {}), "ISNAD_TAGS_PENDING": "1"}
    cmd = [sys.executable, str(HERE / GATES[lane]), base, head]
    if lane == "intake":
        cmd += ["--lint", e.get("LINT") or e.get("TENGOKU_INTAKE_LINT") or "strict"]
    r = subprocess.run(cmd, capture_output=True, text=True, env=e, check=False)
    return r.returncode == 0, (r.stdout + r.stderr).strip()[-600:]


def plan(base: str, head: str, author: str, env: dict[str, str] | None = None) -> dict:
    out: dict = {"lane": "", "modules": [], "paths": [], "refused": "", "tagged": False}
    lane = lane_of(base, head)
    if lane is None or author not in actors(env):
        return out
    out["lane"] = lane
    paths = lane_modules(base, head, lane)
    if not paths:
        return out
    ok, why = lane_gate(lane, base, head, env)
    if not ok:
        out["refused"] = f"the {lane} gate does not pass: {why}"
        return out
    if len(paths) > MAX_MODULES:
        out["refused"] = f"{len(paths)} modules: the autotag builds at most {MAX_MODULES} in one run"
        return out
    # a PR that already carries every tag the offline gate asks for (the lane tagged it itself) has nothing to add; whether they are the build's is the queue's to check
    tagged = all(not module_errors(p, (blob(head, p) or b"").decode("utf-8", errors="replace")) for p in paths)
    out.update(modules=[module_of(p) for p in paths], paths=paths, tagged=tagged)
    return out


def main(argv: list[str]) -> int:
    if len(argv) != 5 or argv[1] != "plan":
        print("usage: autotag.py plan <base> <head> <author>", file=sys.stderr)
        return 2
    print(json.dumps(plan(argv[2], argv[3], argv[4])))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
