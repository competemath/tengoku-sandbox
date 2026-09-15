#!/usr/bin/env python3
"""depends.py <pr body file> — `Depends-On: #N` lines must point at merged PRs
(or PRs already queued ahead). Dependencies are resolved by queue order."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys

from _git import fail

body = open(sys.argv[1]).read() if len(sys.argv) > 1 else ""
deps = re.findall(r"^\s*Depends-On:\s*#(\d+)", body, re.M | re.I)
blocking = []
for n in deps:
    repo = os.environ.get("GITHUB_REPOSITORY")  # the job has no checkout of the PR, so gh cannot infer the repository
    base = ["gh", "pr", "view", n, *(["-R", repo] if repo else [])]
    r = subprocess.run([*base, "--json", "state,isInMergeQueue"], capture_output=True, text=True)
    if r.returncode != 0:  # the job token may not read merge-queue state; the merge state alone answers most cases
        r = subprocess.run([*base, "--json", "state"], capture_output=True, text=True)
    if r.returncode != 0:
        blocking.append(f"#{n} (lookup failed: {r.stderr.strip()[:160]})")
        continue
    d = json.loads(r.stdout)
    if d.get("state") == "MERGED" or d.get("isInMergeQueue"):
        continue
    blocking.append(f"#{n} ({d.get('state', '?').lower()})")
if blocking:
    fail("waiting on dependencies to merge or enter the queue first: " + ", ".join(blocking))
print(f"dependencies OK ({len(deps)})")
