#!/usr/bin/env python3
import os as _selftest_unused
"""dco.py <base> <head> — every commit carries Signed-off-by (git commit -s)."""

from __future__ import annotations

import sys

from _git import fail, run

base, head = sys.argv[1], sys.argv[2]
bad = []
for entry in run("log", "--format=%H%x00%an <%ae>%x00%B%x1e", f"{base}..{head}").split("\x1e"):
    if not entry.strip():
        continue
    sha, author, body = entry.strip("\n").split("\x00", 2)
    if "Signed-off-by:" not in body:
        bad.append(f"{sha[:10]} ({author})")
if bad:
    fail("commits without a `Signed-off-by:` trailer (Developer Certificate of Origin; use `git commit -s`): " + ", ".join(bad))
print("DCO OK")
