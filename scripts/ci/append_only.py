#!/usr/bin/env python3
"""append_only.py <base> <head> — data files only grow.
For every changed file under data/{tentative,staging,trusted}: the base content
must be a byte-prefix of the head content (new files are fine). Retract with a
tombstone line, never by deleting."""

from __future__ import annotations

import sys

from _git import APPEND_ONLY, blob, changed_files, fail, match

base, head = sys.argv[1], sys.argv[2]
checked = 0
for st, p in changed_files(base, head):
    if not match(p, APPEND_ONLY):
        continue
    if st == "D":
        fail(f"{p}: deleted. Data files are append-only; retract with a tombstone line instead.")
    old = blob(base, p) or b""
    new = blob(head, p) or b""
    if not new.startswith(old):
        # locate the first differing byte for the message
        i = next((k for k in range(min(len(old), len(new))) if old[k] != new[k]), min(len(old), len(new)))
        line = old[:i].count(b"\n") + 1
        fail(f"{p}: modified at line {line}. Data files are append-only: add lines at the end, or append a tombstone to retract.")
    if new and not new.endswith(b"\n"):
        fail(f"{p}: must end with a newline (the next append would merge with your last line)")
    checked += 1
print(f"append-only OK ({checked} data files)")
