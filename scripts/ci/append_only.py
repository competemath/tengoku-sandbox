#!/usr/bin/env python3
"""append_only.py <base> <head> — data files only grow.
For every changed file under data/{tentative,staging,trusted}: the base content
must be a byte-prefix of the head content (new files are fine). Retract with a
tombstone line, never by deleting.

One exception: a tentative or staging file may be deleted outright when none of its
records comes from a source still on the allowlist (schemas/sources.json `allowed`,
as of the PR's head). Taking a source off the allowlist, for instance because its
licence cannot be redistributed with the rest of the tree, is a tooling PR; deleting
its data is the content PR after it. A tombstone would leave the text in the tree.
Trusted records are compiled into modules and still retract by tombstone."""

from __future__ import annotations

import sys

from _git import APPEND_ONLY, blob, changed_files, deregistered, fail, match

base, head = sys.argv[1], sys.argv[2]
promotion = "--promotion" in sys.argv  # the bot may shrink staging files when it moves records to trusted
checked = 0
for st, p in changed_files(base, head):
    if not match(p, APPEND_ONLY):
        continue
    if promotion and p.startswith("data/staging/"):
        continue
    if st == "D":
        if deregistered(base, p):
            print(f"{p}: deleted with its source (no record comes from a source on the allowlist)")
            checked += 1
            continue
        fail(
            f"{p}: deleted. Data files are append-only; retract with a tombstone line instead (a whole file may go only once its source is off the allowlist)."
        )
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
