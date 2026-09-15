#!/usr/bin/env python3
"""sorry_scan.py <base> <head> — advisory only. Lists sorry/admit in what the PR adds.
Leak IV in the merge queue is the authority; this just tells the author early."""

from __future__ import annotations

import json
import re
import sys

from _git import added_lines, changed_files, match

base, head = sys.argv[1], sys.argv[2]
hits = []
for st, p in changed_files(base, head):
    if match(p, ["data/*/*.jsonl"]):
        for no, text in added_lines(base, head, p):
            try:
                r = json.loads(text)
            except Exception:
                continue
            if re.search(r"\b(sorry|admit)\b", str(r.get("proof", "")) + str(r.get("context", ""))):
                hits.append(f"{p}:{no} — {r.get('name')}")
    elif p.endswith(".lean"):
        hits += [f"{p}:{no}" for no, text in added_lines(base, head, p) if re.search(r"\b(sorry|admit)\b", text)]
if hits:
    print("### sorry / admit in this PR (advisory — the merge queue's build decides)\n")
    print("\n".join(f"- {h}" for h in hits))
else:
    print("no sorry/admit in added content")
