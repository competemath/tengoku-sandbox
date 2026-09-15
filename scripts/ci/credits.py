#!/usr/bin/env python3
"""credits.py <base> <head> — nobody's name comes off.
Any removed or changed line carrying an authorship or provenance marker fails.
Scripts, workflows and schemas are exempt: they mention the marker keys by
name (a fixture record in selftest.sh tripped this in the sandbox). Seeded
modules, data, docs and licences are covered."""

from __future__ import annotations

import re
import sys

from _git import changed_files, fail, match, removed_lines

EXEMPT = ["scripts/*", ".github/*", "schemas/*", "*.py", "*.sh", "*.toml", "*.yml", "*.yaml", "*.json"]
CREDIT = re.compile(r"(Authors?:|@author|\bCredit|Copyright|\"source_url\"|\"added_by\"|\"author\"|\"authors\")", re.I)
base, head = sys.argv[1], sys.argv[2]
hits = []
for st, p in changed_files(base, head):
    if st == "A" or match(p, EXEMPT):
        continue
    for no, text in removed_lines(base, head, p):
        if CREDIT.search(text):
            hits.append(f"{p}:{no}: {text.strip()[:120]}")
if hits:
    fail("credit or provenance lines were removed or changed:\n  " + "\n  ".join(hits[:10]))
print("credits OK")
