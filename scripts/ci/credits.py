#!/usr/bin/env python3
"""credits.py <base> <head> — nobody's name comes off.
Any removed or changed line carrying an authorship or provenance marker fails.
Scripts, workflows and schemas are exempt: they mention the marker keys by
name (a fixture record in selftest.sh tripped this in the sandbox). Seeded
modules, data, docs and licences are covered. One exception: deleting the whole data
file of a source taken off the allowlist (_git.deregistered), whose records must leave
the tree with their credits."""

from __future__ import annotations

import json
import re
import sys

from _git import added_lines, changed_files, deregistered, fail, match, removed_lines

EXEMPT = ["scripts/*", ".github/*", "schemas/*", "*.py", "*.sh", "*.toml", "*.yml", "*.yaml", "*.json"]
CREDIT = re.compile(r"(Authors?:|@author|\bCredit|Copyright|\"source_url\"|\"added_by\"|\"author\"|\"authors\")", re.I)
base, head = sys.argv[1], sys.argv[2]
promotion = "--promotion" in sys.argv  # the bot moves staging records to trusted: the credit travels with them
moved: set[tuple[str, str]] = set()
if promotion:
    for st, p in changed_files(base, head):
        if match(p, ["data/trusted/*.jsonl"]):
            for _, text in added_lines(base, head, p):
                try:
                    r = json.loads(text)
                except Exception:
                    continue
                moved.add((str(r.get("name")), str(r.get("source_url"))))
hits = []
for st, p in changed_files(base, head):
    if st == "A" or match(p, EXEMPT) or (st == "D" and deregistered(base, p)):
        continue
    for no, text in removed_lines(base, head, p):
        if not CREDIT.search(text):
            continue
        if promotion and match(p, ["data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
            try:
                r = json.loads(text)
            except Exception:
                r = {}
            if (str(r.get("name")), str(r.get("source_url"))) in moved:
                continue  # same name and provenance now in trusted
            hits.append(f"{p}:{no}: staging record removed without an identical trusted record ({r.get('name')})")
            continue
        hits.append(f"{p}:{no}: {text.strip()[:120]}")
if hits:
    fail("credit or provenance lines were removed or changed:\n  " + "\n  ".join(hits[:10]))
print("credits OK")
