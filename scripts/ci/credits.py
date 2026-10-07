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

from _git import added_lines, blob, changed_files, deregistered, fail, match, removed_lines

EXEMPT = ["scripts/*", ".github/*", "schemas/*", "*.py", "*.sh", "*.toml", "*.yml", "*.yaml", "*.json"]
CREDIT = re.compile(r"(Authors?:|@author|\bCredit|Copyright|\"source_url\"|\"added_by\"|\"author\"|\"authors\")", re.I)
# In Markdown only the human attribution markers count: a JSON key inside a code example
# (the README's record-shape block carried `"source_url": "..."`) is not a provenance line.
CREDIT_MD = re.compile(r"(Authors?:|@author|Copyright)", re.I)
base, head = sys.argv[1], sys.argv[2]
promotion = "--promotion" in sys.argv  # the bot moves staging records to trusted: the credit travels with them
restructure = (
    "--restructure" in sys.argv
)  # the seed moves into Tengoku/Seed/: a credit line is not removed while it is in the file at its new path
# A record whose credit line still exists anywhere at HEAD is fine, even if the exact bytes
# changed (the promote bot rewrites a staging file's remaining records when it lifts one out,
# which can reorder or reformat lines it never touched content-wise — found live: two records
# untouched by a promotion of a THIRD record in the same per-PR batch file were flagged as
# "removed" purely because the rewrite re-serialised them with different bytes at a new
# position). "Moved" (promoted to trusted) and "still staged" both count as present.
moved: set[tuple[str, str]] = set()
if promotion:
    for st, p in changed_files(base, head):
        if match(p, ["data/trusted/*.jsonl", "data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
            for _, text in added_lines(base, head, p):
                try:
                    r = json.loads(text)
                except Exception:
                    continue
                moved.add((str(r.get("name")), str(r.get("source_url"))))


def moved_lines(path: str) -> set[str]:
    """The lines of a seeded file at its new place, Tengoku/Seed/<same path> (nothing for any other path)."""
    if not (restructure and path.startswith("Tengoku/")):
        return set()
    text = blob(head, "Tengoku/Seed/" + path[len("Tengoku/") :])
    return set(text.decode("utf-8", "replace").split("\n")) if text is not None else set()


# A credit line that a Markdown file loses and another Markdown file gains, verbatim, has moved, not gone (the README's credit example moved to
# docs/credit.md, 2026-10-07). Only Markdown: a credit in a module or a record never travels this way.
md_added: set[str] = set()
for st, p in changed_files(base, head):
    if p.endswith(".md") and st != "D" and not match(p, EXEMPT):
        md_added |= {text.strip() for _, text in added_lines(base, head, p) if CREDIT_MD.search(text)}

hits = []
for st, p in changed_files(base, head):
    if st == "A" or match(p, EXEMPT) or (st == "D" and deregistered(base, p)):
        continue
    rx = CREDIT_MD if p.endswith(".md") else CREDIT
    kept = moved_lines(p) if st == "D" else set()
    for no, text in removed_lines(base, head, p):
        if not rx.search(text) or text in kept or (p.endswith(".md") and text.strip() in md_added):
            continue
        if promotion and match(p, ["data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
            try:
                r = json.loads(text)
            except Exception:
                r = {}
            if (str(r.get("name")), str(r.get("source_url"))) in moved:
                continue  # same name and provenance still present (promoted, or just reformatted in place)
            hits.append(f"{p}:{no}: staging record removed without an identical trusted record ({r.get('name')})")
            continue
        hits.append(f"{p}:{no}: {text.strip()[:120]}")
if hits:
    fail("credit or provenance lines were removed or changed:\n  " + "\n  ".join(hits[:10]))
print("credits OK")
