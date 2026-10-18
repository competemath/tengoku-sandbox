#!/usr/bin/env python3
"""credits.py <base> <head> — nobody's name comes off.
Any removed or changed line carrying an authorship or provenance marker fails.
Scripts, workflows and schemas are exempt: they mention the marker keys by
name (a fixture record in selftest.sh tripped this in the sandbox). Seeded
modules, data, docs and licences are covered. One exception: deleting the whole data
file of a source taken off the allowlist (_git.deregistered), whose records must leave
the tree with their credits. The other: a RAZE PR (scripts/ci/raze_check.py judges it) takes the modules of an intake library out of the tree, and their credit lines go with them:
the files it deletes, and the manifest lines of the modules whose files it deletes (the corrected bundle that brings the modules back carries its own)."""

from __future__ import annotations

import json
import re
import sys
from collections import Counter

from _git import added_lines, blob, changed_files, deregistered, fail, match, module_stem, removed_lines

EXEMPT = ["scripts/*", ".github/*", "schemas/*", "*.py", "*.sh", "*.toml", "*.yml", "*.yaml", "*.json", "README.md"]
# "README.md" is the ROOT file only (the pattern has no wildcard): the project's front page is prose, and a rewrite of the paragraph that explains the
# `Author:` convention was refused as a removed credit (tengoku#559, the maintainer's decision). A README.md anywhere else is covered, and a credit line
# moved INTO the root README is not kept (an exempt file is no home for a credit).
CREDIT = re.compile(r"(Authors?:|@author|\bCredit|Copyright|\"source_url\"|\"added_by\"|\"author\"|\"authors\")", re.I)
# In Markdown only the human attribution markers count: a JSON key inside a code example
# (the README's record-shape block carried `"source_url": "..."`) is not a provenance line.
CREDIT_MD = re.compile(r"(Authors?:|@author|Copyright)", re.I)
base, head = sys.argv[1], sys.argv[2]
promotion = "--promotion" in sys.argv  # the bot moves staging records to trusted: the credit travels with them
restructure = (
    "--restructure" in sys.argv
)  # the seed moves into Tengoku/Seed/: a credit line is not removed while it is in the file at its new path
raze = "--raze" in sys.argv  # a removal of intake modules: the credit lines of what is deleted go with it (and nothing else)
razed_files: set[str] = set()
if raze:
    razed_files = {p for st, p in changed_files(base, head) if st == "D" and re.fullmatch(r"Tengoku/.+\.lean", p)}


def razed_record(text: str) -> bool:
    """Whether this removed manifest line is the record of a module whose file this PR deletes."""
    try:
        mod = json.loads(text).get("module")
    except Exception:
        return False
    return isinstance(mod, str) and f"{module_stem(mod)}.lean" in razed_files


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
# docs/credit.md, 2026-10-07). Only Markdown: a credit in a module or a record never travels this way. Counted per occurrence: a line gained
# once covers one removal, so two files losing the same line need it gained twice.
md_added: Counter[str] = Counter()
for st, p in changed_files(base, head):
    if p.endswith(".md") and st != "D" and not match(p, EXEMPT):
        md_added.update(text.strip() for _, text in added_lines(base, head, p) if CREDIT_MD.search(text))


def moved_in_markdown(path: str, text: str) -> bool:
    """Whether this removed Markdown line is covered by a verbatim gain elsewhere in Markdown (each gain covers one removal)."""
    key = text.strip()
    if not path.endswith(".md") or md_added[key] <= 0:
        return False
    md_added[key] -= 1
    return True


def terminator_split(text: str) -> str:
    """The line without a docstring terminator at its end (`... credit. -/` is `... credit.`), or "" when it does not end with one."""
    core = text.rstrip()
    return core[:-2].rstrip() if core.endswith("-/") and len(core) > 2 else ""


hits = []
for st, p in changed_files(base, head):
    if st == "A" or match(p, EXEMPT) or (st == "D" and deregistered(base, p)):
        continue
    if raze and st == "D" and (p in razed_files or re.fullmatch(r"data/intake/[^/]+/.+", p)):
        continue  # a deleted module, or the data of a whole library that is razed
    rx = CREDIT_MD if p.endswith(".md") else CREDIT
    kept = moved_lines(p) if st == "D" else set()
    # A docstring that gets a line added at its end (the isnad tagger's `@isnad1 ...`) loses its ` -/` on the line that carried it; if that line carries a marker (an ordinary "credit" in
    # the sentence, tengoku#539), it counts as changed, though its text is still there. A line whose text survives VERBATIM as a gained line, with only the terminator gone, has lost nothing.
    # Per occurrence, as the Markdown move above: one gained line covers one removal.
    gained: Counter[str] = Counter()
    if p.endswith(".lean") and st != "D":
        gained.update(t.rstrip() for _, t in added_lines(base, head, p))
    for no, text in removed_lines(base, head, p):
        if not rx.search(text) or text in kept or moved_in_markdown(p, text):
            continue
        core = terminator_split(text)
        if core and gained[core] > 0:
            gained[core] -= 1
            continue
        if raze and re.fullmatch(r"data/intake/[^/]+/manifest\.jsonl", p) and razed_record(text):
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
