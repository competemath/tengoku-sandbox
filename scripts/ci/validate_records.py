#!/usr/bin/env python3
"""validate_records.py <base> <head> — every added record is well-formed.
Checks only the lines a PR adds to data/*/*.jsonl: JSON, required fields per
tier (schemas/record.schema.json), status matches the tier, library matches
the file, source on the allowlist (schemas/sources.json), no duplicate names
in the PR or against trusted, tombstones point at existing names and carry a fixed category, a note on
where to look instead points at a tombstoned name, a credit correction names a trusted record and links its
evidence, file ≤ 50 MB, at most ten headline records per PR, each crediting its author."""

from __future__ import annotations

import json
import re
import sys
import urllib.parse

from _git import ROOT, added_lines, blob, changed_files, fail, library_of, load_schema, match

MAX_BYTES = 50 * 1024 * 1024
MAX_HEADLINES = 10  # the results a PR is about, shown first; more would be clutter
base, head = sys.argv[1], sys.argv[2]
schema = load_schema("record.schema.json")
NAME_RE = re.compile(
    r"[^\s,\x00-\x08\x0e-\x1b]+"
)  # not whitespace, a comma or a control character (\s already covers \t \n \v \f \r and \x1c-\x1f)
sources_doc = load_schema("sources.json")
sources = sources_doc["allowed"]
corpora = sources_doc.get("corpora", {})
errors, seen, names_by_tier = [], set(), {}
headlines: list[str] = []


def tier(p: str) -> str:
    return p.split("/")[1]


_EVENTS: list[dict] | None = None


def _tombstones_in(f) -> list[dict]:
    """The tombstone records of one trusted file; each line is decoded."""
    out = []
    for line in f.open(encoding="utf-8"):
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if isinstance(r, dict) and "tombstone" in r:
            out.append(r)
    return out


def trusted_tombstones() -> list[dict]:
    """Every tombstone line in trusted, flat and per-library files. All of trusted parses in under a second."""
    global _EVENTS
    if _EVENTS is None:
        _EVENTS = [r for f in (ROOT / "data" / "trusted").rglob("*.jsonl") for r in _tombstones_in(f)]
    return _EVENTS


def tombstone_categories() -> dict[str, str]:
    """name -> the category its first tombstone set (a category never changes)."""
    out: dict[str, str] = {}
    for r in trusted_tombstones():
        if r.get("category"):
            out.setdefault(str(r["tombstone"]), str(r["category"]))
    return out


def tombstoned_names() -> set[str]:
    return {str(r["tombstone"]) for r in trusted_tombstones()}


def trusted_names() -> set[str]:
    out = set()
    for f in (ROOT / "data" / "trusted").rglob("*.jsonl"):  # flat and per-library files
        for line in f.open("rb"):
            m = re.search(rb'"name"\s*:\s*"([^"]+)"', line)
            if m:
                out.add(m.group(1).decode())
    return out


known = None
tombstoned = None
categories = None
AT_RE = re.compile(r"\d{4}-\d{2}-\d{2}(?:T\d{2}:\d{2}:\d{2}Z)?")  # UTC: the newest correction is the greatest string


def good_link(url: str) -> bool:
    try:
        u = urllib.parse.urlsplit(url)
    except ValueError:
        return False
    return u.scheme in ("http", "https") and bool(u.hostname) and "." in (u.hostname or "") and not re.search(r"\s", url)


for st, p in changed_files(base, head):
    if not match(
        p, ["data/tentative/*.jsonl", "data/staging/*.jsonl", "data/trusted/*.jsonl", "data/tentative/*/*.jsonl", "data/staging/*/*.jsonl"]
    ):
        continue
    t, lib = tier(p), library_of(p)
    size = len(blob(head, p) or b"")
    if size > MAX_BYTES:
        errors.append(f"{p}: {size / 1048576:.0f} MB > 50 MB; shard into {lib}.NN.jsonl")
    for no, text in added_lines(base, head, p):
        if not text.strip():
            errors.append(f"{p}:{no}: blank line")
            continue
        try:
            r = json.loads(text)
        except Exception as e:
            errors.append(f"{p}:{no}: not JSON ({e})")
            continue
        if not isinstance(r, dict):  # a number, string or list used to end the check in a traceback (scripts/ci/fuzz)
            errors.append(f"{p}:{no}: a record is a JSON object, not {type(r).__name__}")
            continue
        if any(k in r for k in ("tombstone", "tombstone_note", "credit_correction")) and "at" in r and not AT_RE.fullmatch(str(r["at"])):
            errors.append(f"{p}:{no}: at is a UTC date or time: YYYY-MM-DD or YYYY-MM-DDTHH:MM:SSZ (got {r['at']!r})")
        if "tombstone" in r:
            for k in schema["tombstone"]["required"]:
                if k not in r:
                    errors.append(f"{p}:{no}: tombstone missing {k}")
            if "category" in r and r["category"] not in schema["tombstone_categories"]:
                errors.append(f"{p}:{no}: tombstone category {r['category']!r} is not one of {', '.join(schema['tombstone_categories'])}")
            if not isinstance(r["tombstone"], str):
                errors.append(f"{p}:{no}: tombstone is the name of a record (a string)")
                continue
            if categories is None:
                categories = tombstone_categories()
            first = categories.setdefault(str(r["tombstone"]), str(r.get("category", "")))
            if r.get("category") and first and r["category"] != first:
                errors.append(f"{p}:{no}: {r['tombstone']} is already tombstoned as {first!r}; a category never changes")
            if known is None:
                known = trusted_names()
            if t == "trusted" and r["tombstone"] not in known:
                errors.append(f"{p}:{no}: tombstone for unknown name {r['tombstone']}")
            continue
        if "tombstone_note" in r or "credit_correction" in r:
            kind = "tombstone_note" if "tombstone_note" in r else "credit_correction"
            for k in schema[kind]["required"]:
                if k not in r:
                    errors.append(f"{p}:{no}: {kind} missing {k}")
            if not isinstance(r[kind], str):
                errors.append(f"{p}:{no}: {kind} is the name of a record (a string)")
                continue
            if t != "trusted":
                errors.append(f"{p}:{no}: a {kind} goes in data/trusted/<library>.jsonl")
            if known is None:
                known = trusted_names()
            if tombstoned is None:  # the base's tombstones and the ones this PR adds
                tombstoned = tombstoned_names()
                for _, q in changed_files(base, head):
                    if match(q, ["data/trusted/*.jsonl", "data/trusted/*/*.jsonl"]):
                        for _, x in added_lines(base, head, q):
                            try:
                                added = json.loads(x)
                            except ValueError:
                                continue
                            if isinstance(added, dict) and "tombstone" in added:  # the word alone (a note's text) is not one
                                tombstoned.add(str(added["tombstone"]))
            if kind == "tombstone_note":
                if r["tombstone_note"] not in tombstoned:
                    errors.append(f"{p}:{no}: a tombstone_note is for a retracted record; {r['tombstone_note']} has no tombstone")
                see = r.get("see", [])
                if not isinstance(see, list) or not all(isinstance(x, str) for x in see):
                    errors.append(f"{p}:{no}: see is a list of tengoku names or links")
            else:
                if r["credit_correction"] not in known:
                    errors.append(f"{p}:{no}: credit_correction for unknown name {r['credit_correction']}")
                elif r["credit_correction"] in tombstoned:  # a retraction is permanent: the corrected record is never generated
                    errors.append(f"{p}:{no}: {r['credit_correction']} is retracted; a credit correction for it would have no effect")
                credit = str(r.get("credit", ""))
                if not re.fullmatch(r"Authors?:[^\r\n]+", credit) or len(re.findall(r"\bAuthors?:", credit)) != 1:
                    errors.append(f"{p}:{no}: credit is one `Author:` line (a single line with a single `Author:`)")
                if any(d in str(r.get(k, "")) for k in ("credit", "evidence") for d in ("-/", "/-")):
                    errors.append(f"{p}:{no}: credit and evidence may not contain `-/` or `/-` (they are written into a Lean doc comment)")
                if not good_link(str(r.get("evidence", ""))):
                    errors.append(f"{p}:{no}: evidence is an http(s) link to what shows the plagiarism")
            continue
        req = schema["record"]["required"] + schema["record"].get("required_by_tier", {}).get(t, [])
        for k in req:
            if k not in r:
                errors.append(f"{p}:{no}: missing {k}")
        for k, ty in schema["record"]["types"].items():
            if k in r and not isinstance(r[k], {"string": str, "number": (int, float), "boolean": bool}[ty]):
                errors.append(f"{p}:{no}: {k} must be {ty}")
        if r.get("status") != t:
            errors.append(f"{p}:{no}: status {r.get('status')!r} in data/{t}/ (must be {t!r})")
        if r.get("library") != lib:
            errors.append(f"{p}:{no}: library {r.get('library')!r} in a {lib} file")
        if t == "staging" and lib in corpora and not (r.get("source_path") and r.get("context") is not None):
            errors.append(
                f"{p}:{no}: a {lib} record needs source_path and context, or it is never compiled (see schemas/sources.json corpora)"
            )
        if not any(str(r.get("source_url", "")).startswith(s) for s in sources):
            errors.append(f"{p}:{no}: source_url not on the allowlist (schemas/sources.json): {r.get('source_url')}")
        n = r.get("name")
        # The name is a Lean identifier: no whitespace, no commas (the queue passes names comma-separated), no control characters.
        if not isinstance(n, str) or not NAME_RE.fullmatch(n):
            errors.append(f"{p}:{no}: name is not a Lean identifier: {n!r}")
        elif "tombstone" not in r and not re.search(
            r"(?<![\w'])" + re.escape(n.rsplit(".", 1)[-1]) + r"(?![\w'])", str(r.get("statement", ""))
        ):
            errors.append(f"{p}:{no}: statement does not declare {n} (its last component must appear; namespaces may come from context)")
        if n in seen:
            errors.append(f"{p}:{no}: duplicate name in this PR: {n}")
        seen.add(n)
        if t != "trusted":
            if known is None:
                known = trusted_names()
            if n in known:
                errors.append(f"{p}:{no}: {n} is already trusted")
        # a contributor names headlines when adding records; promotion carries them into trusted, many PRs at once
        if r.get("headline") is True and t != "trusted":
            stmt = str(r.get("statement", ""))
            doc = re.search(r"/--(.*?)-/", stmt, re.S)  # the credit is in the declaration's docstring,
            keyword = re.search(r"^\s*(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*?(?:theorem|lemma)\b", stmt, re.M)
            if doc and keyword and doc.start() > keyword.start():
                doc = None  # which comes before the theorem: a doc comment after it belongs to something else
            if not doc or not re.search(r"^\s*Authors?:", doc.group(1), re.M):
                errors.append(f"{p}:{no}: a headline credits its author: an `Author:` line in the statement's docstring")
            headlines.append(str(n))
        if "sorry" in str(r.get("proof", "")) and t == "trusted":
            errors.append(f"{p}:{no}: a trusted record cannot contain sorry")
if len(headlines) > MAX_HEADLINES:
    errors.append(
        f"{len(headlines)} headline records; a PR names at most {MAX_HEADLINES} (the results it is about): {', '.join(headlines[:12])}"
    )
if errors:
    fail("record validation:\n  " + "\n  ".join(errors[:25]) + ("" if len(errors) <= 25 else f"\n  … {len(errors) - 25} more"))
print(f"records OK ({len(seen)} added)")
