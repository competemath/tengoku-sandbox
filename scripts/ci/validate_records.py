#!/usr/bin/env python3
"""validate_records.py <base> <head> — every added record is well-formed.
Checks only the lines a PR adds to data/*/*.jsonl: JSON, required fields per
tier (schemas/record.schema.json), status matches the tier, library matches
the file, source on the allowlist (schemas/sources.json), no duplicate names
in the PR or against trusted, tombstones point at existing names, file ≤ 50 MB."""

from __future__ import annotations

import json
import re
import sys

from _git import ROOT, added_lines, blob, changed_files, fail, library_of, load_schema, match

MAX_BYTES = 50 * 1024 * 1024
base, head = sys.argv[1], sys.argv[2]
schema = load_schema("record.schema.json")
NAME_RE = re.compile(r"[^\s,\x00-\x1f]+")
sources_doc = load_schema("sources.json")
sources = sources_doc["allowed"]
corpora = sources_doc.get("corpora", {})
errors, seen, names_by_tier = [], set(), {}


def tier(p: str) -> str:
    return p.split("/")[1]


def trusted_names() -> set[str]:
    out = set()
    for f in (ROOT / "data" / "trusted").glob("*.jsonl"):
        for line in f.open("rb"):
            m = re.search(rb'"name"\s*:\s*"([^"]+)"', line)
            if m:
                out.add(m.group(1).decode())
    return out


known = None
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
        if "tombstone" in r:
            for k in schema["tombstone"]["required"]:
                if k not in r:
                    errors.append(f"{p}:{no}: tombstone missing {k}")
            if known is None:
                known = trusted_names()
            if t == "trusted" and r["tombstone"] not in known:
                errors.append(f"{p}:{no}: tombstone for unknown name {r['tombstone']}")
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
        if "sorry" in str(r.get("proof", "")) and t == "trusted":
            errors.append(f"{p}:{no}: a trusted record cannot contain sorry")
if errors:
    fail("record validation:\n  " + "\n  ".join(errors[:25]) + ("" if len(errors) <= 25 else f"\n  … {len(errors) - 25} more"))
print(f"records OK ({len(seen)} added)")
