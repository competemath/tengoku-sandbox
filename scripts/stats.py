#!/usr/bin/env python3
"""Write data/stats.json: what the tree holds, per library and tier.

    scripts/stats.py [--out data/stats.json]

The site's stat pills read this file straight from GitHub (raw, ISR-cached),
so no database is involved in showing what Tengoku contains. Run by the
promote loop before every commit and by the nightly build.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

TIERS = ("trusted", "staging", "tentative")
ATTRIBUTES_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)+")
PROMOTED_RE = re.compile(rb'"promoted_at"\s*:\s*"([^"]+)"')


def count_lines(path: Path) -> int:
    n = 0
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            n += chunk.count(b"\n")
    return n


def statement_key(record: dict) -> str | None:
    """A record's statement without its leading attributes and with its whitespace collapsed: the identity of a theorem across
    tiers. A bundle's manifest line and the harvester's record hold the same statement under different names (the manifest's is
    fully qualified); a promoted record keeps its name but the trusted copy may drop an attribute."""
    st = record.get("statement")
    if not isinstance(st, str) or not st:
        return None
    return " ".join(ATTRIBUTES_RE.sub("", st).split())


def iter_records(path: Path):
    with path.open("rb") as f:
        for line in f:
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r, dict):
                yield r


def count_already_trusted(tentative: Path, trusted: Path | None, manifest: Path | None) -> int:
    """How many records of a library's tentative file are theorems the tree already holds as trusted: in its intake bundle's
    manifest, or as a promoted record. Tentative files are append-only, so a record stays when its library arrives as a bundle
    or when it is promoted; counting it as well counted the theorem twice (56,523 records, 2026-10-15)."""
    names: set[str] = set()
    keys: set[str] = set()
    for path in (trusted, manifest):
        if path is None or not path.exists():
            continue
        for r in iter_records(path):
            if path is trusted and isinstance(r.get("name"), str):
                names.add(r["name"])
            k = statement_key(r)
            if k:
                keys.add(k)
    if not names and not keys:
        return 0
    return sum(1 for r in iter_records(tentative) if r.get("name") in names or statement_key(r) in keys)


def last_promoted(path: Path) -> str | None:
    best = None
    with path.open("rb") as f:
        for line in f:
            m = PROMOTED_RE.search(line)
            if m:
                v = m.group(1).decode()
                if best is None or v > best:
                    best = v
    return best


def collect(root: Path) -> dict:
    libraries: dict[str, dict] = {}
    for tier in TIERS:
        for p in sorted((root / "data" / tier).glob("*.jsonl")):
            lib = libraries.setdefault(p.stem, {t: 0 for t in TIERS})
            lib[tier] = count_lines(p)
            if tier == "trusted":
                lp = last_promoted(p)
                if lp:
                    lib["last_promoted_at"] = lp
    # A library that arrived as a factory bundle (docs/pr-classes.md, intake) has no records: its modules are the content and its manifest
    # lists the theorems the merge queue built. They are trusted by the tree's rule (it builds with them), so they count as trusted here,
    # with `intake` saying how many of a library's trusted theorems are in modules rather than records.
    for m in sorted((root / "data" / "intake").glob("*/manifest.jsonl")):
        lib = libraries.setdefault(m.parent.name, {t: 0 for t in TIERS})
        n = count_lines(m)
        lib["trusted"] += n
        lib["intake"] = n
    # a tentative record of a theorem the tree already trusts is the same theorem, not a second one
    for name, lib in libraries.items():
        tentative = root / "data" / "tentative" / f"{name}.jsonl"
        trusted = root / "data" / "trusted" / f"{name}.jsonl"
        manifest = root / "data" / "intake" / name / "manifest.jsonl"
        if lib["tentative"] and tentative.exists() and (trusted.exists() or manifest.exists()):
            dup = count_already_trusted(tentative, trusted, manifest)
            lib["tentative"] -= dup
            lib["tentative_already_trusted"] = dup
    totals = {t: sum(l[t] for l in libraries.values()) for t in TIERS}
    totals["all"] = sum(totals.values())
    totals["tentative_already_trusted"] = sum(l.get("tentative_already_trusted", 0) for l in libraries.values())
    return {"totals": totals, "libraries": libraries, "library_count": len(libraries)}


def git(root: Path, *args: str) -> str:
    try:
        return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, timeout=30).stdout.strip()
    except Exception:
        return ""


def build(root: Path) -> dict:
    s = collect(root)
    s.update(
        {
            "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "tree_commit": git(root, "rev-parse", "HEAD"),
            "toolchain": (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() else "",
            "last_promoted_at": max((l.get("last_promoted_at", "") for l in s["libraries"].values()), default="") or None,
        }
    )
    return s


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    root = Path(a.root)
    stats = build(root)
    out = Path(a.out) if a.out else root / "data" / "stats.json"
    out.write_text(json.dumps(stats, indent=2, sort_keys=True) + "\n")
    t = stats["totals"]
    print(
        f"{out}: {t['all']} records ({t['trusted']} trusted, {t['staging']} staging, {t['tentative']} tentative) in {stats['library_count']} libraries"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
