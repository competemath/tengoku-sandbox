#!/usr/bin/env python3
"""snapshot.py --out DIR [--previous PREV] — a citable snapshot of the library: the dataset and its manifest.

Writes DIR/tengoku-dataset.jsonl.gz (one line per trusted record: what it states, its proof, where it came from,
its licence and credit; retracted records left out, corrected credits applied) and DIR/snapshot.json (the version,
date, commit, toolchain, counts per library, the record fields and the dataset's sha256). The snapshot workflow
publishes both as the release vX.Y.Z, so a paper can cite exactly the library it used.

The version is decided by comparing with the previous release (PREV holds its snapshot.json and dataset), never
by hand:
  X (major)  the toolchain changed, or a field was removed from the records: whoever compiles or reads the dataset
             has to act
  Y (minor)  theorems were added (new or newly trusted), or records gained a field
  Z (patch)  only corrections: retractions, credit corrections, fixes to existing records
No change to the dataset or the toolchain: no new version (DIR/unchanged is written and the workflow publishes
nothing). The first release is 1.0.0."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CREDIT_RE = re.compile(r"^\s*(Authors?:.*)$", re.M)


def lines(p: Path):
    for line in p.read_text(encoding="utf-8").splitlines():
        if line.strip():
            yield json.loads(line)


def licence_of(source_url: str, licences: dict[str, str]) -> str | None:
    best = max((prefix for prefix in licences if source_url.startswith(prefix)), key=len, default=None)
    return licences[best] if best else None


def credit_of(statement: str) -> str | None:
    doc = re.search(r"/--(.*?)-/", statement, re.S)  # the docstring, even after a leading ordinary comment
    found = CREDIT_RE.findall(doc.group(1)) if doc else []
    return " ".join(c.strip() for c in found) or None


def library_files(root: Path, tier: str) -> dict[str, list[Path]]:
    """library -> its files in data/<tier>/ (the flat file and any per-PR files)."""
    out: dict[str, list[Path]] = {}
    base = root / "data" / tier
    if not base.is_dir():
        return out
    for f in sorted(base.glob("*.jsonl")):
        out.setdefault(f.stem, []).append(f)
    for d in sorted(p for p in base.iterdir() if p.is_dir()):
        out.setdefault(d.name, []).extend(sorted(d.glob("*.jsonl")))
    return out


def dataset(root: Path) -> tuple[list[dict], dict[str, dict[str, int]]]:
    sources = json.loads((root / "schemas" / "sources.json").read_text(encoding="utf-8"))
    licences = sources.get("licences", {})
    records: list[dict] = []
    counts: dict[str, dict[str, int]] = {}
    for tier in ("trusted", "staging", "tentative"):
        for library, files in library_files(root, tier).items():
            retracted, corrected, kept = set(), {}, []
            for f in files:
                for r in lines(f):
                    if "tombstone" in r:
                        retracted.add(r["tombstone"])
                    elif "credit_correction" in r:  # the newest by date, whatever file it is in
                        name, at = r["credit_correction"], str(r.get("at", ""))
                        if name not in corrected or at >= corrected[name][0]:
                            corrected[name] = (at, r.get("credit"), r.get("evidence"))
                    elif "tombstone_note" not in r and "name" in r:
                        kept.append(r)
            live = [r for r in kept if r["name"] not in retracted]
            counts.setdefault(library, {})[tier] = len(live)
            if tier != "trusted":
                continue
            for r in live:
                _, credit, evidence = corrected.get(r["name"], (None, credit_of(str(r.get("statement", ""))), None))
                row = {
                    "name": r["name"],
                    "library": library,
                    "statement": r.get("statement"),
                    "proof": r.get("proof"),
                    "source_url": r.get("source_url"),
                    "licence": licence_of(str(r.get("source_url", "")), licences),
                    "credit": credit,
                    "toolchain": r.get("toolchain"),
                    "promoted_at": r.get("promoted_at"),
                    # every row has every field (null or false when it does not apply), so the fields change only
                    # when this code does: a release's version compares them
                    "credit_corrected_evidence": evidence or None,
                    "headline": r.get("headline") is True,
                    "upstream": r.get("upstream") or None,
                }
                records.append(row)
    return records, counts


FIRST_VERSION = "1.0.0"


def previous_release(prev: Path | None) -> tuple[dict, set[str]] | None:
    """The previous release's manifest and the names of its records, or None when there is none."""
    if prev is None or not (prev / "snapshot.json").is_file():
        return None
    manifest = json.loads((prev / "snapshot.json").read_text(encoding="utf-8"))
    raw = gzip.decompress((prev / manifest["dataset"]["file"]).read_bytes()).decode("utf-8")
    return manifest, {json.loads(x)["name"] for x in raw.splitlines() if x.strip()}


def next_version(
    previous: tuple[dict, set[str]] | None, names: set[str], fields: list[str], toolchain: str | None, raw_sha: str
) -> str | None:
    """The version of this snapshot, or None when nothing changed since the previous release (module docstring)."""
    if previous is None:
        return FIRST_VERSION
    old, old_names = previous
    major, minor, patch = (int(x) for x in old["version"].split("."))
    if old.get("toolchain") != toolchain or set(old.get("fields", [])) - set(fields):
        return f"{major + 1}.0.0"
    if old["dataset"].get("uncompressed_sha256") == raw_sha:
        return None
    if names - old_names or set(fields) - set(old.get("fields", [])):
        return f"{major}.{minor + 1}.0"
    return f"{major}.{minor}.{patch + 1}"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--root", default=str(ROOT))
    ap.add_argument("--previous", help="a directory with the previous release's snapshot.json and dataset")
    args = ap.parse_args()
    root, out = Path(args.root), Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    records, counts = dataset(root)
    text = "".join(
        json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in sorted(records, key=lambda r: (r["library"], r["name"]))
    )
    raw = text.encode("utf-8")
    path = out / "tengoku-dataset.jsonl.gz"  # the file the release publishes, and the one the manifest hashes
    path.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))  # mtime 0: the same records give the same bytes
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True).stdout.strip() or None
    toolchain = (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() else None
    fields = sorted({k for row in records for k in row})
    version = next_version(
        previous_release(Path(args.previous) if args.previous else None),
        {r["name"] for r in records},
        fields,
        toolchain,
        hashlib.sha256(raw).hexdigest(),
    )
    if version is None:
        (out / "unchanged").write_text("the dataset and toolchain are those of the previous release\n")
        print("unchanged since the previous release: no new version")
        return
    manifest = {
        "version": version,
        "date": time.strftime("%Y-%m-%d", time.gmtime()),
        "commit": commit,
        "toolchain": toolchain,
        "fields": fields,
        "dataset": {
            "file": path.name,
            "records": len(records),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "uncompressed_sha256": hashlib.sha256(raw).hexdigest(),
        },
        "libraries": {k: counts[k] for k in sorted(counts)},
        "totals": {t: sum(c.get(t, 0) for c in counts.values()) for t in ("trusted", "staging", "tentative")},
    }
    (out / "snapshot.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"v{version} ({manifest['date']}): {len(records)} trusted records, sha256 {manifest['dataset']['sha256'][:16]}…")


if __name__ == "__main__":
    main()
