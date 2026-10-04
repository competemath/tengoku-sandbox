#!/usr/bin/env python3
"""snapshot.py --out DIR [--previous PREV] — a citable snapshot of the library: the dataset and its manifest.

Writes DIR/tengoku-dataset.jsonl.gz (one line per trusted record: what it states, its proof, where it came from,
its licence and credit; retracted records left out, corrected credits applied) and DIR/snapshot.json (the version,
date, commit, toolchain, counts per library, the record fields and the dataset's sha256). The snapshot workflow
publishes both as the release vX.Y.Z, so a paper can cite exactly the library it used. With --notes it also writes
the release notes: what changed since the previous release, and what upgrading means.

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


# every row has every field (null or false when it does not apply), so the fields change only when this code does:
# a release's version compares them
FIELDS = (
    "name",
    "library",
    "statement",
    "proof",
    "source_url",
    "licence",
    "credit",
    "toolchain",
    "promoted_at",
    "credit_corrected_evidence",
    "headline",
    "upstream",
)


def dataset(root: Path) -> tuple[list[dict], dict[str, dict[str, int]]]:
    sources = json.loads((root / "schemas" / "sources.json").read_text(encoding="utf-8"))
    licences = sources.get("licences", {})
    records: list[dict] = []
    counts: dict[str, dict[str, int]] = {}
    for tier in ("trusted", "staging", "tentative"):
        # a library's records can be spread over several files (Mathlib's are data/trusted/mathlib-*.jsonl), so the
        # retractions and corrections of a tier apply across all its files, and a record counts for the library it
        # names (the file's name only when it names none)
        retracted, corrected, kept = set(), {}, []
        for stem, files in library_files(root, tier).items():
            for f in files:
                for r in lines(f):
                    if "tombstone" in r:
                        retracted.add(r["tombstone"])
                    elif "credit_correction" in r:  # the newest by date, whatever file it is in
                        name, at = r["credit_correction"], str(r.get("at", ""))
                        if name not in corrected or at >= corrected[name][0]:
                            corrected[name] = (at, r.get("credit"), r.get("evidence"))
                    elif "tombstone_note" not in r and "name" in r:
                        kept.append((r.get("library") or stem, r))
        for library, r in kept:
            if r["name"] in retracted:
                continue
            counts.setdefault(library, {})
            counts[library][tier] = counts[library].get(tier, 0) + 1
            if tier != "trusted":
                continue
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
                "credit_corrected_evidence": evidence or None,
                "headline": r.get("headline") is True,
                "upstream": r.get("upstream") or None,
            }
            assert tuple(row) == FIELDS
            records.append(row)
    return records, counts


FIRST_VERSION = "1.0.0"


def previous_release(prev: Path | None) -> tuple[dict, dict[str, dict]] | None:
    """The previous release's manifest and its records by name, or None when there is none."""
    if prev is None or not (prev / "snapshot.json").is_file():
        return None
    manifest = json.loads((prev / "snapshot.json").read_text(encoding="utf-8"))
    raw = gzip.decompress((prev / manifest["dataset"]["file"]).read_bytes()).decode("utf-8")
    rows = (json.loads(x) for x in raw.splitlines() if x.strip())
    return manifest, {r["name"]: r for r in rows}


def next_version(
    previous: tuple[dict, dict[str, dict]] | None, names: set[str], fields: list[str], toolchain: str | None, raw_sha: str
) -> str | None:
    """The version of this snapshot, or None when nothing changed since the previous release (module docstring)."""
    if previous is None:
        return FIRST_VERSION
    old, old_rows = previous
    old_names = set(old_rows)
    major, minor, patch = (int(x) for x in old["version"].split("."))
    if old.get("toolchain") != toolchain or set(old.get("fields", [])) - set(fields):
        return f"{major + 1}.0.0"
    if old["dataset"].get("uncompressed_sha256") == raw_sha:
        return None
    if names - old_names or set(fields) - set(old.get("fields", [])):
        return f"{major}.{minor + 1}.0"
    return f"{major}.{minor}.{patch + 1}"


def by_library(rows: list[dict], top: int = 5) -> str:
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["library"]] = counts.get(r["library"], 0) + 1
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    shown = ", ".join(f"{lib} {n:,}" for lib, n in ranked[:top])
    return shown + (f", and {len(ranked) - top} more libraries" if len(ranked) > top else "")


def release_notes(
    version: str, previous: tuple[dict, dict[str, dict]] | None, records: list[dict], toolchain: str | None, fields: list[str]
) -> str:
    """The release notes: what changed since the previous release, and what upgrading means. Written from the same
    comparison that chose the version number, so the notes and the number always agree."""
    if previous is None:
        return (
            f"## What is in v{version}\n\n"
            f"The first release: {len(records):,} trusted theorems from {len({r['library'] for r in records})} libraries "
            f"({by_library(records)}), on `{toolchain}`.\n\n"
            "## Upgrade impact\n\nNone: this is the first release.\n"
        )
    old, old_rows = previous
    rows = {r["name"]: r for r in records}
    added = [rows[n] for n in sorted(set(rows) - set(old_rows))]
    retracted = sorted(set(old_rows) - set(rows))
    corrected = sorted(n for n in set(rows) & set(old_rows) if rows[n] != old_rows[n])
    lines = [f"## What changed since v{old['version']}", ""]
    lines.append(f"- **Added:** {len(added):,} trusted theorems" + (f" ({by_library(added)})." if added else "."))
    lines.append(
        f"- **Retracted:** {len(retracted):,}"
        + (f": {', '.join(f'`{n}`' for n in retracted[:10])}{' …' if len(retracted) > 10 else ''}." if retracted else ".")
    )
    lines.append(
        f"- **Corrected:** {len(corrected):,} existing theorems (a credit or another field changed)"
        + ("." if not corrected else f", e.g. `{corrected[0]}`.")
    )
    if old.get("toolchain") != toolchain:
        lines.append(f"- **Toolchain:** `{old.get('toolchain')}` → `{toolchain}`.")
    else:
        lines.append(f"- **Toolchain:** unchanged, `{toolchain}`.")
    gone, new = sorted(set(old.get("fields", [])) - set(fields)), sorted(set(fields) - set(old.get("fields", [])))
    lines.append(
        "- **Record fields:** "
        + (
            "; ".join(
                x
                for x in (
                    f"added {', '.join(f'`{f}`' for f in new)}" if new else "",
                    f"removed {', '.join(f'`{f}`' for f in gone)}" if gone else "",
                )
                if x
            )
            or "unchanged"
        )
        + "."
    )
    lines += ["", "## Upgrade impact", ""]
    if version.endswith(".0.0"):
        why = []
        if old.get("toolchain") != toolchain:
            why.append(f"the Lean toolchain changed: anything built against v{old['version']} must be rebuilt on `{toolchain}`")
        if gone:
            why.append(f"record fields were removed ({', '.join(gone)}): code reading the dataset must stop expecting them")
        lines.append("Major version: " + "; ".join(why) + ".")
    elif version.endswith(".0"):
        what = []
        if added:
            what.append(f"{len(added):,} theorems were added")
        if new:
            what.append(f"records gained {', '.join(f'`{f}`' for f in new)}")
        lines.append(
            "Minor version: "
            + " and ".join(what)
            + "; nothing is renamed and no field is removed, so upgrading is safe"
            + (", except that the retracted theorems above are gone." if retracted else ".")
        )
    else:
        lines.append(
            "Patch: corrections only (retractions and credit corrections); no theorem was added"
            + (". Check that you do not rely on the retracted theorems above." if retracted else ".")
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--root", default=str(ROOT))
    ap.add_argument("--previous", help="a directory with the previous release's snapshot.json and dataset")
    ap.add_argument("--notes", help="where to write the release notes (markdown); kept out of --out, which is published")
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
    fields = sorted(FIELDS)  # not read from the rows: a release with no records keeps the same fields
    previous = previous_release(Path(args.previous) if args.previous else None)
    version = next_version(
        previous,
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
    if args.notes:
        Path(args.notes).write_text(release_notes(version, previous, records, toolchain, fields), encoding="utf-8")
    print(f"v{version} ({manifest['date']}): {len(records)} trusted records, sha256 {manifest['dataset']['sha256'][:16]}…")


if __name__ == "__main__":
    main()
