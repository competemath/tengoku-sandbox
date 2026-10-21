#!/usr/bin/env python3
"""sbom.py --commit C --version V — the bill of materials of a Tengoku release, as CycloneDX 1.5 JSON on stdout.

Everything is read from the commit itself (git show), so the bill describes exactly what the release holds:
- the Lean toolchain (lean-toolchain);
- every package the tree was seeded from (SEED.md: upstream and exact revision; licence from LICENSE-THIRD-PARTY.md);
- every library whose trusted records the tree holds (data/trusted/<library>…): with a corpus in
  schemas/sources.json, its repository and pinned commit; otherwise (CompeteMath's own problems) its records'
  source; licence from schemas/sources.json `licences`; the number of records. The mathlib-* files are search
  metadata for the seed, which is listed above.
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import subprocess
import uuid
from collections.abc import Iterator

TENGOKU = "https://github.com/competemath/tengoku"
ROLE = "tengoku:role"
# a revision to describe: letters, digits and the few punctuation marks of a ref, never a leading `-` (git would read it as an option)
REVISION = re.compile(r"[0-9A-Za-z][0-9A-Za-z._/@^~{}-]*")
LINK = re.compile(r"\[[^\]]*\]\((https://github\.com/[^)]+)\)")
SEED_ORIGIN = re.compile(r"https?://[^|\s]+")
SEED_REV = re.compile(r"[0-9a-f]{40}")
SEED_PATH = re.compile(r"`?([^`]+)`?")


def show(commit: str, path: str, missing_ok: bool = False) -> str:
    r = subprocess.run(["git", "show", f"{commit}:{path}"], capture_output=True, text=True)
    if r.returncode != 0:
        if missing_ok:
            return ""
        raise SystemExit(f"{path} is not in {commit}: {r.stderr.strip()}")
    return r.stdout


def files(commit: str, path: str) -> list[str]:
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", commit, path], capture_output=True, text=True, check=True).stdout
    return [f for f in out.split("\n") if f]


def resolve(revision: str) -> str:
    """The commit a revision names; a revision that is not plain ref syntax is refused before git sees it."""
    if not REVISION.fullmatch(revision):
        raise SystemExit(f"not a revision: {revision!r}")
    r = subprocess.run(["git", "rev-parse", "--verify", "--end-of-options", f"{revision}^{{commit}}"], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"not a commit: {revision}: {r.stderr.strip()}")
    return r.stdout.strip()


def slug(url: str) -> str:
    m = re.match(r"https?://github\.com/([^/]+)/([^/#?]+?)(?:\.git)?/?$", url.strip())
    return f"{m.group(1)}/{m.group(2)}".lower() if m else ""


def purl(url: str, rev: str) -> str | None:
    s = slug(url)
    return f"pkg:github/{s}@{rev}" if s else None


def licence(spdx: str | None) -> list[dict]:
    return [{"license": {"id": spdx}}] if spdx and re.fullmatch(r"[A-Za-z0-9.+-]+", spdx) else []


def table_rows(text: str) -> Iterator[list[str]]:
    """The cells of every row of every markdown table in the text."""
    for line in text.splitlines():
        if line.startswith("|"):
            yield [cell.strip() for cell in line.strip().strip("|").split("|")]


def seed_licences(third: str) -> dict[str, str]:
    """Licences of the seeded packages, by upstream repository (LICENSE-THIRD-PARTY.md, section 1)."""
    found = {}
    for cells in table_rows(third):
        link = LINK.fullmatch(cells[1]) if len(cells) >= 3 else None
        if link and cells[2]:
            found[slug(link.group(1))] = cells[2]
    return found


def toolchain_component(commit: str) -> dict:
    lean_tag = show(commit, "lean-toolchain").strip().split(":", 1)[1]  # leanprover/lean4:v4.34.0-rc2
    return {
        "type": "application",
        "bom-ref": "lean4",
        "name": "lean4",
        "version": lean_tag,
        "purl": f"pkg:github/leanprover/lean4@{lean_tag}",
        "licenses": licence("Apache-2.0"),
        "properties": [{"name": ROLE, "value": "toolchain"}],
    }


def seed_components(commit: str, licences: dict[str, str]) -> list[dict]:
    """One component per package the tree was seeded from (SEED.md: name, upstream, exact revision, where it went)."""
    out = []
    for cells in table_rows(show(commit, "SEED.md")):
        if len(cells) < 4 or not cells[0] or not SEED_ORIGIN.fullmatch(cells[1]) or not SEED_REV.fullmatch(cells[2]):
            continue
        mapped = SEED_PATH.fullmatch(cells[3])
        if not mapped:
            continue
        name, origin, rev = cells[0], cells[1], cells[2]
        out.append(
            {
                "type": "library",
                "bom-ref": f"seed:{name}",
                "name": name,
                "version": rev,
                "purl": purl(origin, rev),
                "licenses": licence(licences.get(slug(origin))),
                "externalReferences": [{"type": "vcs", "url": origin}],
                "properties": [{"name": ROLE, "value": "seed"}, {"name": "tengoku:path", "value": mapped.group(1).strip()}],
            }
        )
    return out


def trusted_records(commit: str) -> dict[str, list[dict]]:
    """library -> its trusted records, a record whose name a tombstone retracts left out. The mathlib-* files are search metadata for the seed."""
    records: dict[str, list[dict]] = {}
    gone: set[str] = set()
    for f in files(commit, "data/trusted"):
        lib = f.removeprefix("data/trusted/").split("/")[0].removesuffix(".jsonl")
        if not f.endswith(".jsonl") or lib.startswith("mathlib-"):
            continue
        for line in show(commit, f).split("\n"):
            if not line.strip():
                continue
            r = json.loads(line)
            if "tombstone" in r:  # the key, not the word: a proof or url may mention "tombstone"
                gone.add(r["tombstone"])
            else:
                records.setdefault(lib, []).append(r)
    live = {lib: [r for r in rows if r.get("name") not in gone] for lib, rows in records.items()}
    return {lib: rows for lib, rows in live.items() if rows}


def source_component(lib: str, rows: list[dict], registry: dict) -> dict:
    """A library whose records the tree holds: a compiled one by its repository and commit, any other by its records' own source."""
    corpora = registry.get("corpora", {})
    licences = registry.get("licences", {})

    def licence_for(url: str) -> str | None:
        return next((v for k, v in sorted(licences.items(), key=lambda kv: -len(kv[0])) if url.startswith(k.rstrip("/"))), None)

    props = [{"name": ROLE, "value": "source"}, {"name": "tengoku:trusted-records", "value": str(len(rows))}]
    if lib in corpora:
        spec = corpora[lib]
        return {
            "type": "library",
            "bom-ref": f"source:{lib}",
            "name": lib,
            "version": spec["commit"],
            "purl": purl(spec["repo"], spec["commit"]),
            "licenses": licence(licence_for(spec["repo"])),
            "externalReferences": [{"type": "vcs", "url": spec["repo"]}],
            "properties": props,
        }
    src = str(rows[0].get("source_url", ""))
    site = re.match(r"https?://[^/]+(/[^#?]*)?", src)
    return {
        "type": "data",
        "bom-ref": f"source:{lib}",
        "name": lib,
        "licenses": licence(licence_for(src)),
        "externalReferences": [{"type": "website", "url": site.group(0)}] if site else [],
        "properties": props,
    }


def components_of(commit: str) -> list[dict]:
    registry = json.loads(show(commit, "schemas/sources.json"))
    components = [
        toolchain_component(commit),
        *seed_components(commit, seed_licences(show(commit, "LICENSE-THIRD-PARTY.md", missing_ok=True))),
    ]
    components += [source_component(lib, rows, registry) for lib, rows in sorted(trusted_records(commit).items())]
    for c in components:
        for k in ("purl", "licenses", "externalReferences"):
            if not c.get(k):
                c.pop(k, None)
    return components


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--commit", required=True)
    ap.add_argument("--version", required=True)
    a = ap.parse_args()
    commit = resolve(a.commit)
    components = components_of(commit)
    bom = {
        "bomFormat": "CycloneDX",
        "specVersion": "1.5",
        "serialNumber": f"urn:uuid:{uuid.uuid4()}",
        "version": 1,
        "metadata": {
            "timestamp": datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
            "tools": {"components": [{"type": "application", "name": "tengoku scripts/sbom.py"}]},
            "component": {
                "type": "library",
                "bom-ref": "tengoku",
                "name": "tengoku",
                "version": a.version,
                "purl": f"pkg:github/competemath/tengoku@{commit}",
                "licenses": licence("Apache-2.0"),
                "externalReferences": [{"type": "vcs", "url": TENGOKU}],
            },
        },
        "components": components,
        "dependencies": [{"ref": "tengoku", "dependsOn": [c["bom-ref"] for c in components]}],
    }
    print(json.dumps(bom, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
