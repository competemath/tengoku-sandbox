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

TENGOKU = "https://github.com/competemath/tengoku"


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


def slug(url: str) -> str:
    m = re.match(r"https?://github\.com/([^/]+)/([^/#?]+?)(?:\.git)?/?$", url.strip())
    return f"{m.group(1)}/{m.group(2)}".lower() if m else ""


def purl(url: str, rev: str) -> str | None:
    s = slug(url)
    return f"pkg:github/{s}@{rev}" if s else None


def licence(spdx: str | None) -> list[dict]:
    return [{"license": {"id": spdx}}] if spdx and re.fullmatch(r"[A-Za-z0-9.+-]+", spdx) else []


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--commit", required=True)
    ap.add_argument("--version", required=True)
    a = ap.parse_args()
    commit = subprocess.run(["git", "rev-parse", a.commit], capture_output=True, text=True, check=True).stdout.strip()

    # licences of seeded packages, by upstream repository (LICENSE-THIRD-PARTY.md, section 1)
    third = show(commit, "LICENSE-THIRD-PARTY.md", missing_ok=True)
    seed_licence = {}
    for m in re.finditer(r"^\|[^|]*\|\s*\[[^\]]*\]\((https://github\.com/[^)]+)\)\s*\|\s*([^|]+?)\s*\|", third, re.M):
        seed_licence[slug(m.group(1))] = m.group(2)

    components: list[dict] = []
    toolchain = show(commit, "lean-toolchain").strip()  # leanprover/lean4:v4.34.0-rc2
    lean_tag = toolchain.split(":", 1)[1]
    components.append(
        {
            "type": "application",
            "bom-ref": "lean4",
            "name": "lean4",
            "version": lean_tag,
            "purl": f"pkg:github/leanprover/lean4@{lean_tag}",
            "licenses": licence("Apache-2.0"),
            "properties": [{"name": "tengoku:role", "value": "toolchain"}],
        }
    )
    for m in re.finditer(
        r"^\|\s*([^|\s][^|]*?)\s*\|\s*(https?://[^|\s]+)\s*\|\s*([0-9a-f]{40})\s*\|\s*`?([^|`]+)`?\s*\|", show(commit, "SEED.md"), re.M
    ):
        name, origin, rev, mapped = m.groups()
        components.append(
            {
                "type": "library",
                "bom-ref": f"seed:{name}",
                "name": name,
                "version": rev,
                "purl": purl(origin, rev),
                "licenses": licence(seed_licence.get(slug(origin))),
                "externalReferences": [{"type": "vcs", "url": origin}],
                "properties": [{"name": "tengoku:role", "value": "seed"}, {"name": "tengoku:path", "value": mapped.strip()}],
            }
        )
    registry = json.loads(show(commit, "schemas/sources.json"))
    corpora, licences = registry.get("corpora", {}), registry.get("licences", {})

    def licence_for(url: str) -> str | None:
        return next((v for k, v in sorted(licences.items(), key=lambda kv: -len(kv[0])) if url.startswith(k.rstrip("/"))), None)

    counts: dict[str, int] = {}
    origin: dict[str, str] = {}
    for f in files(commit, "data/trusted"):
        lib = f.removeprefix("data/trusted/").split("/")[0].removesuffix(".jsonl")
        if not f.endswith(".jsonl") or lib.startswith("mathlib-"):
            continue
        for line in show(commit, f).split("\n"):
            if line.strip() and '"tombstone"' not in line:
                counts[lib] = counts.get(lib, 0) + 1
                if lib not in origin:
                    origin[lib] = str(json.loads(line).get("source_url", ""))
    for lib in sorted(counts):
        props = [{"name": "tengoku:role", "value": "source"}, {"name": "tengoku:trusted-records", "value": str(counts[lib])}]
        if lib in corpora:
            spec = corpora[lib]
            components.append(
                {
                    "type": "library",
                    "bom-ref": f"source:{lib}",
                    "name": lib,
                    "version": spec["commit"],
                    "purl": purl(spec["repo"], spec["commit"]),
                    "licenses": licence(licence_for(spec["repo"])),
                    "externalReferences": [{"type": "vcs", "url": spec["repo"]}],
                    "properties": props,
                }
            )
        else:
            src = origin.get(lib, "")
            ref = [{"type": "website", "url": re.match(r"https?://[^/]+(/[^#?]*)?", src).group(0)}] if src.startswith("http") else []
            components.append(
                {
                    "type": "data",
                    "bom-ref": f"source:{lib}",
                    "name": lib,
                    "licenses": licence(licence_for(src)),
                    "externalReferences": ref,
                    "properties": props,
                }
            )
    for c in components:
        for k in ("purl", "licenses", "externalReferences"):
            if not c.get(k):
                c.pop(k, None)
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
