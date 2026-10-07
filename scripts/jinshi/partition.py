#!/usr/bin/env python3
"""partition.py [--round K] [--rounds N] [--json OUT] [--list-records] — the tree cut into N disjoint, stable test rounds.

Jinshi (the tree's own soundness tester) is tried on one round of the tree at a time, and a round is opened only when the maintainer
says so. This script says which units are in which round, from the files alone (no Lean runs, no network):

  units     every Lean module of the tree, every record of the data tiers, and the tree's own code
  strata    a unit belongs to one stratum, named by its provenance and folder:
              seed/<Topic>[/<Sub>]        the tree's foundation under Tengoku/Seed/ (SEED.md records where each folder was seeded from, once)
              translated/<Library>[/<Sub>] a library the tree compiles: an intake bundle (data/intake/<library>/) or a legacy generated library
              records/<tier>/<library>    one line of data/<tier>/…jsonl (intake manifests, staging, tentative, trusted)
              custom/<kind>               the tree's own programs: root Lean files, tools/, scripts/, widget/, workflows — never sampled, in every round
            a folder of a seed topic or a library with at least SPLIT modules is its own stratum, so a round draws from every corner of a big folder
  rounds    modules: within each stratum the modules are ordered by sha256("jinshi-v1\n" + path) and dealt out in that order, round
            = rank mod N, so every stratum gives each round its fair share (n/N, rounded) and a round draws from every corner of the tree. That
            deal is FROZEN in tools/jinshi/partition.tsv (--freeze writes it, naming the commit): a module keeps its round for ever, so the
            rounds stay disjoint as the tree grows. A module that is not in the ledger (added after the freeze) gets the hash of its path mod N.
            records: the hash of "<tier>/<library>:<name>" mod N (hundreds of thousands of lines: the hash is even enough, and a record keeps its
            round when its file is split or re-cut). custom code: every round.

Fairness is per stratum, and the report prints every stratum's count per round so an uneven one is visible rather than hidden. --json writes the round's modules and custom files (and per-stratum totals for the records, which are listed only with
--list-records: 676k tentative lines would make the file unreadable).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SALT = "jinshi-v1"
SPLIT = 10  # a sub-folder with this many modules is its own stratum

# SEED.md: the package each seeded folder came from, kept as provenance (every other folder under Seed/ came with the main seed)
SEED_ORIGINS = {
    "Std": "batteries",
    "Tactic/Aesop": "aesop",
    "Meta/Qq": "Qq",
    "Widgets": "proofwidgets",
    "Testing/Random": "plausible",
    "Search/LeanSearchClient": "LeanSearchClient",
    "Meta/ImportGraph": "importGraph",
    "Meta/Cli": "Cli",
}

CUSTOM = [  # (kind, glob)
    ("root-programs", "Tengoku*.lean"),
    ("root-programs", "Tengoku.lean"),
    ("tools", "tools/**/*.lean"),
    ("tools", "tools/**/*.py"),
    ("scripts", "scripts/**/*.py"),
    ("scripts", "scripts/**/*.sh"),
    ("scripts", "scripts/**/*.lean"),
    ("widget", "widget/**/*.ts"),
    ("widget", "widget/**/*.tsx"),
    ("widget", "widget/**/*.js"),
    ("workflows", ".github/workflows/*.yml"),
    ("schemas", "schemas/*.json"),
    ("fixtures", "tools/jinshi/fixtures/**/*.lean"),
]


def bucket(key: str, rounds: int) -> int:
    return int(hashlib.sha256(f"{SALT}\n{key}".encode()).hexdigest(), 16) % rounds


LEDGER = ROOT / "tools" / "jinshi" / "partition.tsv"


def read_ledger() -> tuple[dict[str, int], str]:
    """path -> round, and the commit the ledger was frozen at ('' when there is no ledger)."""
    if not LEDGER.is_file():
        return {}, ""
    rounds: dict[str, int] = {}
    commit = ""
    for line in LEDGER.read_text(encoding="utf-8").splitlines():
        if line.startswith("#"):
            m = re.search(r"commit=([0-9a-f]+)", line)
            commit = m.group(1) if m else commit
            continue
        r, path = line.split("\t", 1)
        rounds[path] = int(r)
    return rounds, commit


def deal(mods: list[dict], rounds: int) -> dict[str, int]:
    """The fair deal: per stratum, modules ordered by the hash of their path, round = rank mod N, with the starting round rotated by the stratum's
    own hash so small strata do not all give their first module to round 0."""
    by: dict[str, list[dict]] = defaultdict(list)
    for u in mods:
        if u["kind"] != "root":
            by[u["stratum"]].append(u)
    out: dict[str, int] = {}
    for stratum, us in by.items():
        us.sort(key=lambda u: hashlib.sha256(f"{SALT}\n{u['path']}".encode()).hexdigest())
        start = bucket(stratum, rounds)
        for i, u in enumerate(us):
            out[u["path"]] = (start + i) % rounds
    return out


def git_commit() -> str:
    try:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return "unknown"


def module_name(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def lean_modules() -> list[dict]:
    """Every module under Tengoku/, with its provenance. Root import files (Tengoku/<Library>.lean, Tengoku/All.lean) are listed as kind=root and
    never sampled: they hold only imports."""
    units = []
    intake = {p.name for p in (ROOT / "data" / "intake").iterdir() if p.is_dir()} if (ROOT / "data" / "intake").is_dir() else set()
    # a library folder's name in data/ is kebab-case; in the tree it is PascalCase
    pascal = {"".join(w.capitalize() for w in lib.split("-")): lib for lib in intake}
    for path in sorted((ROOT / "Tengoku").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        parts = rel.split("/")[1:]  # after Tengoku/
        text = path.read_bytes()
        unit = {"path": rel, "module": module_name(rel), "bytes": len(text), "lines": text.count(b"\n")}
        if len(parts) == 1:  # Tengoku/<X>.lean
            unit.update(kind="root", stratum="custom/root-imports", origin="tree")
        elif parts[0] == "Seed":
            topic = parts[1] if len(parts) > 2 else "(top)"
            sub = parts[2] if len(parts) > 3 else None
            origin = "seed"
            for prefix, pkg in SEED_ORIGINS.items():
                if "/".join(parts[1:]).startswith(prefix + "/"):
                    origin = pkg
            unit.update(kind="seed", topic=topic, sub=sub, origin=origin, stratum=f"seed/{topic}")
        else:
            lib = parts[0]
            sub = parts[1] if len(parts) > 2 else None
            origin = "intake" if lib in pascal else "legacy-generated"
            unit.update(kind="translated", topic=lib, sub=sub, origin=origin, stratum=f"translated/{lib}")
        units.append(unit)
    # split big folders into their sub-folders
    by_sub: dict[tuple[str, str], int] = defaultdict(int)
    for u in units:
        if u.get("sub"):
            by_sub[(u["stratum"], u["sub"])] += 1
    for u in units:
        if u.get("sub") and by_sub[(u["stratum"], u["sub"])] >= SPLIT:
            u["stratum"] = f"{u['stratum']}/{u['sub']}"
    return units


def custom_files() -> list[dict]:
    seen: dict[str, str] = {}
    for kind, pattern in CUSTOM:
        for path in sorted(ROOT.glob(pattern)):
            if path.is_file():
                rel = path.relative_to(ROOT).as_posix()
                if "__pycache__" in rel or rel in seen:
                    continue
                seen[rel] = kind
    return [{"path": rel, "kind": kind, "stratum": f"custom/{kind}", "bytes": os.path.getsize(ROOT / rel)} for rel, kind in seen.items()]


NAME = re.compile(rb'"name"\s*:\s*"((?:[^"\\]|\\.)*)"')


def records(rounds: int, want: int | None, listing: list | None) -> dict[str, dict]:
    """Per stratum records/<tier>/<library>: total lines and how many fall in round `want`. The name is read with a regex, not json.loads:
    676k lines, and only the name is needed."""
    out: dict[str, dict] = {}
    for tier in ("intake", "staging", "tentative", "trusted"):
        base = ROOT / "data" / tier
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.jsonl")):
            rel = path.relative_to(base).as_posix()
            lib = rel.split("/")[0]
            lib = lib[: -len(".jsonl")] if lib.endswith(".jsonl") else lib
            key = f"records/{tier}/{lib}"
            st = out.setdefault(key, {"total": 0, "in_round": 0, "files": 0})
            st["files"] += 1
            with path.open("rb") as fh:
                for lineno, line in enumerate(fh, 1):
                    if not line.strip():
                        continue
                    m = NAME.search(line)
                    name = m.group(1).decode("utf-8", "replace") if m else f"{rel}:{lineno}"
                    st["total"] += 1
                    b = bucket(f"{tier}/{lib}:{name}", rounds)
                    if want is None or b == want:
                        st["in_round"] += 1
                        if listing is not None:
                            listing.append(
                                {"tier": tier, "library": lib, "file": f"data/{tier}/{rel}", "line": lineno, "name": name, "round": b}
                            )
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--round", type=int, default=0, help="the round to list (0-based)")
    ap.add_argument("--rounds", type=int, default=10)
    ap.add_argument("--json", type=Path, help="write the round's manifest here")
    ap.add_argument("--list-records", action="store_true", help="put every record of the round in the manifest too")
    ap.add_argument("--no-records", action="store_true", help="skip the data tiers (fast)")
    ap.add_argument("--freeze", action="store_true", help="deal every module not yet in the ledger and write tools/jinshi/partition.tsv")
    a = ap.parse_args()
    if not 0 <= a.round < a.rounds:
        print(f"--round must be in [0, {a.rounds})", file=sys.stderr)
        return 2

    mods = lean_modules()
    ledger, frozen_at = read_ledger()
    if a.freeze:
        fresh = deal([u for u in mods if u["path"] not in ledger], a.rounds)
        ledger.update(fresh)
        present = {u["path"] for u in mods}
        LEDGER.parent.mkdir(parents=True, exist_ok=True)
        lines = [
            f"# jinshi partition ledger: round<TAB>module path. rounds={a.rounds} salt={SALT} commit={git_commit()} (first freeze: {frozen_at or 'this'})",
            "# A module keeps its round for ever; a module added after a freeze is dealt in at the next --freeze (until then: hash of its path mod rounds).",
        ]
        lines += [f"{ledger[p]}\t{p}" for p in sorted(ledger) if p in present or p not in ledger]
        LEDGER.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"ledger: {LEDGER.relative_to(ROOT)}: {len(fresh)} modules dealt, {len(ledger)} in all", file=sys.stderr)
    unlisted = 0
    for u in mods:
        if u["kind"] == "root":
            u["round"] = None
        elif u["path"] in ledger:
            u["round"] = ledger[u["path"]]
        else:
            u["round"] = bucket(u["path"], a.rounds)
            unlisted += 1
    if unlisted:
        print(
            f"note: {unlisted} modules are not in the ledger (added since the freeze): hashed into rounds; run --freeze to deal them",
            file=sys.stderr,
        )
    custom = custom_files()
    rec_listing: list | None = [] if a.list_records else None
    recs = {} if a.no_records else records(a.rounds, a.round, rec_listing)

    # the report
    strata: dict[str, dict] = {}
    for u in mods:
        st = strata.setdefault(
            u["stratum"],
            {
                "kind": u["kind"],
                "origin": u["origin"],
                "total": 0,
                "in_round": 0,
                "bytes": 0,
                "bytes_in_round": 0,
                "per_round": [0] * a.rounds,
            },
        )
        st["total"] += 1
        st["bytes"] += u["bytes"]
        if u["round"] is not None:
            st["per_round"][u["round"]] += 1
            if u["round"] == a.round:
                st["in_round"] += 1
                st["bytes_in_round"] += u["bytes"]

    def group(prefix: str) -> tuple[int, int, int, int]:
        t = sum(s["total"] for k, s in strata.items() if k.startswith(prefix))
        r = sum(s["in_round"] for k, s in strata.items() if k.startswith(prefix))
        b = sum(s["bytes"] for k, s in strata.items() if k.startswith(prefix))
        br = sum(s["bytes_in_round"] for k, s in strata.items() if k.startswith(prefix))
        return t, r, b, br

    commit = git_commit()
    print(f"# Jinshi partition — round {a.round} of {a.rounds} — {commit[:12]} — salt {SALT}\n")
    print("| class | modules | in round | share | MB | MB in round |")
    print("|---|---:|---:|---:|---:|---:|")
    for name, prefix in (("seed (the tree's foundation)", "seed/"), ("translated libraries", "translated/")):
        t, r, b, br = group(prefix)
        print(f"| {name} | {t} | {r} | {100 * r / max(t, 1):.1f}% | {b / 1e6:.1f} | {br / 1e6:.1f} |")
    print(f"| custom code (every round) | {len(custom)} | {len(custom)} | 100% | {sum(c['bytes'] for c in custom) / 1e6:.2f} | same |")
    if recs:
        for tier in ("intake", "staging", "trusted", "tentative"):
            t = sum(s["total"] for k, s in recs.items() if k.startswith(f"records/{tier}/"))
            r = sum(s["in_round"] for k, s in recs.items() if k.startswith(f"records/{tier}/"))
            if t:
                print(f"| records: {tier} | {t} | {r} | {100 * r / t:.1f}% | | |")
    print(f"\n## Seed, by topic (sub-folders of ≥{SPLIT} modules are their own strata; shown folded)\n")
    print("| topic | origin | modules | in round | share | min/max per round |")
    print("|---|---|---:|---:|---:|---:|")
    folded: dict[str, dict] = {}
    for k, s in strata.items():
        if s["kind"] != "seed":
            continue
        top = "/".join(k.split("/")[:2])
        f = folded.setdefault(top, {"origin": set(), "total": 0, "in_round": 0, "per_round": [0] * a.rounds})
        f["origin"].add(s["origin"])
        f["total"] += s["total"]
        f["in_round"] += s["in_round"]
        f["per_round"] = [x + y for x, y in zip(f["per_round"], s["per_round"])]
    for top, f in sorted(folded.items(), key=lambda kv: -kv[1]["total"]):
        print(
            f"| {top} | {','.join(sorted(f['origin']))} | {f['total']} | {f['in_round']} | {100 * f['in_round'] / f['total']:.1f}% | {min(f['per_round'])}/{max(f['per_round'])} |"
        )
    print("\n## Translated libraries\n")
    print("| library | origin | modules | in round | share | min/max per round |")
    print("|---|---|---:|---:|---:|---:|")
    folded = {}
    for k, s in strata.items():
        if s["kind"] != "translated":
            continue
        top = "/".join(k.split("/")[:2])
        f = folded.setdefault(top, {"origin": s["origin"], "total": 0, "in_round": 0, "per_round": [0] * a.rounds})
        f["total"] += s["total"]
        f["in_round"] += s["in_round"]
        f["per_round"] = [x + y for x, y in zip(f["per_round"], s["per_round"])]
    for top, f in sorted(folded.items(), key=lambda kv: -kv[1]["total"]):
        print(
            f"| {top} | {f['origin']} | {f['total']} | {f['in_round']} | {100 * f['in_round'] / f['total']:.1f}% | {min(f['per_round'])}/{max(f['per_round'])} |"
        )
    print("\n## Custom code (in every round)\n")
    kinds: dict[str, list] = defaultdict(list)
    for c in custom:
        kinds[c["kind"]].append(c)
    for kind, cs in kinds.items():
        print(f"- {kind}: {len(cs)} files, {sum(c['bytes'] for c in cs) / 1e3:.0f} kB")
    if recs:
        print("\n## Records, by tier and library (round share)\n")
        print("| tier | libraries | records | in round |")
        print("|---|---:|---:|---:|")
        for tier in ("intake", "staging", "trusted", "tentative"):
            ks = [k for k in recs if k.startswith(f"records/{tier}/")]
            if ks:
                print(f"| {tier} | {len(ks)} | {sum(recs[k]['total'] for k in ks)} | {sum(recs[k]['in_round'] for k in ks)} |")

    if a.json:
        manifest = {
            "version": 1,
            "salt": SALT,
            "commit": commit,
            "ledger_commit": frozen_at,
            "rounds": a.rounds,
            "round": a.round,
            "strata": strata,
            "modules": [u for u in mods if u["round"] == a.round],
            "roots": [u["path"] for u in mods if u["kind"] == "root"],
            "custom": custom,
            "records": recs,
            "record_list": rec_listing,
        }
        a.json.parent.mkdir(parents=True, exist_ok=True)
        a.json.write_text(json.dumps(manifest, indent=1) + "\n", encoding="utf-8")
        print(
            f"\nmanifest: {a.json} ({len(manifest['modules'])} modules, {len(custom)} custom files"
            + (f", {len(rec_listing)} records" if rec_listing else "")
            + ")"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
