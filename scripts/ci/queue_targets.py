#!/usr/bin/env python3
"""queue_targets.py <base> <head> [--regenerate] — what the merge queue must build.
Clones each touched library's corpus (schemas/sources.json `corpora`) at its
pinned commit into corpora/<library>, runs the generator for every
(library, source_path) the group adds to staging, and prints the candidate
module names, one per line. With --regenerate it regenerates the real modules
of every touched library instead (for the derived-files diff)."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from _git import ROOT, added_lines, changed_files, fail, library_of, load_schema, match

base, head = sys.argv[1], sys.argv[2]
regenerate = "--regenerate" in sys.argv
corpora = load_schema("sources.json").get("corpora", {})


def corpus_dir(lib: str) -> Path:
    spec = corpora.get(lib)
    if not spec:
        fail(f"{lib}: no corpus in schemas/sources.json; its records cannot be compiled")
    d = ROOT / "corpora" / lib
    if not (d / ".git").exists():
        d.parent.mkdir(exist_ok=True)
        subprocess.run(["git", "clone", "-q", "--filter=blob:none", spec["repo"], str(d)], check=True)
        subprocess.run(["git", "-C", str(d), "checkout", "-q", spec["commit"]], check=True)
        print(f"corpus {lib}: {spec['repo']} @ {spec['commit'][:12]}", file=sys.stderr)
    return d


def generate(lib: str, extra: list[str]) -> None:
    cmd = [sys.executable, "scripts/generate.py", "--corpus", str(corpus_dir(lib)), "--libraries", lib, *extra]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    sys.stderr.write(r.stdout[-2000:] + r.stderr[-2000:])
    if r.returncode != 0:
        fail(f"generate.py failed for {lib}: {' '.join(extra)}")


work: dict[str, set[str]] = {}  # library -> source paths added to staging
touched: set[str] = set()  # libraries with any data change (staging or trusted)
for st, p in changed_files(base, head):
    if match(p, ["data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
        lib = library_of(p)
        touched.add(lib)
        for _, text in added_lines(base, head, p):
            try:
                r = json.loads(text)
            except Exception:
                continue
            if "tombstone" in r or not r.get("source_path"):
                continue
            work.setdefault(lib, set()).add(r["source_path"])
    elif match(p, ["data/trusted/*.jsonl"]):
        touched.add(library_of(p))

if regenerate:
    for lib in sorted(touched):
        if lib in corpora:
            generate(lib, [])
    sys.exit(0)


def pascal(s: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in s.replace("_", "-").split("-") if w)


targets: list[str] = []
for lib, paths in sorted(work.items()):
    if lib not in corpora:
        print(f"::warning::{lib}: no corpus, records are data only and not compiled", file=sys.stderr)
        continue
    for sp in sorted(paths):
        generate(lib, ["--candidate", sp])
    for cand in sorted((ROOT / "Tengoku" / pascal(lib)).rglob("_candidate_*.lean")):
        targets.append(".".join(cand.relative_to(ROOT).with_suffix("").parts))
for lib in sorted(touched - set(work)):
    if lib in corpora:
        targets.append(f"Tengoku.{pascal(lib)}")  # tombstones: rebuild the library's modules
print("\n".join(dict.fromkeys(targets)))
