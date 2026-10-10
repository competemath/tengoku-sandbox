#!/usr/bin/env python3
"""dataset_audit.py tengoku-dataset.jsonl.gz — counts the things the data card (docs/data.md) says about a release.

Every number on that page comes from this script, so a reader can recount it and the next release can be compared.
"""

from __future__ import annotations

import gzip
import json
import re
import sys
from collections import Counter, defaultdict

STATEMENT_KIND = re.compile(r"\s*(theorem|lemma|import)\b")
DECLARED_NAME = re.compile(r"\s*(?:theorem|lemma)\s+(\S+)")
SUBSCRIPT = re.compile("[₀-₉ₐ-ₜ]")
SOURCE_DIR = re.compile(r"/blob/[0-9a-f]{40}/([^/#]+)")


def main(path: str) -> None:
    rows = names = empty = 0
    libs: Counter[str] = Counter()
    toolchains: Counter[str] = Counter()
    kinds: Counter[tuple[str, str]] = Counter()
    statements_by_name: dict[str, set[str]] = defaultdict(set)
    reserved: Counter[str] = Counter()
    mismatched = subscripts = native = 0
    sorry: list[tuple[str, str]] = []
    sources: Counter[str] = Counter()
    with gzip.open(path, "rt", encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            rows += 1
            libs[r["library"]] += 1
            toolchains[r["toolchain"]] += 1
            statement, proof = r["statement"] or "", r["proof"] or ""
            empty += not proof.strip()
            kind = STATEMENT_KIND.match(statement)
            kinds[(r["library"], kind.group(1) if kind else "bare type")] += 1
            statements_by_name[r["name"]].add(statement)
            for k in ("credit", "upstream", "credit_corrected_evidence", "headline"):
                reserved[k] += bool(r.get(k))
            declared = DECLARED_NAME.match(statement)
            if declared:
                n = declared.group(1)
                if not (n == r["name"] or n.endswith("." + r["name"]) or r["name"].endswith("." + n)):
                    mismatched += 1
                    subscripts += bool(SUBSCRIPT.search(n))
            text = proof + " " + statement
            native += "native_decide" in text
            if re.search(r"\bsorry\b", text):
                sorry.append((r["library"], r["name"]))
            m = SOURCE_DIR.search(r["source_url"])
            if m and r["library"] == "mathlib":
                sources[m.group(1)] += 1
                for part in ("Archive/Imo/", "Archive/Wiedijk100Theorems/"):
                    sources[part.rstrip("/")] += part in r["source_url"]
    names = len(statements_by_name)
    print(
        f"records {rows:,}; distinct names {names:,}; names with more than one statement {sum(len(v) > 1 for v in statements_by_name.values()):,}"
    )
    print("per library:", dict(libs))
    print("toolchains:", dict(toolchains))
    print(f"empty proofs {empty:,}; native_decide {native}; sorry {sorry}")
    print("statements by kind:", dict(sorted(kinds.items(), key=lambda kv: -kv[1])))
    print("reserved fields set (credit, upstream, credit_corrected_evidence, headline):", dict(reserved))
    print(f"name differs from the declared name {mismatched:,} (a Unicode subscript in the declared name: {subscripts:,})")
    print(
        "Mathlib records by source directory (Archive, MathlibTest, Counterexamples; Archive/Imo and Archive/Wiedijk100Theorems are inside Archive):"
    )
    print({k: sources[k] for k in ("Mathlib", "Archive", "Archive/Imo", "Archive/Wiedijk100Theorems", "MathlibTest", "Counterexamples")})


if __name__ == "__main__":
    main(sys.argv[1])
