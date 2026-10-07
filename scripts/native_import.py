#!/usr/bin/env python3
"""native_import.py — turn trusted records into modules of `Tengoku/Native/` (docs/native.md).

  native_import.py RECORDS.jsonl --out DIR [--source competemath] [--exclude NAME ...] [--max-per-module N]

Native is hand-written or Leak-proved novel content, as Lean modules. CompeteMath's own certified theorems are records (data/trusted/competemath.jsonl, written for
`import Mathlib`); this makes them modules of the tree: `Tengoku/Native/<Source>/<Area>.lean`. A record is LEFT OUT, never rewritten to fit, when it
  - trusts the compiler or is unfinished (`native_decide`, `ofReduceBool`, `sorry`: the words the allow-list lint refuses, see scripts/ci/allowlist.py),
  - has no `theorem`/`lemma` of its own, or names something this module already has;
and the modules are checked afterwards by compiling them (the merge queue does it for the PR; Leak IV for a draft). Every record sits in a namespace of its own,
`Native.<Source>.P<N>` for `https://competemath.com/practice/problems/N` (`P<N>_2` for a second record of the problem), so a helper definition or an `open`/`set_option` in front of the theorem cannot touch
another record, and gets the docstring `competemath.com problem N`. The area of a record (the module it goes to) is guessed from the words of its statement; since Native
is novel content it can be reorganised freely (an isnad id never depends on the module).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HEADER = "/-\nAuthors: {authors}\n-/\nimport Tengoku\n\n"
UNSAFE = re.compile(r"(?<![\w'!?])(native_decide|ofReduceBool|reduceBool|trustCompiler|sorry|sorryAx)(?![\w'!?])")
DECL_MODIFIERS = {"private", "protected", "noncomputable", "nonrec", "public", "meta", "unsafe", "partial"}
# the first rule that matches decides the area
AREAS = [
    (
        "Combinatorics",
        r"\.card\b|Finset\.|Fintype\.|Nat\.choose|\.choose|derange|Equiv\.Perm|Nat\.centralBinom|stirling|Finset\.powerset|Nat\.fib|tile|SimpleGraph",
    ),
    ("Polynomials", r"Polynomial|\.roots|\.eval\b|\.degree|Complex\.exp|Complex\.abs"),
    ("LinearAlgebra", r"Matrix|LinearMap|Module\b|\.det\b|Submodule|FiniteDimensional"),
    (
        "Analysis",
        r"Real\.(?:sin|cos|tan|exp|log|sqrt|pi)|deriv|HasDerivAt|∫|intervalIntegral|Tendsto|Filter|Continuous|iteratedDeriv|tsum|∑'|Real\.sinh",
    ),
    ("NumberTheory", r"Nat\.Prime|Prime\b|Nat\.gcd|Nat\.lcm|ZMod|Int\.emod|Nat\.divisors|Nat\.digits|orderOf|padicVal|∣|% "),
    ("Inequalities", r"∀ [a-z]+(?: [a-z]+)* : ℝ|x \* y|≤ .* \+ .*|abs|‖"),
]
AREA_RES = [(a, re.compile(p)) for a, p in AREAS]


def area_of(text: str) -> str:
    for area, rx in AREA_RES:
        if rx.search(text):
            return area
    return "Misc"


def problem_number(url: str) -> str | None:
    m = re.search(r"/problems/(\d+)", url)
    return m.group(1) if m else None


def body_of(rec: dict) -> str:
    """the record as source: its statement without the `import` line, then its proof"""
    st = re.sub(r"\A(?:import [^\n]*\n)+\s*", "", rec["statement"])
    proof = rec["proof"].strip()
    return st.rstrip() + ("\n" if proof.startswith("--") else " ") + proof


def starts_theorem(line: str) -> bool:
    """the line is a `theorem` or `lemma` command: attributes (`@[…]`) and modifiers first, then the keyword and a name (no regular expression: a nested repeat of
    attributes backtracks exponentially on a crafted line)"""
    rest = line.lstrip()
    while rest.startswith("@["):
        end = rest.find("]")
        if end < 0:
            return False
        rest = rest[end + 1 :].lstrip()
    words = rest.split()
    while words and words[0] in DECL_MODIFIERS:
        words = words[1:]
    return len(words) >= 2 and words[0] in ("theorem", "lemma")


def attributes_only(line: str) -> bool:
    """the line holds attributes and nothing else"""
    rest = line.strip()
    if not rest.startswith("@["):
        return False
    while rest.startswith("@["):
        end = rest.find("]")
        if end < 0:
            return False
        rest = rest[end + 1 :].lstrip()
    return rest == ""


def theorem_offset(body: str) -> int | None:
    """where the first theorem/lemma command starts, from the attribute lines above it (a docstring goes in front of those)"""
    lines = body.split("\n")
    starts, off = [], 0
    for ln in lines:
        starts.append(off)
        off += len(ln) + 1
    for k, ln in enumerate(lines):
        if starts_theorem(ln):
            while k > 0 and attributes_only(lines[k - 1]):
                k -= 1
            return starts[k]
    return None


def left_out(rec: dict, taken: set[str], exclude: set[str]) -> str | None:
    text = rec["statement"] + "\n" + rec["proof"]
    if rec["name"] in exclude:
        return "excluded"
    if UNSAFE.search(text):
        return "trusts the compiler or is unfinished"
    if theorem_offset(rec["statement"]) is None:
        return "no theorem or lemma of its own"
    if rec["name"] in taken:
        return "a name this source already has"
    return None


def place_docstring(body: str, doc: str) -> str:
    """the docstring in front of the first theorem/lemma (and its attributes); a body that has one already keeps it"""
    start = theorem_offset(body)
    assert start is not None
    before = body[:start]
    if re.search(r"/--[^/]*-/\s*\Z", before):
        return body
    return before + doc + "\n" + body[start:]


def render(rec: dict, source: str, label: str, used: dict[str, int]) -> str:
    n = problem_number(rec.get("source_url", "")) or re.sub(r"\W", "_", rec["name"])
    used[n] = used.get(n, 0) + 1
    ns = f"Native.{source}.P{n}" + (
        "" if used[n] == 1 else f"_{used[n]}"
    )  # two records of one problem (two proofs, or a helper and its theorem)
    body = place_docstring(body_of(rec), f"/-- {label} problem {n}. -/")
    return f"namespace {ns}\n\n{body}\n\nend {ns}\n"


def build(
    records: list[dict], source: str, label: str, exclude: set[str], per_module: int, authors: str
) -> tuple[dict[str, str], list[tuple[str, str]], dict[str, str]]:
    """(module files by relative path, [(record name, why it is left out)], record name -> module path)"""
    by_area: dict[str, list[dict]] = {}
    out: list[tuple[str, str]] = []
    taken: set[str] = set()
    for rec in records:
        why = left_out(rec, taken, exclude)
        if why:
            out.append((rec["name"], why))
            continue
        taken.add(rec["name"])
        by_area.setdefault(area_of(rec["statement"]), []).append(rec)
    files: dict[str, str] = {}
    where: dict[str, str] = {}
    used: dict[str, int] = {}
    for area, recs in sorted(by_area.items()):
        chunks = [recs[i : i + per_module] for i in range(0, len(recs), per_module)]
        for k, chunk in enumerate(chunks, 1):
            stem = area if len(chunks) == 1 else f"{area}{k}"
            path = f"Tengoku/Native/{source}/{stem}.lean"
            files[path] = HEADER.format(authors=authors) + "\n".join(render(r, source, label, used) for r in chunk)
            for r in chunk:
                where[r["name"]] = path
    files["Tengoku/Native.lean"] = "".join(
        f"import {p[: -len('.lean')].replace('/', '.')}\n" for p in sorted(files)
    )  # the umbrella imports every module once
    return files, out, where


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("records")
    ap.add_argument("--out", required=True)
    ap.add_argument("--source", default="Competemath", help="the folder and namespace: Tengoku/Native/<Source>/")
    ap.add_argument("--label", default="competemath.com")
    ap.add_argument("--authors", default="CompeteMath")
    ap.add_argument("--exclude", nargs="*", default=[])
    ap.add_argument("--max-per-module", type=int, default=40)
    a = ap.parse_args(argv)
    records = [json.loads(ln) for ln in Path(a.records).read_text(encoding="utf-8").splitlines() if ln.strip()]
    files, out, where = build(records, a.source, a.label, set(a.exclude), a.max_per_module, a.authors)
    root = Path(a.out)
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    (root / "native-import.json").write_text(json.dumps({"left_out": out, "where": where}, indent=1, ensure_ascii=False), encoding="utf-8")
    reasons: dict[str, int] = {}
    for _, why in out:
        reasons[why] = reasons.get(why, 0) + 1
    print(f"{len(where)} records in {len(files) - 1} modules (and the umbrella Tengoku/Native.lean); left out: {reasons}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
