#!/usr/bin/env python3
"""Derive the search index's text, structure and graph features from the
extractor's output (docs/tengoku-search-plan.md, section 3, steps 2 and 4).

    scripts/derive.py <index dir>      # reads decls.jsonl + deps.jsonl, writes derived.jsonl + symbols.jsonl

Per declaration: name tokens, an English name gloss, a rule-based statement
gloss, topic labels, a type hash (alpha-renamed statement) and graph features
(PageRank, degrees). Plus one symbols.jsonl with document frequencies. No
dependencies beyond the standard library; numpy speeds PageRank up when present.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

# Mathlib's naming abbreviations, expanded so English queries meet English text.
ABBREV = {
    "comm": "commutative",
    "assoc": "associative",
    "distrib": "distributive",
    "deriv": "derivative",
    "iff": "if and only if",
    "le": "less than or equal",
    "lt": "less than",
    "ge": "greater than or equal",
    "gt": "greater than",
    "ne": "not equal",
    "eq": "equal",
    "succ": "successor",
    "pred": "predecessor",
    "add": "addition",
    "sub": "subtraction",
    "mul": "multiplication",
    "div": "division",
    "neg": "negation",
    "inv": "inverse",
    "pow": "power",
    "sq": "square",
    "sqrt": "square root",
    "nonneg": "nonnegative",
    "pos": "positive",
    "nonpos": "nonpositive",
    "inj": "injective",
    "surj": "surjective",
    "bij": "bijective",
    "mono": "monotone",
    "anti": "antitone",
    "cont": "continuous",
    "diff": "differentiable",
    "lim": "limit",
    "sup": "supremum",
    "inf": "infimum",
    "abs": "absolute value",
    "nat": "natural number",
    "int": "integer",
    "rat": "rational",
    "real": "real",
    "cpx": "complex",
    "fin": "finite",
    "card": "cardinality",
    "len": "length",
    "mem": "member",
    "compl": "complement",
    "dvd": "divides",
    "gcd": "greatest common divisor",
    "lcm": "least common multiple",
    "coprime": "coprime",
    "mod": "modulo",
    "emod": "modulo",
    "cancel": "cancellation",
    "self": "self",
    "zero": "zero",
    "one": "one",
    "two": "two",
    "left": "left",
    "right": "right",
    "of": "of",
    "to": "to",
    "mk": "make",
    "id": "identity",
    "fun": "function",
    "hom": "homomorphism",
    "iso": "isomorphism",
    "equiv": "equivalence",
    "prod": "product",
    "sum": "sum",
    "union": "union",
    "inter": "intersection",
    "subset": "subset",
    "empty": "empty",
    "univ": "universal set",
    "range": "range",
    "image": "image",
    "preimage": "preimage",
    "comp": "composition",
    "apply": "apply",
    "def": "definition",
    "coe": "coercion",
    "cast": "cast",
    "ofnat": "of natural number",
    "tendsto": "tends to",
    "nhds": "neighbourhood",
    "integral": "integral",
    "measurable": "measurable",
    "finset": "finite set",
    "list": "list",
    "multiset": "multiset",
}
# Constants that carry notation: their symbol and the words a person types.
NOTATION = {
    "HAdd.hAdd": ("+", "plus"),
    "HSub.hSub": ("-", "minus"),
    "HMul.hMul": ("*", "times"),
    "HDiv.hDiv": ("/", "divided by"),
    "HPow.hPow": ("^", "to the power"),
    "Neg.neg": ("-", "negative"),
    "Inv.inv": ("⁻¹", "inverse"),
    "Eq": ("=", "equals"),
    "Ne": ("≠", "not equal"),
    "LE.le": ("≤", "at most"),
    "LT.lt": ("<", "less than"),
    "GE.ge": ("≥", "at least"),
    "GT.gt": (">", "greater than"),
    "And": ("∧", "and"),
    "Or": ("∨", "or"),
    "Not": ("¬", "not"),
    "Iff": ("↔", "if and only if"),
    "Exists": ("∃", "there exists"),
    "Membership.mem": ("∈", "in"),
    "HasSubset.Subset": ("⊆", "subset of"),
    "Union.union": ("∪", "union"),
    "Inter.inter": ("∩", "intersection"),
    "Finset.sum": ("∑", "sum"),
    "Finset.prod": ("∏", "product"),
    "Function.comp": ("∘", "composed with"),
    "Dvd.dvd": ("∣", "divides"),
    "abs": ("|·|", "absolute value"),
    "Nat": ("ℕ", "natural numbers"),
    "Int": ("ℤ", "integers"),
    "Rat": ("ℚ", "rationals"),
    "Real": ("ℝ", "reals"),
    "Complex": ("ℂ", "complex numbers"),
    "Real.sqrt": ("√", "square root"),
    "Real.exp": ("exp", "exponential"),
    "Real.log": ("log", "logarithm"),
    "Real.pi": ("π", "pi"),
}
GLOSS_SYMBOLS = [(sym, words) for sym, words in NOTATION.values()] + [
    ("∀", "for all"),
    ("→", "implies"),
    ("↔", "if and only if"),
    ("¬", "not"),
    ("∧", "and"),
    ("∨", "or"),
    ("≠", "not equal"),
    ("≤", "at most"),
    ("≥", "at least"),
    ("∈", "in"),
    ("∉", "not in"),
    ("⊆", "subset of"),
    ("∪", "union"),
    ("∩", "intersection"),
    ("∑", "sum"),
    ("∏", "product"),
    ("∫", "integral"),
    ("∘", "composed with"),
    ("∣", "divides"),
    ("ℕ", "natural numbers"),
    ("ℤ", "integers"),
    ("ℚ", "rationals"),
    ("ℝ", "reals"),
    ("ℂ", "complex numbers"),
    ("√", "square root"),
    ("π", "pi"),
    ("∞", "infinity"),
    ("=", "equals"),
    ("<", "less than"),
    (">", "greater than"),
    ("+", "plus"),
    ("-", "minus"),
    ("*", "times"),
    ("/", "divided by"),
    ("^", "to the power"),
]
CAMEL = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?]*")


def tokens(name: str) -> list[str]:
    out = []
    for part in re.sub(r"[«»'!?]", "", name).replace("#", "_").split("."):
        for piece in part.split("_"):
            for tok in CAMEL.split(piece):
                tok = tok.strip().lower()
                if tok:
                    out.append(tok)
    return out


def gloss_tokens(toks: list[str]) -> str:
    return " ".join(ABBREV.get(t, t) for t in toks)


def name_gloss(name: str) -> str:
    return gloss_tokens(tokens(name))


def statement_gloss(stmt: str) -> str:
    s = stmt
    for sym, words in sorted(GLOSS_SYMBOLS, key=lambda x: -len(x[0])):
        s = s.replace(sym, f" {words} ")
    s = re.sub(r"[()\[\]{}⟨⟩,:]", " ", s)
    s = IDENT.sub(
        lambda m: gloss_tokens(tokens(m.group(0))) if not m.group(0).islower() or "_" in m.group(0) or "." in m.group(0) else m.group(0), s
    )
    return re.sub(r"\s+", " ", s).strip()


def topics(module: str) -> list[str]:
    parts = module.split(".")
    if parts and parts[0] == "Tengoku":
        parts = parts[1:]
    return [" ".join(t.lower() for t in CAMEL.split(p)) for p in parts if p and p != "Basic"]


def type_hash(stmt: str, binders: list[dict]) -> str:
    s = stmt
    for i, b in enumerate(binders):
        n = b.get("name", "")
        if n and not n.startswith("_"):
            s = re.sub(rf"(?<![A-Za-z0-9_.']){re.escape(n)}(?![A-Za-z0-9_'])", f"𝑥{i}", s)
    s = re.sub(r"\s+", " ", s).strip()
    return hashlib.sha1(s.encode()).hexdigest()[:16]


def pagerank(nodes: list[str], edges: dict[str, list[str]], damping=0.85, iters=30) -> dict[str, float]:
    idx = {n: i for i, n in enumerate(nodes)}
    N = len(nodes)
    if N == 0:
        return {}
    out = [[idx[t] for t in edges.get(n, []) if t in idx] for n in nodes]
    try:
        import numpy as np  # optional

        r = np.full(N, 1.0 / N)
        for _ in range(iters):
            nr = np.full(N, (1 - damping) / N)
            dangling = 0.0
            for i, targets in enumerate(out):
                if targets:
                    share = damping * r[i] / len(targets)
                    nr[targets] += share
                else:
                    dangling += r[i]
            nr += damping * dangling / N
            r = nr
        return {n: float(r[idx[n]]) for n in nodes}
    except ImportError:
        r = [1.0 / N] * N
        for _ in range(iters):
            nr = [(1 - damping) / N] * N
            dangling = 0.0
            for i, targets in enumerate(out):
                if targets:
                    share = damping * r[i] / len(targets)
                    for t in targets:
                        nr[t] += share
                else:
                    dangling += r[i]
            add = damping * dangling / N
            r = [v + add for v in nr]
        return {n: r[idx[n]] for n in nodes}


def derive(decls: list[dict], deps: dict[str, list[str]]) -> tuple[list[dict], list[dict], list[dict]]:
    names = [d["name"] for d in decls]
    present = set(names)
    in_degree = Counter()
    for src, targets in deps.items():
        for t in targets:
            if t in present and t != src:
                in_degree[t] += 1
    pr = pagerank(names, {n: [t for t in deps.get(n, []) if t in present] for n in names})
    df = Counter()
    for d in decls:
        for c in set(d.get("constants_type", [])):
            df[c] += 1
    derived = []
    for d in decls:
        toks = tokens(d["name"])
        derived.append(
            {
                "name": d["name"],
                "name_tokens": toks,
                "name_gloss": gloss_tokens(toks),
                "statement_gloss": statement_gloss(d.get("statement", "")),
                "topics": topics(d.get("module", "")),
                "type_hash": type_hash(d.get("statement", ""), d.get("binders", [])),
                "notation_used": sorted({NOTATION[c][0] for c in d.get("constants_type", []) if c in NOTATION}),
                "pagerank": pr.get(d["name"], 0.0),
                "in_degree": in_degree.get(d["name"], 0),
                "out_degree": len([t for t in deps.get(d["name"], []) if t in present]),
            }
        )
    symbols = [
        {"name": c, "df": n, "symbol": NOTATION.get(c, ("", ""))[0] or None, "gloss": NOTATION.get(c, ("", name_gloss(c)))[1]}
        for c, n in sorted(df.items(), key=lambda kv: -kv[1])
    ]
    # Name-token document frequencies: "comm" is rare and telling, "nat" is not.
    token_df = Counter()
    for r in derived:
        for tok in set(r["name_tokens"]):
            token_df[tok] += 1
    tokens_out = [{"token": tok, "df": n} for tok, n in sorted(token_df.items(), key=lambda kv: -kv[1])]
    return derived, symbols, tokens_out


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    d = Path(sys.argv[1])
    decls = [json.loads(l) for l in (d / "decls.jsonl").open() if l.strip()]
    deps = {}
    if (d / "deps.jsonl").exists():
        for l in (d / "deps.jsonl").open():
            if l.strip():
                o = json.loads(l)
                deps[o["from"]] = o["to"]
    derived, symbols, tokens_out = derive(decls, deps)
    with (d / "derived.jsonl").open("w") as f:
        for r in derived:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    with (d / "symbols.jsonl").open("w") as f:
        for r in symbols:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    with (d / "tokens.jsonl").open("w") as f:
        for r in tokens_out:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(f"derived {len(derived)} declarations, {len(symbols)} symbols, {len(tokens_out)} name tokens -> {d}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
