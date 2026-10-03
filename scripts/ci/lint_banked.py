#!/usr/bin/env python3
"""lint_banked.py <base> <head> | --text FILE — banked Lean must not run code.
Records paste `context` and `proof` verbatim into modules; modules are compiled
by CI and imported by every Leak service, where `initialize` runs. A staging or
trusted record (the tiers the tree compiles) must pass the allow-list
(scripts/ci/allowlist.py): only known-inert commands, attributes and options.
Tentative records (never compiled) and module lines keep the list of known
dangers below. Existing records are not re-judged: only lines a PR adds."""

from __future__ import annotations

import json
import os
import re
import sys

from _git import added_lines, changed_files, fail, load_schema, match, pascal
from allowlist import violations

NOTATION = "syntax/macro/elab/notation declarations"
FORBIDDEN = [
    (re.compile(r"^\s*import\b", re.M), "import (the generator supplies imports)"),
    (re.compile(r"#eval\b"), "#eval"),
    (re.compile(r"#print\s+axioms"), "#print axioms (CI runs its own)"),
    (re.compile(r"\brun_cmd\b"), "run_cmd"),
    (re.compile(r"\brun_tac\b"), "run_tac"),
    (re.compile(r"\brun_elab\b"), "run_elab"),
    (re.compile(r"^\s*(builtin_)?initialize\b", re.M), "initialize (runs on import in every Leak service)"),
    (
        re.compile(r"@\[\s*(init|builtin_init|extern|implemented_by|export|never_extract)\b"),
        "@[init]/@[extern]/@[implemented_by]/@[export]",
    ),
    (re.compile(r"^\s*(unsafe|partial)\s+(def|theorem|abbrev|instance|opaque)", re.M), "unsafe/partial definitions"),
    (
        re.compile(
            r"^\s*(@\[[^\]]*\]\s*)*(scoped\s+|local\s+)?(macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|notation3?|infixl?|infixr|prefix|postfix)\b",
            re.M,
        ),
        NOTATION,
    ),
    (re.compile(r"\bnative_decide\b"), "native_decide (trusts the compiler)"),
    (re.compile(r"^\s*opaque\b", re.M), "opaque"),
    (re.compile(r"^\s*axiom\b", re.M), "axiom"),
    (re.compile(r"\bIO\.(Process|FS)\b|\bSystem\.(FilePath|Platform)\b"), "IO.Process / IO.FS"),
]
SET_OPTION = re.compile(r"set_option\s+([A-Za-z_][\w.]*)")


def intake_modules(base: str, head: str) -> tuple[str, ...]:
    """The module paths of an intake bundle in this diff, when the repository's intake lint is `proposed` (variable TENGOKU_INTAKE_LINT):
    notation commands are allowed there, as in scripts/ci/intake_check.py (the allow-list lint of the bundle). Nowhere else."""
    if os.environ.get("TENGOKU_INTAKE_LINT") != "proposed":
        return ()
    libs = {m.group(1) for _, p in changed_files(base, head) if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}
    return tuple(x for lib in libs for x in (f"Tengoku/{pascal(lib)}/", f"Tengoku/{pascal(lib)}.lean"))


def check_text(label: str, text: str, allowed: set[str], notation_ok: bool = False) -> list[str]:
    out = []
    for re_, why in FORBIDDEN:
        if why == NOTATION and notation_ok:
            continue
        if re_.search(text):
            out.append(f"{label}: {why}")
    for opt in SET_OPTION.findall(text):
        if opt not in allowed:
            out.append(f"{label}: set_option {opt} is not on the allowlist")
    return out


def main() -> None:
    allowed = set(load_schema("allowed-options.json")["allowed"])
    errors = []
    if sys.argv[1] == "--text":
        errors = check_text(sys.argv[2], open(sys.argv[2]).read(), allowed)
    else:
        base, head = sys.argv[1], sys.argv[2]
        intake = intake_modules(base, head)
        for st, p in changed_files(base, head):
            if match(
                p,
                [
                    "data/tentative/*.jsonl",
                    "data/staging/*.jsonl",
                    "data/trusted/*.jsonl",
                    "data/tentative/*/*.jsonl",
                    "data/staging/*/*.jsonl",
                ],
            ):
                for no, text in added_lines(base, head, p):
                    try:
                        r = json.loads(text)
                    except Exception:
                        continue
                    if not isinstance(r, dict) or "tombstone" in r:  # not an object: validate_records.py refuses it
                        continue
                    body = "\n".join(str(r.get(k, "")) for k in ("context", "statement", "proof"))
                    label = f"{p}:{no} ({r.get('name')})"
                    if p.startswith(("data/staging/", "data/trusted/")):  # compiled: only what is known to be inert
                        errors += [f"{label}: {v}" for v in violations(body, allowed)]
                    else:
                        errors += check_text(label, body, allowed)
            elif p.endswith(".lean") and p.startswith(
                "Tengoku/"
            ):  # modules only; root tool programs (TengokuExtract/TengokuAxioms) run in CI, not in the library
                # `import` lines in a module are the generator's own (a promotion regenerates them); records may not contain one.
                errors += check_text(
                    p,
                    "\n".join(t for _, t in added_lines(base, head, p) if not re.match(r"^\s*import\b", t)),
                    allowed,
                    notation_ok=p.startswith(intake) if intake else False,
                )
    if errors:
        fail("banked content lint:\n  " + "\n  ".join(errors[:20]))
    print("content lint OK")


main()
