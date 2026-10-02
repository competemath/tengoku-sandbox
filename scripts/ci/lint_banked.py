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
import re
import sys

from _git import added_lines, changed_files, fail, load_schema, match
from allowlist import violations

# a line that starts (after its attributes and a scoped/local) a declaration of syntax: one message, two patterns
_DECLARATION_PREFIX = r"^\s*(@\[[^\]]*\]\s*)*(scoped\s+|local\s+)?"
_SYNTAX_DECLARATIONS = "syntax/macro/elab/notation declarations"
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
    (re.compile(_DECLARATION_PREFIX + r"(macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat)\b", re.M), _SYNTAX_DECLARATIONS),
    (re.compile(_DECLARATION_PREFIX + r"(notation3?|infixl?|infixr|prefix|postfix)\b", re.M), _SYNTAX_DECLARATIONS),
    (re.compile(r"\bnative_decide\b"), "native_decide (trusts the compiler)"),
    (re.compile(r"^\s*opaque\b", re.M), "opaque"),
    (re.compile(r"^\s*axiom\b", re.M), "axiom"),
    (re.compile(r"\bIO\.(Process|FS)\b|\bSystem\.(FilePath|Platform)\b"), "IO.Process / IO.FS"),
]
SET_OPTION = re.compile(r"set_option\s+([A-Za-z_][\w.]*)")


def check_text(label: str, text: str, allowed: set[str]) -> list[str]:
    out = [f"{label}: {why}" for re_, why in FORBIDDEN if re_.search(text)]
    out += [f"{label}: set_option {opt} is not on the allowlist" for opt in SET_OPTION.findall(text) if opt not in allowed]
    return list(dict.fromkeys(out))


RECORD_FILES = [
    "data/tentative/*.jsonl",
    "data/staging/*.jsonl",
    "data/trusted/*.jsonl",
    "data/tentative/*/*.jsonl",
    "data/staging/*/*.jsonl",
]


def record_errors(base: str, head: str, p: str, allowed: set[str]) -> list[str]:
    """The lines a PR adds to one records file, judged by the allow-list (compiled tiers) or the list of known dangers."""
    errors: list[str] = []
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
    return errors


def module_errors(base: str, head: str, p: str, allowed: set[str]) -> list[str]:
    """The lines a PR adds to a module: `import` lines are the generator's own (a promotion regenerates them); records may not contain one."""
    added = "\n".join(t for _, t in added_lines(base, head, p) if not re.match(r"^\s*import\b", t))
    return check_text(p, added, allowed)


def diff_errors(base: str, head: str, allowed: set[str]) -> list[str]:
    errors: list[str] = []
    for _, p in changed_files(base, head):
        if match(p, RECORD_FILES):
            errors += record_errors(base, head, p, allowed)
        elif p.endswith(".lean") and p.startswith(
            "Tengoku/"
        ):  # modules only; root tool programs (TengokuExtract/TengokuAxioms) run in CI, not in the library
            errors += module_errors(base, head, p, allowed)
    return errors


def main() -> None:
    allowed = set(load_schema("allowed-options.json")["allowed"])
    if sys.argv[1] == "--text":
        with open(sys.argv[2]) as f:
            errors = check_text(sys.argv[2], f.read(), allowed)
    else:
        errors = diff_errors(sys.argv[1], sys.argv[2], allowed)
    if errors:
        fail("banked content lint:\n  " + "\n  ".join(errors[:20]))
    print("content lint OK")


main()
