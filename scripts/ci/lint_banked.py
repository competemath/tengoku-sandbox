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
import tempfile
from pathlib import Path

from _git import added_lines, blob, changed_files, fail, load_schema, match, pascal
from allowlist import violations
from lean_lex import code_only
from restructure_check import is_restructure

IMPORT_START = r"^\s*import\b"
NOTATION = "syntax/macro/elab/notation declarations"
SYNTAX_COMMANDS = [
    "macro",
    "macro_rules",
    "syntax",
    "elab",
    "elab_rules",
    "declare_syntax_cat",
    "notation3?",
    "infixl?",
    "infixr",
    "prefix",
    "postfix",
]
FORBIDDEN = [
    (re.compile(IMPORT_START, re.M), "import (the generator supplies imports)"),
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
        re.compile(r"^\s*(@\[[^\]]*\]\s*)*(scoped\s+|local\s+)?(" + "|".join(SYNTAX_COMMANDS) + r")\b", re.M),
        NOTATION,
    ),
    (re.compile(r"\bnative_decide\b"), "native_decide (trusts the compiler)"),
    (re.compile(r"^\s*opaque\b", re.M), "opaque"),
    (re.compile(r"^\s*axiom\b", re.M), "axiom"),
    (re.compile(r"\bIO\.(Process|FS)\b|\bSystem\.(FilePath|Platform)\b"), "IO.Process / IO.FS"),
]
SET_OPTION = re.compile(r"set_option\s+([A-Za-z_][\w.]*)")


def intake_modules(base: str, head: str) -> tuple[str, ...]:
    """The module paths of an intake bundle in this diff, when the repository's intake lint is `proposed` or `wide` (variable TENGOKU_INTAKE_LINT):
    notation commands are allowed there, as in scripts/ci/intake_check.py (the allow-list lint of the bundle). Nowhere else."""
    if os.environ.get("TENGOKU_INTAKE_LINT") not in ("proposed", "wide"):
        return ()
    libs = {m.group(1) for _, p in changed_files(base, head) if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}
    return tuple(x for lib in libs for x in (f"Tengoku/{pascal(lib)}/", f"Tengoku/{pascal(lib)}.lean"))


def in_intake(p: str, intake: tuple[str, ...]) -> bool:
    """Is `p` one of the bundle's own modules: its root file exactly, or a file under its directory (never a sibling that merely starts the same)."""
    return p in intake or any(x.endswith("/") and p.startswith(x) for x in intake)


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


RECORD_FILES = [
    "data/tentative/*.jsonl",
    "data/staging/*.jsonl",
    "data/trusted/*.jsonl",
    "data/tentative/*/*.jsonl",
    "data/staging/*/*.jsonl",
]


def lint_record_file(base: str, head: str, p: str, allowed: set[str]) -> list[str]:
    """The lines a PR adds to a records file, judged by the allow-list (compiled tiers) or the list of known dangers."""
    errors = []
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


def lint_module(base: str, head: str, p: str, allowed: set[str], notation_ok: bool, added: bool = False) -> list[str]:
    """The lines a PR adds to a module. `import` lines in a module are the generator's own (a promotion regenerates them); records may not contain one.
    A module the PR adds is read whole and without its comments and string literals (lean_lex.code_only): the words this list refuses are
    refused where they run, not where a docstring mentions them (`#print axioms` in a doc comment is prose). A module the PR changes is read
    by the lines it adds, comments included: a line alone cannot tell code from the middle of a comment."""
    raw = blob(head, p) if added else None
    if added and raw is None:  # fail closed: the line-by-line path below cannot see a block comment that an `import X -/` line closes
        return [f"{p}: could not read the module at {head}"]
    if raw is not None:
        # comments and strings first, THEN the import lines: a line `import X -/` inside a block comment closes it, and dropping it first would
        # turn the rest of the file into comment text (a `#eval` after it would go unread)
        code = code_only(raw.decode("utf-8", "replace"))
        return check_text(p, "\n".join(ln for ln in code.split("\n") if not re.match(IMPORT_START, ln)), allowed, notation_ok=notation_ok)
    text = "\n".join(t for _, t in added_lines(base, head, p) if not re.match(IMPORT_START, t))
    return check_text(p, text, allowed, notation_ok=notation_ok)


def checked_path(arg: str) -> Path:
    """A file given on the command line: it must lie in the working directory or the temporary directory."""
    p = Path(arg).resolve()
    if not any(p.is_relative_to(root.resolve()) for root in (Path.cwd(), Path(tempfile.gettempdir()))):
        fail(f"{arg} is outside the working directory and the temporary directory")
    return p


def main() -> None:
    allowed = set(load_schema("allowed-options.json")["allowed"])
    errors = []
    if sys.argv[1] == "--text":
        errors = check_text(sys.argv[2], checked_path(sys.argv[2]).read_text(), allowed)
    else:
        base, head = sys.argv[1], sys.argv[2]
        intake = intake_modules(base, head)
        moved_seed = is_restructure(
            base, head
        )  # the seed's move is recomputed by restructure_check.py; it is upstream code, never banked content
        for st, p in changed_files(base, head):
            if moved_seed and p.startswith("Tengoku/Seed/"):
                continue
            if match(p, RECORD_FILES):
                errors += lint_record_file(base, head, p, allowed)
            elif p.endswith(".lean") and p.startswith(
                "Tengoku/"
            ):  # modules only; root tool programs (TengokuExtract/TengokuAxioms) run in CI, not in the library
                errors += lint_module(base, head, p, allowed, notation_ok=in_intake(p, intake), added=st == "A")
    if errors:
        fail("banked content lint:\n  " + "\n  ".join(errors[:20]))
    print("content lint OK")


main()
