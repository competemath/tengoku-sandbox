#!/usr/bin/env python3
"""scope_fix_check.py <base> <head> — the checks of a SCOPE-FIX PR.

A merged library cannot be edited (its modules are derived files), yet a library can register, for the whole tree, an instance or a simp lemma
that mentions nothing of its own types (`attribute [instance] Matrix.linftyOpNormedAddCommGroup`: the norm of every matrix in the tree becomes the
L-infinity operator norm; the merge queue's leak report lists them). A scope-fix PR makes such a registration `local` to the module that makes
it and gives the library's own importers the same registrations, local to each: inside the library nothing changes, outside it nothing leaks.

Only that one transformation is accepted, and it is checked line by line, not trusted:
  - every changed file is an existing module `Tengoku/<Library>/….lean` of a library that arrived as an intake bundle (data/intake/<library>/ at
    the base), modified in place; nothing else is touched (no manifest, no All.lean, no other path);
  - a line may change in exactly one way: the word `local ` inserted, in code, before `instance` or `simp` (`local instance`, `@[local simp]`,
    `attribute [local instance]`); the same number of lines before and after, in the same order;
  - lines may be added in exactly one form: `attribute [local instance] N …`, `attribute [local instance P] N …` (a priority), `attribute [local simp] N …`,
    blank lines, and the one note comment `-- Tengoku: … (generated)`; each N is a name the library itself registers (an instance it declares or
    names in an `attribute [instance]`, a simp lemma it declares or names in `attribute [simp]`) or an automatically named instance (`inst…`).
Nothing is declared, removed, reordered or renamed, so no theorem, statement, import or axiom changes; the merge queue builds the library.
"""

from __future__ import annotations

import difflib
import re
import sys

from _git import blob, changed_files, fail, pascal, run

NAME = r"[\w.'«»!?]+"
ATTR_LINE = re.compile(rf"attribute \[local (?:instance(?: \d+)?|simp)\]( {NAME})+")
NOTE = re.compile(r"-- Tengoku: \d+ registration\(s\) of this module made local so they do not change other libraries \(generated\)")
KEYWORD = re.compile(r"(?:instance|simp)(?![\w'.])")
INSTANCE_DECL = re.compile(rf"(?<![\w.])instance\s+(?:\(priority\s*:=[^)]*\)\s*)?({NAME})")
SIMP_DECL = re.compile(
    rf"@\[[^\]]*(?<![\w.])simp\b[^\]]*\]\s*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev)\s+({NAME})"
)
ATTRIBUTE_CMD = re.compile(rf"attribute\s*\[([^\]]*)\]((?:[ \t\n]+{NAME})+)")
IN_CODE = re.compile(r"--[^\n]*|/-|\"(?:\\.|[^\"\\])*\"")  # a line comment, the start of a block comment, a string literal


def _block_end(text: str, i: int) -> int:
    """the index just past the `-/` that closes the (nested) block comment opened at i; the end of the text if it never closes"""
    depth, j = 1, i + 2
    while j < len(text) and depth:
        if text.startswith("/-", j):
            depth, j = depth + 1, j + 2
        elif text.startswith("-/", j):
            depth, j = depth - 1, j + 2
        else:
            j += 1
    return j


def mask(text: str) -> str:
    """the text with comments and string literals blanked to spaces: same length, same columns (a word found in it is code)"""
    out, i = list(text), 0
    while m := IN_CODE.search(text, i):
        j = _block_end(text, m.start()) if m.group() == "/-" else m.end()
        for k in range(m.start(), j):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


def local_insertion(old: str, new: str) -> bool:
    """new is old with `local ` inserted once, in code, before `instance` or `simp`"""
    k = next((i for i, (a, b) in enumerate(zip(old, new)) if a != b), min(len(old), len(new)))
    if not (new[k : k + 6] == "local " and new[k + 6 :] == old[k:]):
        return False
    return mask(new)[k : k + 6] == "local " and bool(KEYWORD.match(new, k + 6))


def last(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def registered(ns: str) -> set[str]:
    """last components of the names the library registers for the whole tree, read (approximately) from its modules at the base"""
    out: set[str] = set()
    for p in run("ls-tree", "-r", "--name-only", base, f"Tengoku/{ns}").split("\n"):
        b = blob(base, p) if p.endswith(".lean") else None
        if b is not None:
            out |= registrations(mask(b.decode("utf-8", "replace")))
    return out


def registrations(text: str) -> set[str]:
    """the (last components of the) names an instance or simp registration of this masked module text mentions"""
    out = {last(m.group(1)) for m in INSTANCE_DECL.finditer(text)} | {last(m.group(1)) for m in SIMP_DECL.finditer(text)}
    for m in ATTRIBUTE_CMD.finditer(text):
        if re.search(r"(?<![\w.])(?:instance|simp)\b", m.group(1)):
            out |= {last(n) for n in m.group(2).split()}
    return out


def added_line_errors(path: str, lineno: int, line: str, known: set[str]) -> list[str]:
    if not line or NOTE.fullmatch(line):
        return []
    if not ATTR_LINE.fullmatch(line):
        return [
            f"{path}:{lineno}: an added line must be `attribute [local instance|simp] names`, a blank line or the note, not `{line[:80]}`"
        ]
    return [
        f"{path}:{lineno}: `{name}` is not a name this library registers (the line may only repeat the library's own registrations)"
        for name in line.split("]", 1)[1].split()
        if last(name) not in known and not re.match(r"inst[A-Z_]", last(name))
    ]


def opcode_errors(path: str, o: list[str], n: list[str], op: tuple, known: set[str]) -> list[str]:
    """the problems with one edit of a file (an `equal` stretch has none)"""
    tag, i1, i2, j1, j2 = op
    if tag == "equal":
        return []
    if tag == "insert":
        return [e for k in range(j1, j2) for e in added_line_errors(path, k + 1, n[k], known)]
    if tag == "replace" and i2 - i1 == j2 - j1:
        return [
            f"{path}:{b + 1}: a changed line may only gain `local ` before `instance`/`simp`: `{o[a][:60]}` -> `{n[b][:60]}`"
            for a, b in zip(range(i1, i2), range(j1, j2))
            if not local_insertion(o[a], n[b])
        ]
    return [f"{path}:{j1 + 1}: lines were removed or replaced by a different number of lines ({tag}: {i2 - i1} -> {j2 - j1})"]


def check_file(path: str, old: str, new: str, known: set[str]) -> list[str]:
    o, n = old.split("\n"), new.split("\n")
    ops = difflib.SequenceMatcher(None, o, n, autojunk=False).get_opcodes()
    return [e for op in ops for e in opcode_errors(path, o, n, op, known)]


def intake_namespaces() -> set[str]:
    """the libraries that arrived as intake bundles (data/intake/<library>/manifest.jsonl at the base), as module namespaces"""
    return {
        pascal(m.group(1))
        for p in run("ls-tree", "-r", "--name-only", base, "data/intake").split()
        if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))
    }


def file_errors(st: str, p: str, intake: set[str], known_by_ns: dict[str, set[str]]) -> list[str]:
    m = re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", p)
    if st != "M" or not m or m.group(1) not in intake:
        return [f"{p}: a scope-fix PR only modifies existing modules of libraries that arrived as intake bundles (status {st})"]
    ob, nb = blob(base, p), blob(head, p)
    if ob is None or nb is None:
        return [f"{p}: not readable at {base if ob is None else head}"]
    try:
        known = known_by_ns.setdefault(m.group(1), registered(m.group(1)))
        return check_file(p, ob.decode("utf-8"), nb.decode("utf-8"), known)
    except UnicodeDecodeError:
        return [f"{p}: not valid UTF-8"]


def main() -> None:
    files = changed_files(base, head)
    intake, known_by_ns = intake_namespaces(), {}
    errors = [e for st, p in files for e in file_errors(st, p, intake, known_by_ns)]
    if not files:
        errors.append("an empty diff")
    if errors:
        fail("scope-fix PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    libraries = {re.match(r"Tengoku/([^/]+)/", p).group(1) for _, p in files}
    print(f"scope-fix ok: {len(files)} modules of {len(libraries)} libraries, only `local` registrations")


base, head = sys.argv[1], sys.argv[2]
main()
