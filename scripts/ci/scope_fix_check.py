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

base, head = sys.argv[1], sys.argv[2]
NAME = r"[\w.'«»!?]+"
ATTR_LINE = re.compile(rf"attribute \[local (?:instance(?: \d+)?|simp)\]( {NAME})+")
NOTE = re.compile(r"-- Tengoku: \d+ registration\(s\) of this module made local so they do not change other libraries \(generated\)")
KEYWORD = re.compile(r"(?:instance|simp)(?![\w'.])")


def mask(text: str) -> str:
    """the text with comments and string literals blanked to spaces: same length, same columns (a word found in it is code)"""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        else:
            out.append(text[i])
            i += 1
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
        if b is None:
            continue
        text = mask(b.decode("utf-8", "replace"))
        out |= {last(m.group(1)) for m in re.finditer(rf"(?<![\w.])instance\s+(?:\(priority\s*:=[^)]*\)\s*)?({NAME})", text)}
        out |= {
            last(m.group(1))
            for m in re.finditer(
                rf"@\[[^\]]*(?<![\w.])simp\b[^\]]*\]\s*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev)\s+({NAME})", text
            )
        }
        for m in re.finditer(rf"attribute\s*\[([^\]]*)\]((?:[ \t\n]+{NAME})+)", text):
            if re.search(r"(?<![\w.])(?:instance|simp)\b", m.group(1)):
                out |= {last(n) for n in m.group(2).split()}
    return out


def check_file(path: str, old: str, new: str, known: set[str]) -> list[str]:
    errors = []
    o, n = old.split("\n"), new.split("\n")
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, o, n, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        if tag == "insert":
            for k in range(j1, j2):
                if n[k] and not ATTR_LINE.fullmatch(n[k]) and not NOTE.fullmatch(n[k]):
                    errors.append(f"{path}:{k + 1}: an added line must be `attribute [local instance|simp] names`, a blank line or the note, not `{n[k][:80]}`")
                elif ATTR_LINE.fullmatch(n[k]):
                    for name in n[k].split("]", 1)[1].split():
                        if last(name) not in known and not re.match(r"inst[A-Z_]", last(name)):
                            errors.append(f"{path}:{k + 1}: `{name}` is not a name this library registers (the line may only repeat the library's own registrations)")
        elif tag == "replace" and i2 - i1 == j2 - j1:
            for a, b in zip(range(i1, i2), range(j1, j2)):
                if not local_insertion(o[a], n[b]):
                    errors.append(f"{path}:{b + 1}: a changed line may only gain `local ` before `instance`/`simp`: `{o[a][:60]}` -> `{n[b][:60]}`")
        else:
            errors.append(f"{path}:{j1 + 1}: lines were removed or replaced by a different number of lines ({tag}: {i2 - i1} -> {j2 - j1})")
    return errors


files = changed_files(base, head)
intake = {
    pascal(m.group(1))
    for p in run("ls-tree", "-r", "--name-only", base, "data/intake").split()
    if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))
}
errors: list[str] = []
known_by_ns: dict[str, set[str]] = {}
for st, p in files:
    m = re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", p)
    if st != "M" or not m or m.group(1) not in intake:
        errors.append(f"{p}: a scope-fix PR only modifies existing modules of libraries that arrived as intake bundles (status {st})")
        continue
    ob, nb = blob(base, p), blob(head, p)
    if ob is None or nb is None:
        errors.append(f"{p}: not readable at {base if ob is None else head}")
        continue
    try:
        known = known_by_ns.setdefault(m.group(1), registered(m.group(1)))
        errors += check_file(p, ob.decode("utf-8"), nb.decode("utf-8"), known)
    except UnicodeDecodeError:
        errors.append(f"{p}: not valid UTF-8")
if not files:
    errors.append("an empty diff")
if errors:
    fail("scope-fix PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
print(f"scope-fix ok: {len(files)} modules of {len({re.match(r'Tengoku/([^/]+)/', p).group(1) for _, p in files})} libraries, only `local` registrations")
