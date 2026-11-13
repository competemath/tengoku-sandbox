#!/usr/bin/env python3
"""imports_resolve.py <base> <head> — every `import Tengoku…` of the tree names a module that exists once the change is merged.

No Lean runs: a module is a file (`Tengoku/A/B.lean` is `Tengoku.A.B`, `Tengoku.lean` is `Tengoku`) and an import is a line of a file's header (comments,
doc-comment examples and anything after the first command are not). A change that adds or edits Lean files has its own imports checked; a change that deletes or
moves a module has every Lean file of the tree checked, since an importer it never touched may name the one that is gone.

Why it is a gate: a pull request that was green when it was opened can be broken by what merged after it (the seed moved into Tengoku/Seed/ and five open intake
PRs kept importing Tengoku.Std, which no longer existed: green at the PR, red only in the merge queue's multi-hour build). This finds it from the files alone,
in seconds, on the PR and again on the merged result in the queue.

    imports_resolve.py <base> <head>
"""

from __future__ import annotations

import re
import subprocess
import sys

from _git import ROOT, changed_files, fail, module_name, module_stem, run

IMPORT = re.compile(r"(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?(?P<mod>[^\s]+)")
KEYWORD = re.compile(r"(?:module|prelude)\b")
LIMIT = 20  # errors listed
ROOT_MODULE, ROOT_FILE = "Tengoku", "Tengoku.lean"


def module_of(path: str) -> str | None:
    """`Tengoku/A/B.lean` is Tengoku.A.B; `Tengoku.lean` is Tengoku; any other path is not a module of the tree."""
    if path == ROOT_FILE:
        return ROOT_MODULE
    if path.startswith("Tengoku/") and path.endswith(".lean"):
        return module_name(path[: -len(".lean")])
    return None


def strip_comments(text: str) -> str:
    """The text with every comment replaced by a space (newlines kept): `-- …` to the end of the line, and `/- … -/` (nested, over any number of lines). Lean
    reads a closed comment as whitespace, so `/- note -/ import X` is an import."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if depth:
            i, depth, kept = _inside_block(text, i, depth)
            out.append(kept)
        elif two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            end = text.find("\n", i)
            i = n if end < 0 else end  # the newline itself is read next
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _inside_block(text: str, i: int, depth: int) -> tuple[int, int, str]:
    """One step inside a `/- … -/` at nesting `depth`: (the next index, the new depth, what it leaves in the output: a space when the outermost comment closes,
    a newline where the comment has one, nothing otherwise)."""
    two = text[i : i + 2]
    if two == "/-":
        return i + 2, depth + 1, ""
    if two == "-/":
        return i + 2, depth - 1, " " if depth == 1 else ""
    return i + 1, depth, "\n" if text[i] == "\n" else ""


def header_imports(text: str) -> list[str]:
    """The modules a file imports: the `import` lines of its header, after any comments and a `module`/`prelude` keyword, up to the first command."""
    out: list[str] = []
    for raw in strip_comments(text).split("\n"):
        line = raw.strip()
        if not line or KEYWORD.fullmatch(line):
            continue
        m = IMPORT.match(line)
        if not m:
            break  # the first command ends the header
        out.append(m.group("mod"))
    return out


def modules_at(rev: str) -> set[str]:
    names = run("ls-tree", "-r", "--name-only", rev, "--", ROOT_MODULE, ROOT_FILE).splitlines()
    return {m for p in names if (m := module_of(p))}


def read_blobs(rev: str, paths: list[str]) -> dict[str, str]:
    """The text of each path at rev, in one `git cat-file --batch` (a tree has ten thousand files; a process each would take minutes)."""
    if not paths:
        return {}
    proc = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert proc.stdin and proc.stdout
    out: dict[str, str] = {}
    for p in paths:
        proc.stdin.write(f"{rev}:{p}\n".encode())
        proc.stdin.flush()
        head = proc.stdout.readline().split()
        if len(head) != 3:  # `<rev>:<path> missing`
            continue
        data = proc.stdout.read(int(head[2]))
        proc.stdout.read(1)  # the newline after the content
        out[p] = data.decode("utf-8", "replace")
    proc.stdin.close()
    proc.wait()
    return out


def what_to_check(changes: list[tuple[str, str]], modules: set[str]) -> tuple[list[str], str]:
    """(the files whose imports are read, and what that covers in words): every module of the tree when the change removes or moves one, else the files it adds or edits."""
    if any(st == "D" for st, _ in changes):
        targets = sorted(f"{module_stem(m)}.lean" if m != ROOT_MODULE else ROOT_FILE for m in modules)
        return targets, f"every module of the tree ({len(targets)}): the change removes or moves one"
    targets = sorted(p for st, p in changes if st != "D")
    return targets, f"the {len(targets)} module(s) the change adds or edits"


def unresolved(path: str, text: str, modules: set[str]) -> list[str]:
    """The imports of one file that name a module the tree does not have, each as an error line."""
    errors: list[str] = []
    for mod in header_imports(text):
        if mod.split(".")[0] != ROOT_MODULE or mod in modules:
            continue  # Lean, Init, Std: the toolchain's; the intake and lint gates decide what else may be imported
        hint = ""
        seed = "Tengoku.Seed." + mod.removeprefix("Tengoku.")
        if mod != ROOT_MODULE and seed in modules:
            hint = f" (the seed moved into Tengoku/Seed/: did you mean {seed}, or just `import Tengoku`?)"
        errors.append(f"{path}: imports {mod}, which is not a module of the tree after this change{hint}")
    return errors


def main() -> None:
    base, head = sys.argv[1], sys.argv[2]
    changes = [(st, p) for st, p in changed_files(base, head) if module_of(p)]
    if not changes:
        print("imports: no Lean module changed")
        return
    modules = modules_at(head)
    targets, scope = what_to_check(changes, modules)
    errors = [e for path, text in read_blobs(head, targets).items() for e in unresolved(path, text, modules)]
    if errors:
        shown = errors[:LIMIT] + ([f"… and {len(errors) - LIMIT} more"] if len(errors) > LIMIT else [])
        fail("an import names a module that does not exist:\n  " + "\n  ".join(shown))
    print(f"imports OK: {scope}")


if __name__ == "__main__":
    main()
