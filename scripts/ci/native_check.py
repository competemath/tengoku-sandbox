#!/usr/bin/env python3
"""native_check.py <base> <head> — the checks of a NATIVE PR (docs/native.md, docs/pr-classes.md section 8).

Native is novel content: Lean modules under `Tengoku/Native/`, written by hand or proved by Leak (CompeteMath's own certified theorems, scripts/native_import.py), as
opposed to the seed and to translations of other people's libraries. A native PR adds or edits those modules and nothing else, and comes from `TENGOKU_BOT`.
It runs no Lean and nothing of the PR; it reads git objects:

  shape       only `Tengoku/Native/**.lean` (added or modified, never deleted: a module is not retracted by deleting it), the umbrella `Tengoku/Native.lean`, and
              `Tengoku/All.lean` when the umbrella is new (it gains exactly `import Tengoku.Native`); at most 400 modules a PR
  umbrella    imports every module under Tengoku/Native/ exactly once and nothing else
  modules     UTF-8; a credit (`Authors: …` in the header comment); imports only `Tengoku` and `Tengoku.Native.*` (what Native builds on is the seed; the seed and the
              translated libraries never import Native); the content allow-list of the intake class in strict mode (scripts/ci/allowlist.py: known-inert commands, no code that
              runs while compiling, no `native_decide` or any other way to trust the compiler); no `sorry`; no isnad tag (tags are written by the sweep, which recomputes them)
The merge queue builds the PR's modules, checks the axioms of every theorem (three standard axioms and nothing else) and writes the leak report.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import isnad_tag as tg  # noqa: E402
from _git import ROOT, blob, changed_files, fail, run  # noqa: E402
from allowlist import violations  # noqa: E402

MAX_NATIVE_MODULES = 400
ALL = "Tengoku/All.lean"
UMBRELLA = "Tengoku/Native.lean"
NATIVE_FILE = re.compile(r"Tengoku/Native/.+\.lean")
IMPORT_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$")
MODULE_LINE = re.compile(r"^\s*(?:module|prelude)\s*$")
IMPORT_OK = re.compile(r"Tengoku(?:\.Native\..+)?")
AUTHORS = re.compile(r"^[ \t]*Authors?:[ \t]*\S", re.M)
SORRY = re.compile(r"(?<![\w'!?])sorry(?![\w'!?])")


def is_native(base: str, head: str) -> bool:
    """The diff has the shape of a native PR: every path is a Native module, the umbrella or All.lean, and at least one is a Native module. (What is wrong with it is
    for `main` below to say, so that the PR gets a message about Native and not about some other class.)"""
    paths = [p for _, p in changed_files(base, head)]
    return (
        bool(paths)
        and any(NATIVE_FILE.fullmatch(p) for p in paths)
        and all(NATIVE_FILE.fullmatch(p) or p in (UMBRELLA, ALL) for p in paths)
    )


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def text_at(rev: str, path: str) -> str | None:
    raw = blob(rev, path)
    try:
        return None if raw is None else raw.decode("utf-8")
    except UnicodeDecodeError:
        return None


def import_errors(path: str, text: str) -> tuple[list[str], str]:
    """the imports the module may not have, and the module with its import and `module` lines blanked (what the lint reads)"""
    errors, body = [], []
    for ln in text.split("\n"):
        m = IMPORT_LINE.match(ln.split("--", 1)[0])
        if m and not IMPORT_OK.fullmatch(m.group(1)):
            errors.append(f"{path}: imports {m.group(1)}: Native builds on `Tengoku` and on other Native modules only")
        body.append("" if m or MODULE_LINE.match(ln) else ln)
    return errors, "\n".join(body)


def content_errors(path: str, body: str, allowed: set[str], keywords: set[str]) -> list[str]:
    errors = [f"{path}: {v}" for v in violations(body, allowed, keywords)[:3]]
    code = "".join(text if kind == "code" else re.sub(r"[^\n]", " ", text) for kind, text in ((k, body[a:b]) for k, a, b in tg.scan(body)))
    if SORRY.search(code):
        errors.append(f"{path}: `sorry`: a Native module holds finished proofs only")
    for kind, a, b in tg.scan(body):
        if kind == "doc" and any(tg.TAG_LINE.match(ln) for ln in body[a + 3 : b - 2].split("\n")):
            errors.append(f"{path}: an isnad tag: tags are written by the sweep (isnad-tag), which recomputes them")
            break
    return errors


def module_errors(path: str, text: str, allowed: set[str], keywords: set[str]) -> list[str]:
    errors = []
    head = text.split("import ", 1)[0]
    if not AUTHORS.search(head):
        errors.append(f"{path}: no credit: the header comment names its author (`Authors: …`)")
    more, body = import_errors(path, text)
    return errors + more + content_errors(path, body, allowed, keywords)


def umbrella_errors(text: str | None, modules: set[str]) -> list[str]:
    if text is None:
        return [f"{UMBRELLA} is missing or not UTF-8: it imports every module under Tengoku/Native/"]
    lines = [ln for ln in text.split("\n") if ln.strip() and not ln.lstrip().startswith("--")]
    found = [m.group(1) for ln in lines if (m := IMPORT_LINE.match(ln))]
    errors = []
    if len(found) != len(lines):
        errors.append(f"{UMBRELLA} holds only import lines (and comments)")
    if sorted(found) != sorted(modules):
        missing, extra = sorted(modules - set(found)), sorted(set(found) - modules)
        errors.append(
            f"{UMBRELLA} must import every Native module exactly once (missing {missing[:3]}, not modules {extra[:3]}, {len(found) - len(set(found))} twice)"
        )
    return errors


def all_errors(base: str, head: str, files: list[tuple[str, str]]) -> list[str]:
    """Tengoku/All.lean: untouched, except that the first Native PR adds exactly `import Tengoku.Native`"""
    touched = ALL in [p for _, p in files]
    new_umbrella = blob(base, UMBRELLA) is None
    diff = [ln for ln in run("diff", "-U0", f"{base}...{head}", "--", ALL).splitlines() if ln[:1] in "+-" and ln[:3] not in ("+++", "---")]
    if new_umbrella and diff not in (["+import Tengoku.Native"], ["+public import Tengoku.Native"]):
        return [f"{ALL} must gain exactly `import Tengoku.Native` with the umbrella (diff: {diff[:3]})"]
    if not new_umbrella and touched:
        return [f"{ALL} is untouched once Tengoku/Native.lean is in the tree"]
    return []


def shape_errors(files: list[tuple[str, str]]) -> list[str]:
    errors = []
    if not files:
        errors.append("an empty diff")
    modules = [p for _, p in files if NATIVE_FILE.fullmatch(p)]
    if len(modules) > MAX_NATIVE_MODULES:
        errors.append(f"{len(modules)} modules: a native PR has at most {MAX_NATIVE_MODULES}")
    for st, p in files:
        if not (NATIVE_FILE.fullmatch(p) or p in (UMBRELLA, ALL)):
            errors.append(f"{p}: not a Native path (Tengoku/Native/**.lean, {UMBRELLA}, {ALL})")
        elif st not in ("A", "M"):
            errors.append(f"{p}: a native PR adds and modifies, status {st}")
    return errors


def main(argv: list[str]) -> None:
    base, head = argv[1], argv[2]
    files = changed_files(base, head)
    errors = shape_errors(files) + all_errors(base, head, files)
    allowed = set(json.loads((ROOT / "schemas" / "allowed-options.json").read_text())["allowed"])
    keywords = set(json.loads((ROOT / "schemas" / "command-keywords.json").read_text())["commands"])
    for st, p in files:
        if st in ("A", "M") and NATIVE_FILE.fullmatch(p):
            text = text_at(head, p)
            errors += [f"{p}: not readable as UTF-8"] if text is None else module_errors(p, text, allowed, keywords)
    at_head = {module_of(p) for p in run("ls-tree", "-r", "--name-only", head, "Tengoku/Native").split("\n") if NATIVE_FILE.fullmatch(p)}
    if at_head or UMBRELLA in [p for _, p in files]:
        errors += umbrella_errors(text_at(head, UMBRELLA), at_head)
    if errors:
        fail("native PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    print(f"native ok: {sum(1 for _, p in files if NATIVE_FILE.fullmatch(p))} modules")


if __name__ == "__main__":
    main(sys.argv)
