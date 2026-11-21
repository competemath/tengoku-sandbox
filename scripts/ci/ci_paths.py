"""ci_paths.py: which files of a pull request are CI, decided by the files, not by anyone's judgement.

A change is CI-class when it touches a workflow, a file under scripts/ci/, the CODEOWNERS file, a data file the gates read (schemas/, the toolchain, tools/*.lean), or any file a gate script depends on: a module or script that a workflow runs (or a gate script
under scripts/ci/ that it reaches) imports or calls, followed to the end. That last rule is the one that matters: scripts/roots_tree.py is no gate and lives outside scripts/ci/, but
scripts/ci/roots_check.py imports it to recompute what a roots PR must be, so a change to it changes a gate (tengoku#1026 went in without a campaign because it was judged "a library module").

Standard library only. Python imports are read with `ast` (an import inside a function counts: roots_check.py imports roots_tree there), shell and workflow text for `scripts/...` paths.
"""

from __future__ import annotations

import ast
import posixpath
import re

DIRECT_PREFIXES = ("scripts/ci/", ".github/workflows/", "schemas/")
# data the gates read to decide what they accept (allowed-options.json, command-keywords.json, the toolchain they check a bundle against): editing one changes a gate as surely as editing a script
DIRECT_FILES = {".github/CODEOWNERS", "lean-toolchain", "lakefile.toml", "lake-manifest.json"}
DIRECT_PATTERNS = (re.compile(r"^tools/[^/]+\.lean$"),)  # tools/CommandKeywords.lean: what cmdkw_check compares against
# the one data file under schemas/ that is NOT a gate input but the registry itself: it grows with every registry PR, and the append-only rule, the owners file and the registry class judge that
DIRECT_EXEMPT = {"schemas/sources.json"}
DOC_SUFFIXES = (".md",)  # a document under scripts/ci/ (the campaign README) is not a gate
SEARCH_DIRS = (
    "scripts/ci",
    "scripts",
)  # where a gate script finds `import name` (its own folder first, then the sys.path.insert of roots_check.py)
SCRIPT_REF = re.compile(r"(?<![\w/.-])(scripts/[\w./-]+\.(?:py|sh|mjs))")
ENTRY = re.compile(r"^scripts/ci/[^/]+\.(?:py|sh)$")  # every top-level gate script is an entry point, run from a workflow or by another one


def is_doc(path: str) -> bool:
    return path.endswith(DOC_SUFFIXES)


def python_imports(text: str) -> set[str]:
    """the top-level module names a Python file imports, wherever the statement stands (a function body too); a file that does not parse imports nothing"""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return set()
    found: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            found |= {a.name.split(".")[0] for a in node.names}
        elif isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
            found.add(node.module.split(".")[0])
    return found


def resolve(module: str, importer: str, known: set[str]) -> str | None:
    """the file a module name means for this importer: its own folder, then scripts/ci, then scripts"""
    for d in (posixpath.dirname(importer), *SEARCH_DIRS):
        cand = posixpath.join(d, module + ".py")
        if cand in known:
            return cand
    return None


def references(path: str, text: str, known: set[str]) -> set[str]:
    """the repository files this file depends on: the modules it imports, and the scripts it names (a workflow step, a shell script, a path string in Python)"""
    out: set[str] = set()
    if path.endswith(".py"):
        for m in python_imports(text):
            if (r := resolve(m, path, known)) is not None:
                out.add(r)
    for m in SCRIPT_REF.finditer(text):
        if m.group(1) in known:
            out.add(m.group(1))
    out.discard(path)
    return out


def gate_closure(files: dict[str, str]) -> dict[str, str]:
    """{file: why} for every file a gate depends on. `files` maps a repository path to its text (the workflows, scripts/ and nothing else is needed)."""
    known = set(files)
    parent: dict[str, str] = {}
    queue = [p for p in sorted(known) if p.startswith(".github/workflows/") or ENTRY.match(p)]
    seen = set(queue)
    while queue:
        cur = queue.pop(0)
        for dep in sorted(references(cur, files[cur], known)):
            if dep not in seen:
                seen.add(dep)
                parent[dep] = cur
                queue.append(dep)
    return {p: f"used by {parent[p]}" for p in parent}


def ci_files(changed: list[str], files: dict[str, str]) -> dict[str, str]:
    """{changed path: reason} for the changed files that are CI-class: direct (a workflow, scripts/ci, CODEOWNERS) or a dependency of a gate"""
    closure = gate_closure(files)
    out: dict[str, str] = {}
    for p in changed:
        if is_doc(p):
            continue
        if p in DIRECT_EXEMPT:
            continue
        if p in DIRECT_FILES or p.startswith(DIRECT_PREFIXES) or any(rx.match(p) for rx in DIRECT_PATTERNS):
            out[p] = "a workflow, a gate script, a file a gate reads, or the owners file"
        elif p in closure:
            out[p] = f"a gate dependency ({closure[p]})"
    return out
