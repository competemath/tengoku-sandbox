"""Shared helpers for the CI gates: diff parsing and tiering. Standard library only."""

from __future__ import annotations

import fnmatch
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(os.environ.get("TENGOKU_CI_ROOT") or Path(__file__).resolve().parents[2])

# Path classes (docs: security plan §3). First match wins.
TIERS = [
    ("derived", ["Tengoku/*/**", "Tengoku/All.lean", "data/stats.json", "data/cache-latest.json"]),
    ("content", ["data/tentative/*.jsonl", "data/staging/*.jsonl", "data/tentative/*/*.jsonl", "data/staging/*/*.jsonl"]),
    ("tombstone", ["data/trusted/*.jsonl"]),
    (
        "tooling",
        [
            "Tengoku.lean",
            "Tengoku/*.lean",
            "lean-toolchain",
            "lakefile.toml",
            "lake-manifest.json",
            "scripts/**",
            "TengokuExtract.lean",
            "TengokuAxioms.lean",
            ".github/**",
            "schemas/**",
            ".pre-commit-config.yaml",
            "pyproject.toml",
            ".gitleaks.toml",
        ],
    ),
    ("docs", ["README.md", "CONTRIBUTING.md", "docs/**", "LICENSE*", "*.md"]),
]
APPEND_ONLY = [
    "data/tentative/*.jsonl",
    "data/staging/*.jsonl",
    "data/trusted/*.jsonl",
    "data/tentative/*/*.jsonl",
    "data/staging/*/*.jsonl",
]


def _pascal(s: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[-_ ]+", s) if w)


def derived_prefixes() -> list[str]:
    """Generated library modules: Tengoku/<Library>/** and Tengoku/<Library>.lean for every data library."""
    libs = {f.stem for tier in ("trusted", "staging", "tentative") for f in (ROOT / "data" / tier).glob("*.jsonl")}
    out = []
    for lib in libs:
        ns = _pascal(lib)
        out += [f"Tengoku/{ns}/", f"Tengoku/{ns}.lean"]
    return out


def run(*args: str, check: bool = True) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=check).stdout


def match(path: str, patterns: list[str]) -> bool:
    for p in patterns:
        if fnmatch.fnmatch(path, p):
            return True
        if p.endswith("/**") and path.startswith(p[:-3] + "/"):
            return True
        if "/**" in p and not p.endswith("/**"):
            head, tail = p.split("/**", 1)
            if path.startswith(head + "/") and fnmatch.fnmatch(path, "*" + tail):
                return True
    return False


def tier_of(path: str) -> str:
    # Generated library modules live under Tengoku/<Library>/ — anything not a seeded topic directory.
    if path in ("Tengoku/All.lean", "data/stats.json", "data/cache-latest.json") or any(
        path == d or path.startswith(d) for d in derived_prefixes()
    ):
        return "derived"
    for name, pats in TIERS[1:]:
        if match(path, pats):
            return name
    return "tooling"


def _range(base: str, head: str) -> list[str]:
    return ["--cached"] if head == "--staged" else [f"{base}...{head}" if "..." not in base else base]


def changed_files(base: str, head: str) -> list[tuple[str, str]]:
    """[(status, path)] with status A/M/D/R…; renames reported as D old + A new. head='--staged' means the index."""
    out = []
    for line in run("diff", "--name-status", "-M", *_range(base, head)).splitlines():
        parts = line.split("\t")
        st = parts[0][0]
        if st == "R":
            out.append(("D", parts[1]))
            out.append(("A", parts[2]))
        else:
            out.append((st, parts[-1]))
    return out


def added_lines(base: str, head: str, path: str) -> list[tuple[int, str]]:
    """(new line number, text) for lines added in the diff of one file."""
    diff = run("diff", "-U0", *_range(base, head), "--", path)
    out, new_no = [], 0
    for line in diff.splitlines():
        if line.startswith("@@"):
            m = re.search(r"\+(\d+)(?:,(\d+))?", line)
            new_no = int(m.group(1))
        elif line.startswith("+") and not line.startswith("+++"):
            out.append((new_no, line[1:]))
            new_no += 1
        elif line.startswith("-") and not line.startswith("---"):
            pass
        elif not line.startswith(("diff", "index", "\\")):
            new_no += 1
    return out


def removed_lines(base: str, head: str, path: str) -> list[tuple[int, str]]:
    diff = run("diff", "-U0", *_range(base, head), "--", path)
    out, old_no = [], 0
    for line in diff.splitlines():
        if line.startswith("@@"):
            m = re.search(r"-(\d+)(?:,(\d+))?", line)
            old_no = int(m.group(1))
        elif line.startswith("-") and not line.startswith("---"):
            out.append((old_no, line[1:]))
            old_no += 1
        elif line.startswith("+"):
            pass
        elif not line.startswith(("diff", "index", "\\")):
            old_no += 1
    return out


def blob(rev: str, path: str) -> bytes | None:
    spec = f":{path}" if rev == "--staged" else f"{rev}:{path}"
    r = subprocess.run(["git", "show", spec], cwd=ROOT, capture_output=True)
    return r.stdout if r.returncode == 0 else None


def deregistered(base: str, path: str) -> bool:
    """A tentative or staging file none of whose records (as of `base`) comes from a source still on the
    allowlist (schemas/sources.json `allowed`, as checked out): its source was taken off the allowlist,
    and the file may be deleted, credits and all (append_only.py, credits.py)."""
    if not path.startswith(("data/tentative/", "data/staging/")):
        return False
    allowed = load_schema("sources.json")["allowed"]
    urls = []
    for line in (blob(base, path) or b"").splitlines():
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except ValueError:
            return False
        if "tombstone" not in r:
            urls.append(str(r.get("source_url", "")))
    return bool(urls) and not any(u.startswith(s) for u in urls for s in allowed)


def gh_output(key: str, value: str) -> None:
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            f.write(f"{key}={value}\n")


def fail(msg: str) -> None:
    if os.environ.get("GITHUB_ACTIONS"):
        # `::error::` becomes a check-run annotation (what the verdict comment quotes); newlines must be
        # %0A-encoded or GitHub keeps only the first line. The readable form goes to the log too.
        print("::error::" + msg.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A"))
    print("FAIL: " + msg)
    sys.exit(1)


def load_schema(name: str) -> dict:
    return json.loads((ROOT / "schemas" / name).read_text())


def library_of(path: str) -> str:
    """data/<tier>/<library>.jsonl → library; data/<tier>/<library>/<file>.jsonl → library."""
    parts = path.split("/")
    return parts[2] if len(parts) == 4 else Path(path).stem


def pascal(s: str) -> str:
    """equational-theories -> EquationalTheories (the generated library directory)."""
    return "".join(w[:1].upper() + w[1:] for w in s.replace("_", "-").split("-") if w)


def library_of_module(path: str, libraries) -> str | None:
    """Tengoku/<Pascal>/... or Tengoku/<Pascal>.lean -> the library it is generated from (one of `libraries`), else None."""
    parts = path.split("/")
    if len(parts) < 2 or parts[0] != "Tengoku":
        return None
    head = parts[1][:-5] if len(parts) == 2 and parts[1].endswith(".lean") else parts[1]
    return next((lib for lib in libraries if pascal(lib) == head), None)


_DECL = r"(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom)"
_SCOPE_OR_DECL = re.compile(
    r"^[ \t]*(?:(namespace)\s+(\S+)|((?:(?:noncomputable|private|public|protected)\s+)*section\b|mutual\b)[^\n]*|(end)\b[^\n]*|"
    r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|nonrec|partial|unsafe)\s+)*" + _DECL + r"\s+([^\s(\[{:⦃]+))",
    re.M,
)


def declared_names(text: str) -> set[str]:
    """Full names a Lean module declares: comments and strings ignored (lean_lex), each name resolved against the
    `namespace` blocks around it (`namespace Other … theorem foo` declares `Other.foo`; `_root_.x` declares `x`)."""
    from lean_lex import code_only

    names: set[str] = set()
    stack: list[list[str]] = []  # one entry per block `end` closes: namespaces add their name; sections, mutual add nothing
    for m in _SCOPE_OR_DECL.finditer(code_only(text)):
        ns, ns_name, sec, end, decl = m.groups()
        if ns:
            stack.append(ns_name.split("."))
        elif sec:
            stack.append([])
        elif end:
            if stack:
                stack.pop()
        elif decl:
            prefix = [p for scope in stack for p in scope]
            names.add(decl[len("_root_.") :] if decl.startswith("_root_.") else ".".join(prefix + [decl]))
    return names


def unplaced(names: set[str], texts: list[str]) -> list[str]:
    """Records no candidate module declares. A module may wrap its records in a library namespace
    (`EquationalTheories`), so a declared name counts when it is the record's name or ends with `.<name>`."""
    declared = set().union(*(declared_names(t) for t in texts)) if texts else set()
    return sorted(n for n in names if not any(d == n or d.endswith("." + n) for d in declared))
