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


def gh_output(key: str, value: str) -> None:
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            f.write(f"{key}={value}\n")


def fail(msg: str) -> None:
    print(f"::error::{msg}" if os.environ.get("GITHUB_ACTIONS") else f"FAIL: {msg}")
    sys.exit(1)


def load_schema(name: str) -> dict:
    return json.loads((ROOT / "schemas" / name).read_text())


def library_of(path: str) -> str:
    """data/<tier>/<library>.jsonl → library; data/<tier>/<library>/<file>.jsonl → library."""
    parts = path.split("/")
    return parts[2] if len(parts) == 4 else Path(path).stem
