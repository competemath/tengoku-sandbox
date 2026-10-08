#!/usr/bin/env python3
"""run.py --round K [--rounds N] [--jobs J] [--checks replay,autoimplicit,env] [--modules FILE] --out DIR — one round of Jinshi (docs/jinshi.md).

On a built tree (scripts/cache.sh get; lake build Tengoku.All; lake build tengoku-jinshi), for every module of the round:

  replay        `leanchecker <module>`: the toolchain's own kernel re-adds every declaration of the module to the environment of its
                imports. A module whose .olean holds something the kernel would not accept fails. One process per module, J at a time.
  reproduce     `lake env lean -D<lakefile leanOptions> <file>`: the module compiled again with lake's own options, its .olean compared
                byte for byte with the cached .olean the tree ships (the attested cache): a difference is a compiled artefact that is not
                what the source gives (tampering, a stale cache, or a non-reproducible compile), reported as `warn` with the byte of the
                first difference; identical ones are counted as `info`. (Round 0 compared the autoImplicit re-elaboration's olean instead,
                compiled with other options: every module differed by the same 88 bytes.)
  autoimplicit  `lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>`: the module re-elaborated with auto-bound implicits off.
                Every `unknown identifier` error is a declaration in which Lean silently quantified a name (fail); any other error is
                reported as `warn` (the re-elaboration should otherwise succeed: the module built). A module that sets
                `autoImplicit true` itself is reported as opting in (warn), since the option on the command line cannot override it.
  lean4lean     `lean4lean <module>` (digama0/lean4lean: a kernel written in Lean, independent of the C++ one in its code if not in its
                design), the same replay by a second implementation, when the binary is given by JINSHI_LEAN4LEAN (the workflow builds it).
  options       the module's `set_option` lines (in code, never in comments or strings): a heartbeat or recursion limit raised above the
                default, or set to 0 (no limit), is a module that compiles only with extra budget (fragile under any toolchain change:
                warn); `debug.*` options and `autoImplicit true` are warn; a linter switched off is info. No Lean runs.
  env           tengoku-jinshi over the round's modules in one process: the examinations the executable lists (--list).
  mutants       off by default (`--checks` must name it): `tengoku-jinshi --check mutants --mutants-out DIR/mutants` mutates the first
                theorems of each module (eight operators at fixed positions, Jinshi/Mutants.lean), judges every mutant with Lean's kernel
                in-process and writes it unchecked as a module of its own; then scripts/jinshi/mutants.py has leanchecker and lean4lean
                judge each one, plus nanoda (scripts/jinshi/nanoda.py) when NANODA_BIN and JINSHI_LEAN4EXPORT name their binaries.
                Kernels that disagree on a mutant: fail (one of them has a bug; the module is the reproducer).

Writes DIR/<check>.jsonl (one finding per line, the same shape for every check) and DIR/summary.md. Exit 0 always: the summary is the
verdict, the workflow decides. `--modules FILE` (one module name per line) replaces the round's list (a rehearsal on a few modules).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))

UNKNOWN = re.compile(
    r"^(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+): error(?:\([^)]*\))?: (?P<msg>[Uu]nknown (?:identifier|constant) `?(?P<ident>[^`\s']+)`?.*)$",
    re.M,
)
ERROR = re.compile(r"^(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+): error(?:\([^)]*\))?: (?P<msg>.*)$", re.M)
# the one DECL pattern: decl_at() (declaration attribution for a diagnostic's line) and the
# cascade-suppression filter below both use this.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|structure|inductive|class|abbrev|instance|opaque|axiom)\s+([\w.'!?]+)",
    re.M,
)


def lake_options() -> list[str]:
    """The [leanOptions] of lakefile.toml as -D flags: a compile that is to reproduce lake's olean must use lake's options."""
    text = (ROOT / "lakefile.toml").read_text(encoding="utf-8") if (ROOT / "lakefile.toml").is_file() else ""
    m = re.search(r"^\[leanOptions\]\n((?:[^\[\n][^\n]*\n?)*)", text, re.M)
    out = []
    for ln in (m.group(1) if m else "").splitlines():
        if "=" in ln and not ln.strip().startswith("#"):
            k, v = (s.strip() for s in ln.split("=", 1))
            out.append(f"-D{k}={v.strip(chr(34))}")
    return out


def reproduce_findings(path: Path, module: str, timeout: int = 1800) -> list[dict]:
    """The module compiled again with lake's own options: the olean must be byte-identical to the cached one, or the cache is not what the
    source gives today."""
    cached = ROOT / ".lake" / "build" / "lib" / "lean" / (module.replace(".", "/") + ".olean")
    if not path.is_file():
        return []  # the missing source is reported once, by the driver's input check
    if not cached.is_file():
        return [
            {
                "check": "reproduce",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": "no cached .olean for this module in .lake/build: nothing to compare the compile with (the cache does not cover the module, or was not fetched)",
            }
        ]
    out_dir = Path(tempfile.mkdtemp(prefix="jinshi-rep-"))
    olean_out = out_dir / "out.olean"
    try:
        r = subprocess.run(
            ["lake", "env", "lean", *lake_options(), "-o", str(olean_out), str(path)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        shutil.rmtree(out_dir, ignore_errors=True)
        return [
            {
                "check": "reproduce",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"re-compilation exceeded {timeout} s",
            }
        ]
    if r.returncode != 0 or not olean_out.is_file():
        shutil.rmtree(out_dir, ignore_errors=True)
        return [
            {
                "check": "reproduce",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"the module does not compile with lake's options (exit {r.returncode}): {(r.stdout + r.stderr)[-300:]}",
            }
        ]
    a, b = olean_out.read_bytes(), cached.read_bytes()
    same = a == b
    if not same:
        # where the first difference is, and whether it is only the header (the first 1 KiB) or the body
        i = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
        detail = (
            f"the re-compiled olean DIFFERS from the cached one ({len(a)} vs {len(b)} bytes, first difference at byte {i}, "
            + ("in the header" if i < 1024 else "in the body")
            + "): the cache is not what the source gives today (tampering, a stale cache, or a non-reproducible compile)"
        )
    else:
        detail = "the re-compiled olean is byte-identical to the cached one"
    shutil.rmtree(out_dir, ignore_errors=True)
    return [{"check": "reproduce", "severity": "info" if same else "warn", "module": module, "name": "", "line": None, "detail": detail}]


REALIZED = re.compile(r"constant has already been declared '[^']*\.(?:congr_simp|hcongr(?:_[A-Za-z0-9_]+)?)'")
OPT_IN = re.compile(r"^\s*set_option\s+autoImplicit\s+true\b", re.M)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


NS = re.compile(r"^\s*(namespace|end)\s+([^\s]+)\s*$", re.M)
GREEK = re.compile(r"^[α-ωΑ-Ω][₀-₉'0-9]*$")


def decl_at(text: str, line: int) -> str:
    """the name of the declaration whose header is the nearest one at or above `line` (1-based), with the namespaces open there"""
    events = [(m.start(), "decl", m.group(1)) for m in DECL.finditer(text)] + [
        (m.start(), m.group(1), m.group(2)) for m in NS.finditer(text)
    ]
    events.sort()
    stack: list[str] = []
    best = ""
    for pos, kind, name in events:
        if text.count("\n", 0, pos) + 1 > line:
            break
        if kind == "namespace":
            stack.append(name)
        elif kind == "end":
            if stack and stack[-1] == name:
                stack.pop()
        else:
            best = ".".join(stack + [name]) if not name.startswith("_root_.") else name[len("_root_.") :]
    return best


# --- autoimplicit near-miss: is a silently auto-bound name a typo of something already in scope? ---
# A near-miss is reported only as an enrichment of the existing finding's detail string (never a
# severity change): it is a hint for a human triaging a round's fails, not a verdict.
IDENT = re.compile(r"[A-Za-zΑ-Ωα-ω_][A-Za-z0-9_'!?₀-₉]*")
_KEYWORDS = {
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive", "opaque", "axiom",
    "private", "protected", "noncomputable", "unsafe", "partial", "nonrec", "scoped", "local", "where", "deriving",
    "by", "do", "let", "have", "fun", "match", "with", "if", "then", "else", "from", "show", "suffices", "calc",
    "Type", "Prop", "Sort", "True", "False", "Nat", "Int", "sorry", "in", "open", "import", "namespace", "end",
    "variable", "variables", "section", "universe", "mut", "mutual", "set_option", "attribute",
}
VARIABLE_LINE = re.compile(r"^\s*variables?\s*(?:\([^)]*\)|\{[^}]*\}|⦃[^⦄]*⦄|\[[^\]]*\])*", re.M)


def _levenshtein(a: str, b: str) -> int:
    if a == b:
        return 0
    if len(a) > len(b):
        a, b = b, a
    prev = list(range(len(a) + 1))
    for i, cb in enumerate(b, 1):
        cur = [i] + [0] * len(a)
        for j, ca in enumerate(a, 1):
            cur[j] = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb))
        prev = cur
    return prev[-1]


def near_miss(ident: str, candidates: set[str]) -> tuple[str, int] | None:
    """the UNIQUE closest candidate to `ident` within a length-scaled edit-distance budget, or None.

    Deterministic by construction: every candidate at the best distance is collected, and a result is
    returned only when exactly one achieves it. A tie between two equally-plausible candidates (both
    `n` and `h` are one edit from `m`) is genuinely ambiguous, not a confident "likely meant X", so it
    is reported as no match rather than an arbitrary pick -- the first version of this picked whichever
    tied candidate happened to come first in a `set`'s iteration order, which is nondeterministic across
    runs; a dedicated regression test for exactly a tie now guards this (see selftest.py).
    """
    budget = 1 if len(ident) <= 3 else 2
    by_distance: dict[int, list[str]] = {}
    for c in sorted(candidates):
        if c == ident or c in _KEYWORDS or ident in _KEYWORDS:
            continue
        d = _levenshtein(ident, c)
        if d <= budget:
            by_distance.setdefault(d, []).append(c)
    if not by_distance:
        return None
    d = min(by_distance)
    tied = by_distance[d]
    return (tied[0], d) if len(tied) == 1 else None


def candidates_in_scope(text: str, line: int) -> set[str]:
    """identifiers plausibly already in scope at `line`: every identifier in the enclosing
    declaration's own source span, plus every name bound by a `variable`/`variables` line earlier in
    the file (the common case: a shared `variable` was renamed or removed, and a later declaration
    still spells the old name, which auto-binds instead of erroring)."""
    starts = sorted(m.start() for m in DECL.finditer(text))
    offset = 0
    for i, ln in enumerate(text.split("\n"), 1):
        if i == line:
            break
        offset += len(ln) + 1
    enclosing = max((s for s in starts if s <= offset), default=None)
    end = min((s for s in starts if s > (enclosing if enclosing is not None else -1)), default=len(text))
    span = text[enclosing:end] if enclosing is not None else ""
    names = {m.group(0) for m in IDENT.finditer(span)}
    for vm in VARIABLE_LINE.finditer(text):
        if vm.start() >= offset:
            continue
        names |= {m.group(0) for m in IDENT.finditer(vm.group(0))}
    return names - _KEYWORDS


def autoimplicit_findings(path: Path, module: str, lake: bool = False, timeout: int = 1800) -> list[dict]:
    if not path.is_file():
        return [
            {
                "check": "autoimplicit",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"no source file at {path.relative_to(ROOT) if path.is_absolute() else path}: not a module of the tree?",
            }
        ]
    text = path.read_text(encoding="utf-8", errors="replace")
    olean_out = Path(tempfile.mkdtemp(prefix="jinshi-")) / "out.olean"
    cmd = (["lake", "env"] if lake else []) + [
        "lean",
        "-DautoImplicit=false",
        "-DrelaxedAutoImplicit=false",
        "-o",
        str(olean_out),
        str(path),
    ]
    out: list[dict] = []
    if OPT_IN.search(text):
        out.append(
            {
                "check": "autoimplicit",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": text[: OPT_IN.search(text).start()].count("\n") + 1,
                "detail": "the module sets `autoImplicit true` itself: the re-elaboration cannot turn it off; read its statements by hand",
            }
        )
    try:
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return out + [
            {
                "check": "autoimplicit",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"re-elaboration exceeded {timeout} s",
            }
        ]
    log = r.stdout + r.stderr
    errors = list(ERROR.finditer(log))
    shutil.rmtree(olean_out.parent, ignore_errors=True)
    seen = set()
    # a declaration that failed makes every LATER use of it "unknown": not a finding. Only an earlier declaration can have failed, so
    # the short name is suppressed only below the line that declares it (`theorem t : P → P` before `def P` keeps its auto-bound `P`).
    declared_at: dict[str, int] = {}
    for d in DECL.finditer(text):
        declared_at.setdefault(d.group(1).rsplit(".", 1)[-1], text[: d.start()].count("\n") + 1)
    for m in errors:
        line = int(m.group("line"))
        u = UNKNOWN.match(m.group(0))
        name = decl_at(text, line)
        key = (name, u.group("ident") if u else m.group("msg")[:60])
        if key in seen:
            continue
        seen.add(key)
        if u and declared_at.get(u.group("ident").rsplit(".", 1)[-1], 10**9) < line:
            continue
        if u:
            ident = u.group("ident")
            greek = bool(GREEK.match(ident))  # a Greek letter is the idiom for a type variable: quantified on purpose, almost always
            miss = near_miss(ident, candidates_in_scope(text, line))
            out.append(
                {
                    "check": "autoimplicit",
                    "severity": "warn" if greek else "fail",
                    "module": module,
                    "name": name,
                    "line": line,
                    "detail": f"with autoImplicit off: {m.group('msg').strip()} — Lean quantified `{ident}` in this declaration silently"
                    + (" (a Greek letter: a type variable by convention; check it is one)" if greek else "")
                    + (f" (one edit from `{miss[0]}`, already in scope here: likely a typo, not an intentional free variable)" if miss else ""),
                }
            )
        else:
            out.append(
                {
                    "check": "autoimplicit",
                    "severity": "warn",
                    "module": module,
                    "name": name,
                    "line": line,
                    "detail": f"with autoImplicit off the module does not re-elaborate: {m.group('msg').strip()[:200]}",
                }
            )
    return out


SET_OPTION = re.compile(r"^[ \t]*set_option[ \t]+([\w.]+)[ \t]+([^\s]+)", re.M)
BUDGETS = {
    "maxHeartbeats": 200000,
    "synthInstance.maxHeartbeats": 20000,
    "maxRecDepth": 512,
    "synthInstance.maxSize": 128,
    "exponentiation.threshold": 256,
}


def options_findings(path: Path, module: str) -> list[dict]:
    """the module's set_option lines, read from the code (scripts/ci/lean_lex.py blanks comments and strings)"""
    if not path.is_file():
        return []
    sys.path.insert(0, str(ROOT / "scripts" / "ci"))
    from lean_lex import code_only  # noqa: E402

    code = code_only(path.read_text(encoding="utf-8", errors="replace"))
    out = []
    for m in SET_OPTION.finditer(code):
        name, value = m.group(1), m.group(2)
        line = code.count("\n", 0, m.start()) + 1
        if name in BUDGETS:
            try:
                v = int(value)
            except ValueError:
                continue
            if v == 0 or v > BUDGETS[name]:
                out.append(
                    {
                        "check": "options",
                        "severity": "warn",
                        "module": module,
                        "name": "",
                        "line": line,
                        "detail": f"`set_option {name} {value}`: the module compiles only with {'no limit' if v == 0 else 'more budget than the default ' + str(BUDGETS[name])} (fragile under any toolchain change)",
                    }
                )
        elif name.startswith("debug."):
            out.append(
                {
                    "check": "options",
                    "severity": "warn",
                    "module": module,
                    "name": "",
                    "line": line,
                    "detail": f"`set_option {name} {value}`: a debug option in shipped code",
                }
            )
        elif name in ("autoImplicit", "relaxedAutoImplicit") and value == "true":
            out.append(
                {
                    "check": "options",
                    "severity": "warn",
                    "module": module,
                    "name": "",
                    "line": line,
                    "detail": f"`set_option {name} true`: auto-bound implicits switched on by the module itself",
                }
            )
        elif name.startswith("linter.") and value == "false":
            out.append(
                {
                    "check": "options",
                    "severity": "info",
                    "module": module,
                    "name": "",
                    "line": line,
                    "detail": f"`set_option {name} false`: a linter switched off",
                }
            )
    return out


def replay_finding(module: str, timeout: int = 1800) -> list[dict]:
    try:
        r = subprocess.run(["lake", "env", "leanchecker", module], cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return [
            {
                "check": "replay",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"leanchecker exceeded {timeout} s",
            }
        ]
    if r.returncode == 0:
        return []
    tail = (r.stdout + r.stderr).strip().splitlines()[-5:]
    return [
        {
            "check": "replay",
            "severity": "fail",
            "module": module,
            "name": "",
            "line": None,
            "detail": f"leanchecker refused the module (exit {r.returncode}): " + " | ".join(tail)[:600],
        }
    ]


def lean4lean_finding(module: str, timeout: int = 1800) -> list[dict]:
    binary = os.environ.get("JINSHI_LEAN4LEAN", "")
    if not binary:
        return []
    try:
        r = subprocess.run(["lake", "env", binary, module], cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return [
            {
                "check": "lean4lean",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"lean4lean exceeded {timeout} s",
            }
        ]
    if r.returncode == 0:
        return []
    tail = (r.stdout + r.stderr).strip().splitlines()[-5:]
    return [
        {
            "check": "lean4lean",
            "severity": "info" if REALIZED.search(" ".join(tail)) else "fail",
            "module": module,
            "name": "",
            "line": None,
            "detail": (
                "lean4lean refused a realized constant (a reserved `congr_simp`/`hcongr` name that several modules may create; Lean deduplicates them at import, lean4lean does not model that: not a finding about the tree): "
                if REALIZED.search(" ".join(tail))
                else f"lean4lean refused the module (exit {r.returncode}): "
            )
            + " | ".join(tail)[:600],
        }
    ]


def env_findings(modules: list[str]) -> list[dict]:
    exe = ROOT / ".lake" / "build" / "bin" / "tengoku-jinshi"
    args = [str(exe)]
    for m in modules:
        args += ["--module", m]
    r = subprocess.run(["lake", "env"] + args, cwd=ROOT, capture_output=True, text=True)
    if r.returncode:
        return [
            {
                "check": "env",
                "severity": "warn",
                "module": "",
                "name": "",
                "line": None,
                "detail": f"tengoku-jinshi failed (exit {r.returncode}): {(r.stderr or r.stdout)[-600:]}",
            }
        ]
    # the executable ends with one {"check": "summary", ...} line of counts: not a finding
    return [f for f in (json.loads(line) for line in r.stdout.splitlines() if line.strip()) if f.get("check") != "summary"]


def summarize(rnd: int, modules: list[str], results: dict[str, list[dict]], timings: dict[str, float]) -> list[str]:
    """the Markdown summary of a round (or of a merged set of shards): counts per check, every fail, the warns, the Jinshi grade"""
    lines = [f"# Jinshi — round {rnd} — {len(modules)} modules", "", "| check | fail | warn | info | time |", "|---|---:|---:|---:|---:|"]
    for check, fs in sorted(results.items()):
        n = {s: sum(1 for f in fs if f["severity"] == s) for s in ("fail", "warn", "info")}
        lines.append(f"| {check} | {n['fail']} | {n['warn']} | {n['info']} | {timings.get(check, 0):.0f} s |")
    fails = [f for fs in results.values() for f in fs if f["severity"] == "fail"]
    if fails:
        lines += ["", f"## Fail ({len(fails)})", ""]
        for f in fails[:300]:
            lines.append(
                f"- `{f['check']}` {f['module']}"
                + (f" `{f['name']}`" if f["name"] else "")
                + (f" line {f['line']}" if f.get("line") else "")
                + f": {f['detail'][:300]}"
            )
    warns = [f for fs in results.values() for f in fs if f["severity"] == "warn"]
    if warns:
        by_check: dict[str, int] = {}
        for f in warns:
            by_check[f["check"]] = by_check.get(f["check"], 0) + 1
        lines += ["", f"## Warn ({len(warns)}): " + ", ".join(f"{k} {v}" for k, v in sorted(by_check.items())), ""]
        for f in warns[:150]:
            lines.append(f"- `{f['check']}` {f['module']}" + (f" `{f['name']}`" if f["name"] else "") + f": {f['detail'][:200]}")
    by_module: dict[str, int] = {}
    for fs in results.values():
        for f in fs:
            if f["severity"] in ("fail", "warn") and f["check"] != "summary":
                by_module[f["module"]] = by_module.get(f["module"], 0) + 1
    clean = [m for m in modules if m not in by_module]
    lines += [
        "",
        f"**Jinshi grade**: {len(clean)} of {len(modules)} modules with no fail and no warn ({100 * len(clean) / max(1, len(modules)):.1f}%).",
    ]
    return lines


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--round", type=int, default=0)
    ap.add_argument("--rounds", type=int, default=10)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 1))
    ap.add_argument("--checks", default="replay,lean4lean,autoimplicit,options,env")
    ap.add_argument("--modules", type=Path, help="one module name per line, instead of the round")
    ap.add_argument(
        "--shard",
        default="",
        help="k/N: only every N-th module of the sorted list, starting at k (0-based); the shards of a round partition it",
    )
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    checks = {c.strip() for c in a.checks.split(",") if c.strip()}
    a.out.mkdir(parents=True, exist_ok=True)

    if a.modules:
        modules = [ln.strip() for ln in a.modules.read_text().splitlines() if ln.strip() and not ln.startswith("#")]
    else:
        from partition import bucket, lean_modules, read_ledger  # noqa: E402

        ledger, _ = read_ledger()
        modules = []
        for u in lean_modules():
            if u["kind"] == "root":
                continue
            rnd = ledger.get(u["path"], bucket(u["path"], a.rounds))
            if rnd == a.round:
                modules.append(u["module"])
    modules.sort()
    if a.shard:
        k, n = (int(x) for x in a.shard.split("/"))
        modules = [m for i, m in enumerate(modules) if i % n == k]
    (a.out / "modules.txt").write_text("\n".join(modules) + "\n")
    missing = [m for m in modules if not module_path(m).is_file()]
    results: dict[str, list[dict]] = {}
    timings: dict[str, float] = {}
    if missing:
        results["input"] = [
            {
                "check": "input",
                "severity": "warn",
                "module": m,
                "name": "",
                "line": None,
                "detail": "no source file in the tree for this module name",
            }
            for m in missing
        ]
        modules = [m for m in modules if m not in set(missing)]
        print(f"{len(missing)} named modules have no source file in the tree: {missing[:5]}", flush=True)
    print(f"jinshi round {a.round}: {len(modules)} modules, checks {sorted(checks)}, {a.jobs} jobs", flush=True)

    def flush(check: str) -> None:
        with (a.out / f"{check}.jsonl").open("w", encoding="utf-8") as fh:
            for f in results.get(check, []):
                fh.write(json.dumps(f, ensure_ascii=False) + "\n")
        (a.out / "timings.json").write_text(json.dumps(timings))

    if "replay" in checks:
        t = time.time()
        with ThreadPoolExecutor(a.jobs) as pool:
            results["replay"] = [f for fs in pool.map(replay_finding, modules) for f in fs]
        timings["replay"] = time.time() - t
        print(f"replay: {len(results['replay'])} findings in {timings['replay']:.0f} s", flush=True)
        flush("replay")
    if "lean4lean" in checks and os.environ.get("JINSHI_LEAN4LEAN"):
        t = time.time()
        with ThreadPoolExecutor(a.jobs) as pool:
            results["lean4lean"] = [f for fs in pool.map(lean4lean_finding, modules) for f in fs]
        timings["lean4lean"] = time.time() - t
        print(f"lean4lean: {len(results['lean4lean'])} findings in {timings['lean4lean']:.0f} s", flush=True)
        flush("lean4lean")
    if "autoimplicit" in checks:
        t = time.time()
        with ThreadPoolExecutor(a.jobs) as pool:
            both = [f for fs in pool.map(lambda m: autoimplicit_findings(module_path(m), m, lake=True), modules) for f in fs]
        results["autoimplicit"] = [f for f in both if f["check"] == "autoimplicit"]
        timings["autoimplicit"] = time.time() - t
        print(f"autoimplicit: {len(results['autoimplicit'])} findings in {timings['autoimplicit']:.0f} s", flush=True)
        flush("autoimplicit")
    if "reproduce" in checks:
        t = time.time()
        with ThreadPoolExecutor(a.jobs) as pool:
            results["reproduce"] = [f for fs in pool.map(lambda m: reproduce_findings(module_path(m), m), modules) for f in fs]
        timings["reproduce"] = time.time() - t
        print(f"reproduce: {len(results['reproduce'])} findings in {timings['reproduce']:.0f} s", flush=True)
        flush("reproduce")
    if "options" in checks:
        t = time.time()
        results["options"] = [f for m in modules for f in options_findings(module_path(m), m)]
        timings["options"] = time.time() - t
        flush("options")
        print(f"options: {len(results['options'])} findings in {timings['options']:.0f} s", flush=True)
    if "env" in checks:
        t = time.time()
        fs = env_findings(modules)
        timings["env"] = time.time() - t
        for f in fs:
            results.setdefault(f["check"], []).append(f)
        print(f"env: {len(fs)} findings in {timings['env']:.0f} s", flush=True)
        for check in {f["check"] for f in fs}:
            flush(check)
    if "mutants" in checks:
        t = time.time()
        from mutants import generate, judge  # noqa: E402

        mdir = a.out / "mutants"
        gen = generate(modules, mdir, timeout=3600)
        fs, verdicts = judge(mdir, jobs=a.jobs)
        results["mutants"] = [f for f in gen if not f["detail"].startswith("lean: ")] + fs
        timings["mutants"] = time.time() - t
        flush("mutants")
        print(f"mutants: {len(verdicts)} mutants judged, {len(results['mutants'])} findings in {timings['mutants']:.0f} s", flush=True)

    for check, fs in results.items():
        with (a.out / f"{check}.jsonl").open("w", encoding="utf-8") as fh:
            for f in fs:
                fh.write(json.dumps(f, ensure_ascii=False) + "\n")

    (a.out / "timings.json").write_text(json.dumps(timings))
    lines = summarize(a.round, modules, results, timings)
    (a.out / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines[:8]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
