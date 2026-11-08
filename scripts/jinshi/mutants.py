#!/usr/bin/env python3
"""mutants.py --out DIR [--module M ...] [--seed S] [--jobs J] [--timeout S] — differential kernel fuzzing (docs/jinshi.md, head K).

`tengoku-jinshi --check mutants --mutants-out DIR` (Jinshi/Mutants.lean) takes the first theorems of each examined module, applies a
fixed list of mutation operators to their proofs and statements, judges every mutant with Lean's kernel in its own process, and writes
each mutant UNCHECKED as a module of its own, DIR/JinshiMutants/<Module path>/M<k>.olean (one declaration, importing the examined
module), with DIR/generated.jsonl repeating its findings. This script runs `leanchecker` and `lean4lean` (JINSHI_LEAN4LEAN; without
it only leanchecker) on every such module, so each kernel run judges exactly one mutant, and compares the verdicts. A fourth kernel,
Nanoda (nanoda.py; independent of Lean's own code, reads lean4export's ndjson instead of an `.olean`), joins in when NANODA_BIN names
its binary (and JINSHI_LEAN4EXPORT names a lean4export binary); neither set, nothing changes here. A mutant whose export touches a
`native_decide`-style trusted head is a `skip` for nanoda, not a verdict, and is never counted as a disagreement (nanoda.py, TRUSTED_HEADS):

  fail   KERNELS DISAGREE: one of the kernels has a bug; the mutant's module is the reproducer
  warn   a kernel exceeded the timeout on a mutant, or could not run on it (its verdict is unknown)
  info   one line per examined module: how many mutants every kernel accepted, every kernel refused, how many nanoda skipped

Writes DIR/mutants.jsonl (the findings) and DIR/verdicts.jsonl (every mutant with each kernel's verdict). With `--module`, the generator
is run first (lake build tengoku-jinshi; `--seed` as the executable's). LEAN_PATH is extended by DIR (and kept otherwise: `lake env`
preserves it), so the examined modules must be reachable: the tree's build, or the fixtures' directory in LEAN_PATH. Exit 0 always.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from nanoda import nanoda_verdict

ROOT = Path(__file__).resolve().parents[2]
DETAIL = re.compile(r"^lean: (?P<lean>accept|reject\([^)]*\)); op: (?P<op>\S+); from: (?P<orig>\S+); module: (?P<module>\S+)$")


def _env(out_dir: Path, env: dict | None) -> dict:
    env = dict(env if env is not None else os.environ)
    env["LEAN_PATH"] = os.pathsep.join(p for p in [env.get("LEAN_PATH", ""), str(out_dir.resolve())] if p)
    return env


def generate(modules: list[str], out_dir: Path, seed: str | None = None, env: dict | None = None, timeout: int = 3600) -> list[dict]:
    """tengoku-jinshi --check mutants on the modules; returns its findings (the per-mutant lines carry Lean's in-process verdict)"""
    exe = ROOT / ".lake" / "build" / "bin" / "tengoku-jinshi"
    out_dir.mkdir(parents=True, exist_ok=True)
    args = ["lake", "env", str(exe), "--check", "mutants", "--mutants-out", str(out_dir.resolve())]
    if seed:
        args += ["--seed", seed]
    for m in modules:
        args += ["--module", m]
    try:
        r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=_env(out_dir, env), timeout=timeout)
    except subprocess.TimeoutExpired:
        return [
            {
                "check": "mutants",
                "severity": "warn",
                "module": "",
                "name": "",
                "line": None,
                "detail": f"tengoku-jinshi --check mutants exceeded {timeout} s: no mutants were judged",
            }
        ]
    if r.returncode:
        return [
            {
                "check": "mutants",
                "severity": "warn",
                "module": "",
                "name": "",
                "line": None,
                "detail": f"tengoku-jinshi --check mutants failed (exit {r.returncode}): {(r.stderr or r.stdout)[-600:]}",
            }
        ]
    return [f for f in (json.loads(line) for line in r.stdout.splitlines() if line.strip()) if f["check"] != "summary"]


# a kernel that did not get to judge: the module (or an import) was not found. leanchecker reports a refusal as an uncaught exception
# "while replaying declaration …", lean4lean as "found a problem in …": those are verdicts
NOT_RUN = ("Could not find any oleans", "unknown package", "object file", "No such file", "does not exist")
JUDGED = ("while replaying", "found a problem")


def kernel_verdict(cmd: list[str], env: dict, timeout: int) -> tuple[str, str]:
    """accept | reject | timeout | error (the kernel did not get to judge: a module not found, an I/O failure), and the output's tail"""
    try:
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    text = (r.stdout + r.stderr).strip()
    tail = " | ".join(text.splitlines()[-3:])[:300]
    if r.returncode == 0:
        return "accept", tail
    not_run = any(k in text for k in NOT_RUN) and not any(k in text for k in JUDGED)
    return ("error" if not_run else "reject"), tail


def judge(out_dir: Path, jobs: int = 4, timeout: int = 300, env: dict | None = None) -> tuple[list[dict], list[dict]]:
    """every mutant module of DIR/generated.jsonl judged by leanchecker, lean4lean and (NANODA_BIN set) nanoda; (findings, verdicts)"""
    gen = out_dir / "generated.jsonl"
    if not gen.is_file():
        return (
            [{"check": "mutants", "severity": "warn", "module": "", "name": "", "line": None, "detail": f"no {gen}: nothing generated"}],
            [],
        )
    kenv = _env(out_dir, env)
    lean4lean = kenv.get("JINSHI_LEAN4LEAN", "")
    nanoda_bin = kenv.get("NANODA_BIN", "")
    kernels = ["lean", "leanchecker"] + (["lean4lean"] if lean4lean else []) + (["nanoda"] if nanoda_bin else [])
    mutants = []
    for line in gen.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        f = json.loads(line)
        m = DETAIL.match(f.get("detail", ""))
        if not m or m.group("module") == "none":
            continue
        mutants.append(
            {
                "name": f["name"],
                "examined": f["module"],
                "line": f.get("line"),
                "module": m.group("module"),
                "op": m.group("op"),
                "from": m.group("orig"),
                "lean": m.group("lean"),
            }
        )

    def run(mu: dict) -> dict:
        v = {"lean": "accept" if mu["lean"] == "accept" else "reject"}
        tails = {}
        v["leanchecker"], tails["leanchecker"] = kernel_verdict(["lake", "env", "leanchecker", mu["module"]], kenv, timeout)
        if lean4lean:
            v["lean4lean"], tails["lean4lean"] = kernel_verdict(["lake", "env", lean4lean, mu["module"]], kenv, timeout)
        if nanoda_bin:
            v["nanoda"], tails["nanoda"] = nanoda_verdict(mu["module"], out_dir / "nanoda", kenv, timeout)
        return {**mu, "verdicts": v, "tails": tails}

    with ThreadPoolExecutor(max(1, jobs)) as pool:
        verdicts = list(pool.map(run, mutants))
    findings: list[dict] = []
    per_module: dict[str, dict[str, int]] = {}
    for vd in verdicts:
        c = per_module.setdefault(vd["examined"], {"mutants": 0, "accepted": 0, "refused": 0, "disagree": 0, "timeout": 0, "skipped": 0})
        c["mutants"] += 1
        vs = vd["verdicts"]
        # a native_decide-style trusted head (nanoda.py, TRUSTED_HEADS): nanoda is not a fair judge of this mutant (it only ever
        # sees the axiom, never the compiled code), so its "skip" is dropped before anything below compares the kernels' verdicts
        # — it is never counted as a disagreement, and never masks a real disagreement among the kernels that did judge
        if vs.get("nanoda") == "skip":
            c["skipped"] += 1
        judged = {k: v for k, v in vs.items() if v != "skip"}
        if "timeout" in judged.values() or "error" in judged.values():
            c["timeout"] += 1
            tails = "; ".join(f"{k}: {t}" for k, t in vd["tails"].items() if t and vs.get(k) == "error")
            findings.append(
                {
                    "check": "mutants",
                    "severity": "warn",
                    "module": vd["examined"],
                    "name": vd["name"],
                    "line": vd["line"],
                    "detail": f"a kernel did not judge the mutant (timeout {timeout} s, or it could not run): "
                    + ", ".join(f"{k}={v}" for k, v in vs.items())
                    + f"; op: {vd['op']}; from: {vd['from']}; module: {vd['module']}"
                    + (f"; {tails}" if tails else ""),
                }
            )
            continue
        if len(set(judged.values())) > 1:
            c["disagree"] += 1
            tails = "; ".join(f"{k}: {t}" for k, t in vd["tails"].items() if t)
            findings.append(
                {
                    "check": "mutants",
                    "severity": "fail",
                    "module": vd["examined"],
                    "name": vd["name"],
                    "line": vd["line"],
                    "detail": "KERNELS DISAGREE: "
                    + ", ".join(f"{k}={v}" for k, v in vs.items())
                    + f" (lean: {vd['lean']}); op: {vd['op']}; from: {vd['from']}; module: {vd['module']}"
                    + (f"; {tails}" if tails else ""),
                }
            )
        elif judged["lean"] == "accept":
            c["accepted"] += 1
        else:
            c["refused"] += 1
    for mod, c in sorted(per_module.items()):
        findings.append(
            {
                "check": "mutants",
                "severity": "info",
                "module": mod,
                "name": "",
                "line": None,
                "detail": f"{c['mutants']} mutants: {c['accepted']} accepted by every kernel, {c['refused']} refused by every kernel, "
                f"{c['disagree']} disagreements, {c['timeout']} not judged by every kernel"
                + (f", {c['skipped']} skipped by nanoda (trusted head)" if nanoda_bin else "")
                + f" (kernels: {', '.join(kernels)})",
            }
        )
    with (out_dir / "mutants.jsonl").open("w", encoding="utf-8") as fh:
        for f in findings:
            fh.write(json.dumps(f, ensure_ascii=False) + "\n")
    with (out_dir / "verdicts.jsonl").open("w", encoding="utf-8") as fh:
        for vd in verdicts:
            fh.write(json.dumps({k: v for k, v in vd.items() if k != "tails"}, ensure_ascii=False) + "\n")
    return findings, verdicts


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--module", action="append", default=[], help="generate the mutants of this module first (repeatable)")
    ap.add_argument("--seed", default=None)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=300)
    a = ap.parse_args()
    if a.module:
        for f in generate(a.module, a.out, a.seed):
            if f["severity"] != "info":
                print(json.dumps(f, ensure_ascii=False))
    findings, verdicts = judge(a.out, a.jobs, a.timeout)
    for f in findings:
        print(json.dumps(f, ensure_ascii=False))
    fails = sum(1 for f in findings if f["severity"] == "fail")
    print(f"mutants: {len(verdicts)} mutants judged, {fails} disagreements; {a.out / 'mutants.jsonl'}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
