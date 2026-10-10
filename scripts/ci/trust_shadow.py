#!/usr/bin/env python3
"""trust_shadow.py gather — the evidence a PR already has, written in the trust program's shared format (docs/trust-shadow.md).

  trust_shadow.py gather --repo R --pr N --base SHA --head SHA --author LOGIN --out DIR [--checks FILE]

Runs main's own gates over the PR read as git objects (never checked out): the banked-content lint (lint_banked.py), the
sorry scan (sorry_scan.py) and the class (classify.py). Reads the commit's check runs from a file (`gh api` output the
workflow saved) and turns each into a record. Writes DIR/case.json and DIR/evidence/*.json, the manifest first. Nothing
here decides anything: the judge (tengoku-juridicator) does, in the next step. Standard library only."""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import subprocess
import sys
from pathlib import Path

from trust_vendor.juridicator_evidence import make_evidence

CI = Path(__file__).resolve().parent
SHA = re.compile(r"^[0-9a-f]{40}$")
LOGIN = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9/\[\]-]{0,59})$")  # a user, or a bot such as dependabot[bot]
STATIC = {"role": "tooling", "name": "trust-shadow", "identity": "trust-shadow"}
# the checks whose failure is a mechanical fact about the PR; every other check is third-party or advisory and is only noted
BLOCKING_CHECKS = ("pr-gate",)
CLASS_OF = {
    "content": "content",
    "tombstone": "content",
    "tag": "content",
    "intake": "content",
    "native": "native",
    "tooling": "tooling",
    "restructure": "tooling",
    "scope-fix": "tooling",
    "docs": "docs",
}
OUR_CHECKS = ("trust-shadow", "trust-ledger", "trust-label")
TIMEOUT = 300


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def statute_class(classify_output: str) -> str:
    """classify.py prints `class=<name> ...`; the judge's classes are fewer (CLASS_OF), anything unknown is judged by default."""
    m = re.search(r"^class=([a-z-]+)", classify_output, re.M)
    return CLASS_OF.get(m.group(1), "other") if m else "other"


def case_dict(repo: str, head: str, cls: str, author: str) -> dict:
    if not SHA.match(head):
        raise ValueError("head must be a 40-character commit")
    if not LOGIN.match(author):
        raise ValueError("author is not a GitHub login")
    return {"repo": repo, "head_sha": head, "class": cls, "author": {"identity": author}}


def _case_ref(case: dict) -> dict:
    return {"repo": case["repo"], "head_sha": case["head_sha"], "class": case["class"]}


def _record(case: dict, producer: dict, kind: str, claim: str, outcome: str, verifiability: str, created: str, **kw) -> dict:
    return make_evidence(
        case=_case_ref(case),
        producer=producer,
        kind=kind,
        claim=claim[:300],
        outcome=outcome,
        verifiability=verifiability,
        created=created,
        **kw,
    )


CONTENT_CLASSES = ("content", "native")


def manifest(case: dict, created: str) -> dict:
    kinds = ["mechanical.content_lint"] + (["mechanical.no_sorry"] if case["class"] in CONTENT_CLASSES else [])
    return _record(
        case,
        STATIC,
        "manifest.declared",
        "trust-shadow declares the checks it will report on this PR",
        "pass",
        "attested",
        created,
        details={"checks": kinds, "expected": [{"kind": k, "subject": {"scope": "pr"}} for k in kinds]},
    )


def lint_record(case: dict, base: str, head: str, returncode: int, output: str, created: str) -> dict:
    """pass: exit 0. fail: the lint ran and refused something (it says so). Anything else (a crashed script, a missing
    object) is inconclusive: a tool error is never a verdict about the PR."""
    refused = "banked content lint:" in output
    ok = returncode == 0
    tail = " ".join(output.split())[-160:]
    if ok:
        outcome, claim = "pass", "The banked-content lint passes on what this PR adds."
    elif refused:
        outcome, claim = "fail", f"The banked-content lint fails: {tail}"
    else:
        outcome, claim = "inconclusive", f"The banked-content lint could not run (exit {returncode}): {tail}"
    return _record(
        case,
        STATIC,
        "mechanical.content_lint",
        claim,
        outcome,
        "mechanical",
        created,
        subject={"scope": "pr"},
        reproduce={"command": f"python3 scripts/ci/lint_banked.py {base} {head}"},
        details={"returncode": returncode},
    )


def sorry_record(case: dict, base: str, head: str, returncode: int, output: str, created: str) -> dict:
    """For a content or native PR a sorry is a mechanical failure (the queue's Leak IV would refuse it). For any other PR,
    sorry_scan.py only lists words in tool files, which is normal, so it is noted and weighs nothing."""
    clean = "no sorry/admit in added content" in output
    n = len(re.findall(r"^- ", output, re.M))
    reproduce = {"command": f"python3 scripts/ci/sorry_scan.py {base} {head}"}
    if case["class"] not in CONTENT_CLASSES:
        claim = (
            "No sorry or admit in what this PR adds."
            if clean
            else f"{n} mention(s) of sorry or admit in this non-content PR (noted, not weighed)."
        )
        return _record(
            case,
            STATIC,
            "attested.sorry_noted",
            claim,
            "pass" if clean else "fail",
            "attested",
            created,
            subject={"scope": "pr"},
            details={"occurrences": n},
        )
    if returncode != 0 or not (clean or n):
        return _record(
            case,
            STATIC,
            "mechanical.no_sorry",
            f"The sorry scan could not run (exit {returncode}).",
            "inconclusive",
            "mechanical",
            created,
            subject={"scope": "pr"},
            reproduce=reproduce,
            details={"returncode": returncode},
        )
    claim = "No sorry or admit in what this PR adds." if clean else f"{n} sorry or admit found in what this PR adds."
    return _record(
        case,
        STATIC,
        "mechanical.no_sorry",
        claim,
        "pass" if clean else "fail",
        "mechanical",
        created,
        subject={"scope": "pr"},
        reproduce=reproduce,
        details={"occurrences": n},
    )


def check_records(case: dict, check_runs: list, created: str) -> list:
    """One record per finished check run on the commit. A required check is a mechanical fact (its job link reproduces it);
    every other check is noted as an attested record, which the judge shows and weighs at zero. Skipped and still-running
    checks are left out (they say nothing yet); a cancelled one is inconclusive."""
    # a re-run leaves the earlier run on the commit: the latest finished run of a name is the one that counts
    latest: dict = {}
    for cr in check_runs:
        if isinstance(cr, dict) and isinstance(cr.get("name"), str) and cr.get("status") == "completed":
            key = (str(cr.get("completed_at") or ""), cr.get("id") if isinstance(cr.get("id"), int) else 0)
            if cr["name"] not in latest or key >= latest[cr["name"]][0]:
                latest[cr["name"]] = (key, cr)
    out = []
    for name in sorted(latest):
        cr = latest[name][1]
        conclusion = cr.get("conclusion")
        if name in OUR_CHECKS or conclusion in (None, "skipped", "neutral", "stale"):
            continue
        producer = {"role": "tooling", "name": "github-actions", "identity": f"ci:{name}"[:120]}
        outcome = {"success": "pass", "cancelled": "inconclusive"}.get(conclusion, "fail")
        link = cr.get("html_url") if isinstance(cr.get("html_url"), str) else ""
        if name in BLOCKING_CHECKS:
            out.append(
                _record(
                    case,
                    producer,
                    "mechanical.ci",
                    f"Required check {name}: {conclusion}.",
                    outcome,
                    "mechanical",
                    created,
                    subject={"check": name},
                    reproduce={"command": f"gh run view --log --job {cr.get('id')} -R {case['repo']}"},
                    details={"conclusion": conclusion, "url": link[:200]},
                )
            )
        else:
            out.append(
                _record(
                    case,
                    producer,
                    "attested.ci_advisory",
                    f"Check {name}: {conclusion} (noted, not weighed).",
                    "pass" if outcome == "pass" else "fail",
                    "attested",
                    created,
                    subject={"check": name},
                    details={"conclusion": conclusion, "url": link[:200]},
                )
            )
    return out


def run(args: list, cwd: Path, env: dict | None = None) -> tuple[int, str]:
    done = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=TIMEOUT, check=False, env=env)
    return done.returncode, done.stdout + done.stderr


def gather(a: argparse.Namespace) -> int:
    created = now()
    for sha in (a.base, a.head):
        if not SHA.match(sha):
            print("trust_shadow: base and head must be 40-character commits", file=sys.stderr)
            return 2
    root = CI.parents[1]
    # classify.py asks who opened the PR (a native or tag PR must come from the factory's account); pr-gate already judged that
    # for this PR, so the class is read the way the merge queue reads it
    code, out = run(
        [sys.executable, str(CI / "classify.py"), a.base, a.head], root, {**os.environ, "PR_ACTOR": a.author, "TENGOKU_ACTOR_CHECKED": "1"}
    )
    cls = statute_class(out) if code == 0 else "other"
    case = case_dict(a.repo, a.head, cls, a.author)
    lint_code, lint_out = run([sys.executable, str(CI / "lint_banked.py"), a.base, a.head], root)
    sorry_code, sorry_out = run([sys.executable, str(CI / "sorry_scan.py"), a.base, a.head], root)
    records = [
        manifest(case, created),
        lint_record(case, a.base, a.head, lint_code, lint_out, created),
        sorry_record(case, a.base, a.head, sorry_code, sorry_out, created),
    ]
    if a.checks:
        records += check_records(case, json.loads(Path(a.checks).read_text(encoding="utf-8")), created)
    out_dir = Path(a.out)
    (out_dir / "evidence").mkdir(parents=True, exist_ok=True)
    (out_dir / "case.json").write_text(json.dumps(case, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    for i, rec in enumerate(records):
        (out_dir / "evidence" / f"{i:03d}-{rec['kind'].replace('.', '-')}.json").write_text(
            json.dumps(rec, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(json.dumps({"class": cls, "records": len(records), "lint": lint_code}))
    return 0


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(prog="trust_shadow")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("gather")
    for name in ("repo", "base", "head", "author", "out"):
        g.add_argument(f"--{name}", required=True)
    g.add_argument("--pr")
    g.add_argument("--checks", help="the commit's check runs as `gh api .../check-runs` saved them (JSON list)")
    g.set_defaults(fn=gather)
    args = ap.parse_args(argv)
    try:
        return args.fn(args)
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(f"trust_shadow: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
