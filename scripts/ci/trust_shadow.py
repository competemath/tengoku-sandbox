#!/usr/bin/env python3
"""trust_shadow.py gather — the evidence a PR already has, written in the trust program's shared format (docs/trust-shadow.md).

  trust_shadow.py gather      --repo R --pr N --base SHA --head SHA --author LOGIN --out DIR [--checks FILE]
  trust_shadow.py eligibility --dir DIR --repo R [--app-id N]

Runs main's own gates over the PR read as git objects (never checked out): the banked-content lint (lint_banked.py), the
sorry scan (sorry_scan.py) and the class (classify.py). Reads the commit's check runs from a file (`gh api` output the
workflow saved) and turns each into a record. Writes DIR/case.json and DIR/evidence/*.json, the manifest first. Nothing
here decides anything: the judge (tengoku-juridicator) does, in the next step.

`eligibility` is the third job's half (trust-shadow.yml, `checks: write` only): it takes the validated artifact of `gather` and the judge (case.json,
verdict.json, meta.json), publishes the `merge eligibility` check run on the PR head with `warden.eligibility.build_check_run` (conclusion from the
verdict; the head, merge base, policy digest and evidence digest bound in its external id), and reads it back through `verify_check` pinned to
the App that is meant to make it. ADVISORY: nothing requires the check. Until the judge GitHub App exists the check is made by the Actions identity
(app id 15368). Standard library only, besides the vendored warden modules (scripts/ci/warden/)."""

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
from warden import eligibility as merge_eligibility

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
OUR_CHECKS = ("trust-shadow", "trust-ledger", "trust-label", merge_eligibility.CHECK_NAME)
ACTIONS_APP_ID = 15368  # the GitHub Actions app: who makes the check run until the judge has an App of its own
DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")
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
    # what the `merge eligibility` check binds besides the case: the PR and the merge base the verdict was reached on
    if a.pr and a.pr.isdigit() and int(a.pr) > 0:
        mb_code, mb_out = run(["git", "merge-base", a.base, a.head], root)
        if mb_code == 0 and SHA.match(mb_out.strip()):
            meta = {"pr": int(a.pr), "base": a.base, "merge_base": mb_out.strip()}
            (out_dir / "meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    for i, rec in enumerate(records):
        (out_dir / "evidence" / f"{i:03d}-{rec['kind'].replace('.', '-')}.json").write_text(
            json.dumps(rec, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(json.dumps({"class": cls, "records": len(records), "lint": lint_code}))
    return 0


def validate_meta(meta: object) -> dict:
    if not isinstance(meta, dict) or set(meta) != {"pr", "base", "merge_base"}:
        raise ValueError("meta.json is not {pr, base, merge_base}")
    if isinstance(meta["pr"], bool) or not isinstance(meta["pr"], int) or meta["pr"] <= 0:
        raise ValueError("meta.json: pr is not a positive integer")
    for k in ("base", "merge_base"):
        if not isinstance(meta[k], str) or not SHA.match(meta[k]):
            raise ValueError(f"meta.json: {k} is not a commit")
    return meta


def validate_verdict(verdict: object, case: object, repo: str) -> tuple:
    """The verdict and case the check is built from, checked again here: they come from an artifact, whatever job made it."""
    if (
        not isinstance(verdict, dict)
        or verdict.get("schema") != "tengoku-verdict/1"
        or verdict.get("decision") not in merge_eligibility.DECISIONS
    ):
        raise ValueError("not a verdict")
    for k in ("evidence_digest", "policy_sha256"):
        if not isinstance(verdict.get(k), str) or not DIGEST.match(verdict[k]):
            raise ValueError(f"the verdict has no {k}")
    if not isinstance(case, dict) or case.get("repo") != repo or not SHA.match(str(case.get("head_sha"))):
        raise ValueError("the case is not for this repository and a commit")
    if (verdict.get("case") or {}).get("head_sha") != case["head_sha"]:
        raise ValueError("the verdict and the case name different commits")
    if len(json.dumps(verdict)) > 60_000:
        raise ValueError("verdict too large")
    return verdict, case


def parse_pages(text: str) -> list:
    """The check runs of `gh api --paginate .../check-runs`, which prints one JSON object per page."""
    runs, dec, i = [], json.JSONDecoder(), 0
    while i < len(text):
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text):
            break
        page, i = dec.raw_decode(text, i)
        if isinstance(page, dict) and isinstance(page.get("check_runs"), list):
            runs += page["check_runs"]
    return runs


def gh(*args: str, payload: dict | None = None) -> tuple[int, str]:
    done = subprocess.run(
        ["gh", "api", *args], input=json.dumps(payload) if payload else None, capture_output=True, text=True, check=False, timeout=TIMEOUT
    )
    return done.returncode, done.stdout if done.returncode == 0 else done.stderr


def eligibility(a: argparse.Namespace) -> int:
    d = Path(a.dir)
    verdict, case = validate_verdict(
        json.loads((d / "verdict.json").read_text(encoding="utf-8")), json.loads((d / "case.json").read_text(encoding="utf-8")), a.repo
    )
    meta = validate_meta(json.loads((d / "meta.json").read_text(encoding="utf-8")))
    body = merge_eligibility.build_check_run(verdict, case, meta["merge_base"], meta["pr"])
    rc, out = gh("-X", "POST", f"repos/{a.repo}/check-runs", "--input", "-", payload=body)
    if rc != 0:
        print(f"trust_shadow: the check run was not created: {out.strip()[:300]}", file=sys.stderr)
        return 1
    # read it back the way the merge side will: only a completed check from the expected App, for this head, with the live merge base, counts
    rc, out = gh("--paginate", f"repos/{a.repo}/commits/{case['head_sha']}/check-runs?filter=all&per_page=100")
    admission = merge_eligibility.verify_check(
        parse_pages(out) if rc == 0 else [],
        expected_app_id=a.app_id,
        repo=a.repo,
        pr=meta["pr"],
        live_head=case["head_sha"],
        live_merge_base=meta["merge_base"],
    )
    print(json.dumps({"published": body["conclusion"], "decision": verdict["decision"], "admission": admission.to_json()}, sort_keys=True))
    if (
        admission.decision == "wait"
        and admission.reasons
        and admission.reasons[0] in ("no_eligibility_check", "external_id_malformed", "stale_head")
    ):
        print(
            f"::error::the check run was created but not read back as app {a.app_id}'s `{merge_eligibility.CHECK_NAME}` for this head",
            file=sys.stderr,
        )
        return 1
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
    e = sub.add_parser("eligibility")
    e.add_argument("--dir", required=True)
    e.add_argument("--repo", required=True)
    e.add_argument("--app-id", type=int, default=ACTIONS_APP_ID, help="the App that is meant to make the check (default: GitHub Actions)")
    e.set_defaults(fn=eligibility)
    args = ap.parse_args(argv)
    try:
        return args.fn(args)
    except (ValueError, OSError, KeyError, subprocess.TimeoutExpired) as exc:
        print(f"trust_shadow: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
