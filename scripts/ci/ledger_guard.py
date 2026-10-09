#!/usr/bin/env python3
"""ledger_guard.py check|activity — the records branches only ever grow (docs/ci-records.md).

  ledger_guard.py check --repo DIR --branch NAME --base SHA --head SHA     every file added, none changed: red if any existing record changed
  ledger_guard.py activity --github OWNER/NAME --branch NAME [--days N]    red if the branch was force-pushed or deleted; other pushers are named

`check` reads git objects only (`warden.audit.ledger_guard` and `warden.scope`, which neutralise repository configuration), over the range
BASE..HEAD of the branch, and then verifies the hash chain of the files at HEAD:

  trust-ledger   ledger.jsonl       append-only (the new bytes are the old bytes plus more) and a valid chain (the juridicator's entry hash, the same as warden's)
  ci-records     runs/**            immutable: a path that existed is never modified, deleted or retyped, in the net diff or in any commit of the range
                 chain/ci-*.ndjson  append-only and a valid chain across the files (`warden.audit.verify_dir`, every record against the closed schema)

HEAD must descend from BASE: a rewritten history is an error, not a pass. A fixed BASE cannot see a rewrite that also moved BASE, so `activity`
asks the platform what happened to the branch (its activity feed records every force-push and deletion, with the pusher) and fails on either.
This is the check that stands in for a ruleset with `non_fast_forward` and `deletion` on these branches (tengoku-warden docs/RUNBOOK.md, item 3)
until the maintainer adds it; the ruleset is what actually prevents, this is what notices.

Credit: Tau Ceti Project, TauCetiCI and TauCetiData, whose archives are called append-only and are not (five commits modify and four delete
existing paths, in their data and our reading of it, 2026-10-09); see tengoku-warden docs/TAU-CETI.md. The code is independent."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import subprocess
import sys
from pathlib import Path

from warden import audit, caps, scope

CHAIN_GLOB = re.compile(r"^chain/ci-\d{4}-\d{2}-\d{2}\.ndjson$")
SHA40 = re.compile(r"^[0-9a-f]{40}$")
BRANCHES = ("trust-ledger", "ci-records")
EXPECTED_PUSHER = "github-actions[bot]"
SCOPE_POLICY = {
    "classes": {"any": {"allow": ["**"], "touch_protected": False}},
    "append_only": ["ledger.jsonl", "chain/*.ndjson"],
    "forbid_delete": ["ledger.jsonl", "chain/**", "runs/**"],
    "max_files": 5000,
    "max_added": 5_000_000,
    "max_deleted": 5_000_000,
    "max_new_file_lines": 5_000_000,
    "allowed_modes": ["100644"],
}


def problems_of_range(repo: str, base: str, head: str) -> list:
    """What a branch's range did to files that already existed."""
    out: list = []
    if base == head:
        return out
    result = scope.check(repo, base, head, scope.Policy.from_dict(SCOPE_POLICY), "any")
    out += [f"{v.code} {v.path or '-'}: {v.detail}" for v in result.violations if v.code != "empty_diff"]
    guard = audit.ledger_guard(repo, base, head, ["runs/**"])
    if not guard.ok:
        out += [f"record_changed {v.path} ({v.status}{' in ' + v.commit[:12] if v.commit else ''})" for v in guard.violations]
        if guard.error:
            out.append(f"guard_error: {guard.error}")
    return out


def problems_of_chain(repo: str, head: str) -> tuple:
    """(problems, summary) for the chain files as `head` has them."""
    files = scope.run_git(repo, ["ls-tree", "-r", "--name-only", "-z", head]).decode("utf-8", "surrogateescape").split("\0")
    problems: list = []
    notes: list = []
    if "ledger.jsonl" in files:
        data = scope.run_git(repo, ["cat-file", "blob", f"{head}:ledger.jsonl"])
        try:
            entries, tip = caps.parse_chain(data)
            notes.append(f"ledger.jsonl: {len(entries)} entries, head {tip}")
        except caps.LedgerError as exc:
            problems.append(f"chain_broken ledger.jsonl: {exc}")
    chain = [f for f in files if CHAIN_GLOB.match(f)]
    if chain:
        import tempfile

        work = Path(tempfile.mkdtemp())
        for f in chain:
            (work / Path(f).name).write_bytes(scope.run_git(repo, ["cat-file", "blob", f"{head}:{f}"]))
        result = audit.verify_dir(str(work), prefix="ci")
        if result.ok:
            notes.append(f"chain/: {result.entries} entries in {len(result.files)} files, head {result.head}")
        else:
            problems += [f"chain_broken chain/: {e}" for e in result.errors]
    return problems, notes


def plain(text: object) -> str:
    return re.sub(r"[^A-Za-z0-9_.@\[\]-]", "?", str(text))[:60]


def judge_activity(events: list, since: dt.datetime) -> tuple:
    """(violations, notices) from the platform's activity feed of one branch. A force-push or a deletion is a violation; a push by anybody but the
    Actions identity is a notice (a maintainer creating the branch is expected; a maintainer editing it is not, and is named)."""
    violations: list = []
    notices: list = []
    for e in events:
        if not isinstance(e, dict):
            continue
        when = e.get("timestamp")
        try:
            at = dt.datetime.strptime(when, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)
        except (TypeError, ValueError):
            violations.append("an activity record without a timestamp")
            continue
        if at < since:
            continue
        kind = e.get("activity_type")
        who = (e.get("actor") or {}).get("login", "?") if isinstance(e.get("actor"), dict) else "?"
        line = f"{plain(kind)} by {plain(who)} at {when}"
        if kind in ("force_push", "branch_deletion"):
            violations.append(line)
        elif kind == "push" and who != EXPECTED_PUSHER:
            notices.append(line)
    return violations, notices


def run_check(a: argparse.Namespace) -> int:
    for label, sha in (("base", a.base), ("head", a.head)):
        if not SHA40.match(sha):
            print(f"ledger_guard: {label} is not a full commit id", file=sys.stderr)
            return 2
    problems = problems_of_range(a.repo, a.base, a.head)
    chain_problems, notes = problems_of_chain(a.repo, a.head)
    problems += chain_problems
    lines = [f"### ledger-guard: {a.branch}", ""] + [f"- {n}" for n in notes]
    lines += (
        [f"- **{p}**" for p in problems]
        if problems
        else [f"- no existing record changed between `{a.base[:12]}` and `{a.head[:12]}`; the chain verifies"]
    )
    print("\n".join(lines))
    return 1 if problems else 0


def run_activity(a: argparse.Namespace) -> int:
    since = dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=a.days)
    done = subprocess.run(
        ["gh", "api", f"repos/{a.github}/activity?ref=refs/heads/{a.branch}&per_page=100"],
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    if done.returncode != 0:
        print(f"ledger_guard: cannot read the activity of {a.branch}: {done.stderr.strip()[:200]}", file=sys.stderr)
        return 2
    violations, notices = judge_activity(json.loads(done.stdout or "[]"), since)
    print(f"### activity of {a.branch}, last {a.days} day(s)")
    for v in violations:
        print(f"- **{v}**")
    for n in notices:
        print(f"- notice: {n}")
    if not violations:
        print("- no force-push and no deletion")
    return 1 if violations else 0


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(prog="ledger_guard")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("--repo", default=".")
    c.add_argument("--branch", required=True, choices=BRANCHES)
    c.add_argument("--base", required=True)
    c.add_argument("--head", required=True)
    c.set_defaults(fn=run_check)
    v = sub.add_parser("activity")
    v.add_argument("--github", required=True)
    v.add_argument("--branch", required=True, choices=BRANCHES)
    v.add_argument("--days", type=int, default=3)
    v.set_defaults(fn=run_activity)
    args = ap.parse_args(argv)
    try:
        return args.fn(args)
    except (ValueError, OSError, scope.GitError, caps.LedgerError, subprocess.SubprocessError) as exc:
        print(f"ledger_guard: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
