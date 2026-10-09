#!/usr/bin/env python3
"""ruleset_drift.py snapshot|check — the repository's rulesets are the ones that were reviewed (docs/ci-records.md, "Ruleset drift").

  ruleset_drift.py snapshot --repo OWNER/NAME [--dir .github/rulesets] [--with-bypass]    write the live rulesets, normalised, one file each
  ruleset_drift.py check    --repo OWNER/NAME [--dir .github/rulesets]                    compare the live rulesets with the committed ones, and assert the invariants

A ruleset is what actually enforces: a required check, a merge queue, no force-push, no deletion. Changing one in the settings leaves no diff in the
repository, so a loosened rule is invisible until something merges that should not have. `snapshot` writes each live ruleset as a file with the
volatile fields dropped (ids, timestamps, links) and every list sorted; `check` fetches the live ones the same way and fails with a readable diff on
any difference, a ruleset that is missing, and one that is new. It also asserts what Tau Ceti's Roadmap `auto-merge.yml` asserts of the rules in force
on the default branch (a pull-request rule with required approvals, or the merge queue; required status checks; `non_fast_forward` and `deletion`)
and WARNS about every required check with no `integration_id`: such a check can be set by any identity with write access.

Bypass actors are not visible to a token without administration rights, which is every token a workflow has: the live view then has no
`bypass_actors` and they are NOT compared (the report says so). A snapshot taken with `--with-bypass` by an administrator records them, and a check
run with an administrator's token compares them. Until then the list of who may bypass is something only a person looking at the settings can see.

Credit: Tau Ceti Project, the ruleset snapshots of TauCetiCI (A5; its snapshot noise of 2026-09-28, commit f2777b1, from timezone and ordering)
and the rule-drift assertion of TauCetiRoadmap's auto-merge.yml (Roadmap PR 235, 2026-08-16: a PR targeted an unprotected branch and
`gh pr merge --auto` merged it 11 seconds after it was created, with no review and no build); see tengoku-warden docs/TAU-CETI.md. Independent code."""

from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = re.compile(r"^[A-Za-z0-9_.-]{1,100}/[A-Za-z0-9_.-]{1,100}$")
VOLATILE = {"id", "node_id", "_links", "created_at", "updated_at", "source", "source_type", "current_user_can_bypass", "ruleset_id"}
DEFAULT_DIR = ".github/rulesets"
API = "https://api.github.com/"


class ApiError(Exception):
    pass


def gh_json(path: str):
    done = subprocess.run(["gh", "api", path], capture_output=True, text=True, check=False, timeout=120)
    if done.returncode != 0:
        raise ApiError(f"GET {path}: {done.stderr.strip()[:200]}")
    return json.loads(done.stdout)


def canonical(value):
    """Keys sorted, every list sorted by its members' canonical JSON: the API returns lists in no promised order."""
    if isinstance(value, dict):
        return {k: canonical(v) for k, v in sorted(value.items())}
    if isinstance(value, list):
        # rules by their type first, so that a snapshot reads in the order of the settings page
        return sorted(
            (canonical(v) for v in value),
            key=lambda v: (str(v.get("type", "")) if isinstance(v, dict) else "", json.dumps(v, sort_keys=True)),
        )
    return value


def normalise(ruleset: dict, bypass: bool) -> dict:
    """The part of a ruleset that is a decision: not ids, timestamps or links. `bypass_actors` only when the caller asks and the view has them."""
    keep = {k: v for k, v in ruleset.items() if k not in VOLATILE and (bypass or k != "bypass_actors")}
    return canonical(keep)


def slug(name: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-") or "ruleset"


def render(doc: dict) -> str:
    return json.dumps(doc, indent=2, sort_keys=True) + "\n"


def fetch_live(repo: str, get=None) -> list:
    """Every ruleset that applies to the repository, in full (the list has summaries only)."""
    get = get or gh_json
    out = []
    for summary in get(f"repos/{repo}/rulesets"):
        href = ((summary.get("_links") or {}).get("self") or {}).get("href", "")
        path = href[len(API) :] if href.startswith(API) else f"repos/{repo}/rulesets/{summary['id']}"
        out.append(get(path))
    return out


def load_snapshots(directory: Path) -> dict:
    out = {}
    for f in sorted(directory.glob("*.json")):
        doc = json.loads(f.read_text(encoding="utf-8"))
        out[doc["name"]] = (f.name, doc)
    return out


def compare(live: list, snapshots: dict) -> tuple:
    """(drift as readable lines, notices). `snapshots` is {name: (file name, normalised ruleset)}."""
    drift, notices = [], []
    seen = set()
    for rs in live:
        name = rs["name"]
        seen.add(name)
        view = normalise(rs, bypass=True)
        if name not in snapshots:
            drift.append(f"a ruleset that is not committed: {name!r} (enforcement {rs.get('enforcement')})")
            continue
        fname, snap = snapshots[name]
        if "bypass_actors" not in view and "bypass_actors" in snap:
            snap = {k: v for k, v in snap.items() if k != "bypass_actors"}
            notices.append(f"{name!r}: bypass actors are not visible to this token, so they are not compared")
        elif "bypass_actors" in view and "bypass_actors" not in snap:
            view = {k: v for k, v in view.items() if k != "bypass_actors"}
        if view != snap:
            diff = difflib.unified_diff(
                render(snap).splitlines(), render(view).splitlines(), f"committed/{fname}", f"live/{name}", lineterm="", n=2
            )
            drift.append(f"ruleset {name!r} differs from {fname}:\n" + "\n".join(diff))
    for name, (fname, _doc) in snapshots.items():
        if name not in seen:
            drift.append(f"{fname} is committed but no live ruleset is named {name!r}: it was deleted or renamed")
    return drift, notices


def invariants(rules: list) -> tuple:
    """(failures, warnings) for the rules in force on the default branch (`GET /repos/{repo}/rules/branches/{branch}`)."""
    by_type: dict = {}
    for r in rules:
        by_type.setdefault(r.get("type"), []).append(r)
    failures, warnings = [], []
    reviews = any(
        isinstance(r.get("parameters"), dict) and r["parameters"].get("required_approving_review_count", 0) >= 1
        for r in by_type.get("pull_request", [])
    )
    if not (reviews or by_type.get("merge_queue")):
        failures.append("no pull-request rule with required approvals and no merge queue applies to the default branch")
    checks = [c for r in by_type.get("required_status_checks", []) for c in (r.get("parameters") or {}).get("required_status_checks", [])]
    if not checks:
        failures.append("no required status check applies to the default branch")
    for kind in ("non_fast_forward", "deletion"):
        if not by_type.get(kind):
            failures.append(f"the default branch has no `{kind}` rule")
    for c in checks:
        if not c.get("integration_id"):
            warnings.append(
                f"required check `{c.get('context')}` has no integration_id: any identity with write access can set it (tengoku-warden docs/RUNBOOK.md, item 2)"
            )
    return failures, warnings


def run_snapshot(a: argparse.Namespace) -> int:
    live = fetch_live(a.repo)
    out = Path(a.dir)
    out.mkdir(parents=True, exist_ok=True)
    for rs in live:
        doc = normalise(rs, a.with_bypass)
        (out / f"{slug(rs['name'])}.json").write_text(render(doc), encoding="utf-8")
        print(f"wrote {slug(rs['name'])}.json ({'with' if 'bypass_actors' in doc else 'without'} bypass actors)")
    return 0


def run_check(a: argparse.Namespace) -> int:
    live = fetch_live(a.repo)
    directory = Path(a.dir)
    if not directory.is_dir():
        print(f"ruleset_drift: {a.dir} has no committed rulesets; run `snapshot` first", file=sys.stderr)
        return 2
    drift, notices = compare(live, load_snapshots(directory))
    default = gh_json(f"repos/{a.repo}")["default_branch"]
    failures, warnings = invariants(gh_json(f"repos/{a.repo}/rules/branches/{default}"))
    lines = [f"### ruleset drift: {a.repo}", ""]
    lines += [f"- **drift** {d}" for d in drift] + [f"- **invariant** {f}" for f in failures]
    lines += [f"- warning: {w}" for w in warnings] + [f"- notice: {n}" for n in notices]
    if not (drift or failures):
        lines.append(f"- the {len(live)} live ruleset(s) are the committed ones, and the invariants hold on `{default}`")
    print("\n".join(lines))
    return 1 if drift or failures else 0


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(prog="ruleset_drift")
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, fn in (("snapshot", run_snapshot), ("check", run_check)):
        p = sub.add_parser(name)
        p.add_argument("--repo", required=True)
        p.add_argument("--dir", default=DEFAULT_DIR)
        if name == "snapshot":
            p.add_argument("--with-bypass", action="store_true", help="record the bypass actors (visible to administrators only)")
        p.set_defaults(fn=fn)
    args = ap.parse_args(argv)
    if not REPO.match(args.repo):
        print("ruleset_drift: the repository is not owner/name", file=sys.stderr)
        return 2
    try:
        return args.fn(args)
    except (ApiError, ValueError, KeyError, OSError, subprocess.SubprocessError) as exc:
        print(f"ruleset_drift: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
