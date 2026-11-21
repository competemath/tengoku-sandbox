#!/usr/bin/env python3
"""campaign_check.py: a CI-class change comes with a campaign, or with a waiver only the approver account can give.

Run by .github/workflows/campaign-gate.yml (pull_request_target: the base branch's copy of this script, so a pull request cannot weaken its own gate; nothing of the PR is checked out or run).
Environment: PR (number), REPO, SHA (the PR's head commit), GH_TOKEN. The approver is the constant APPROVER below.

  1. The PR's changed files are read from the API. scripts/ci/ci_paths.py says which are CI-class: none -> this check passes at once.
  2. A CI-class change needs ONE of:
     - a campaign for SHA: not available yet. The sandbox (competemath/tengoku-sandbox) has no workflow that runs the scenario campaign for a commit and attests the result, as
       competemath/emissary-sandbox's campaign.yml does for emissary (campaign-gate.yml there). Until it exists, the second way is the only one;
     - a WAIVER: a review of the PR (approved or commented, not dismissed or requesting changes), on this very commit, by APPROVER, with a line `campaign-waiver: <reason of at least 20 characters>`. The agent that opens these PRs works as
       the maintainer's main account and cannot act as the approver, which is why a label or a comment of the author would not bind it. A push after the waiver voids it (the review is
       on the old commit), like any approval.
Exit 0: not CI-class, or waived. Exit 1: CI-class and neither.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ci_paths

# The account whose review can waive the campaign. A constant of this file on purpose: a repository variable could be edited by any admin, with no pull request to see it,
# and the waiver may be a COMMENT review, which an author can write on their own PR. Changing it is a CI-class change like any other.
APPROVER = "mikael-bashir"  # SANDBOX: the account that can write a review here
ACCEPTED_STATES = {"APPROVED", "COMMENTED"}  # not CHANGES_REQUESTED, and a DISMISSED review keeps its body in the API but no longer counts
MIN_REASON = 20
# no lazy quantifier in front of a trailing-space class (it backtracks, super-linear on a crafted body): the reason is taken whole and stripped
WAIVER = re.compile(r"^[ \t]*campaign-waiver:[ \t]*(?P<reason>\S.*)$", re.MULTILINE | re.IGNORECASE)


def waiver(reviews: list[dict], approver: str, sha: str) -> tuple[str | None, list[str]]:
    """(reason, problems): the newest acceptable waiver, and what was wrong with the others (so a refusal can say why)"""
    problems: list[str] = []
    for r in sorted(reviews, key=lambda r: r.get("submitted_at") or "", reverse=True):
        m = WAIVER.search(r.get("body") or "")
        if not m or r.get("state") not in ACCEPTED_STATES:
            continue
        who = ((r.get("user") or {}).get("login") or "").lower()
        if who != approver.lower():
            problems.append(f"a waiver by {who or 'nobody'}, not by {approver}")
        elif r.get("commit_id") != sha:
            problems.append(f"a waiver on commit {(r.get('commit_id') or '?')[:8]}, not on the head {sha[:8]} (a push voids it)")
        elif len(m.group("reason").strip()) < MIN_REASON:
            problems.append(f"a waiver whose reason is under {MIN_REASON} characters")
        else:
            return m.group("reason").strip(), problems
    return None, problems


def gh_list(path: str) -> list[dict]:
    """every element of a paginated list endpoint (`--jq '.[]'` prints one compact JSON object per line, whatever the page count)"""
    out = subprocess.run(["gh", "api", path, "--paginate", "--jq", ".[]"], capture_output=True, text=True, check=True).stdout
    return [json.loads(line) for line in out.splitlines() if line.strip()]


def tree_files(root: Path) -> dict[str, str]:
    """the workflows and scripts of the checkout (the BASE branch on pull_request_target), as {repository path: text}"""
    files: dict[str, str] = {}
    for sub in (".github/workflows", "scripts"):
        for p in (root / sub).rglob("*"):
            rel = p.relative_to(
                root
            ).as_posix()  # the test is on the path inside the checkout: a checkout that itself sits under a folder named tests must not lose every file
            if p.is_file() and p.suffix in {".py", ".sh", ".mjs", ".yml", ".yaml"} and "/tests/" not in "/" + rel:
                files[rel] = p.read_text(errors="replace")
    return files


def verdict(changed: list[str], files: dict[str, str], reviews: list[dict], approver: str, sha: str) -> tuple[bool, str]:
    ci = ci_paths.ci_files(changed, files)
    if not ci:
        return True, "not a CI-class change: no campaign needed"
    listing = "; ".join(f"{p} ({why})" for p, why in sorted(ci.items())[:8]) + (" …" if len(ci) > 8 else "")
    reason, problems = waiver(reviews, approver, sha)
    if reason:
        return True, f"CI-class change, waived by {approver}: {reason}\n  {listing}"
    why = ("; refused: " + "; ".join(problems)) if problems else ""
    return False, (
        f"a CI-class change needs a sandbox campaign for {sha[:8]} or a waiver by {approver}{why}.\n"
        f"  CI-class files: {listing}\n"
        f"  A campaign for a commit is not available for this repository yet; the waiver is a review of this PR on this commit with a line `campaign-waiver: <reason>` (docs/campaign-gate.md)."
    )


def main() -> int:
    pr, repo, sha = os.environ["PR"], os.environ["REPO"], os.environ["SHA"]
    # a rename out of a CI-class path changes that path too
    changed = [n for f in gh_list(f"repos/{repo}/pulls/{pr}/files") for n in (f["filename"], f.get("previous_filename")) if n]
    reviews = gh_list(f"repos/{repo}/pulls/{pr}/reviews")
    root = Path(os.environ.get("TENGOKU_CI_ROOT") or Path(__file__).resolve().parents[2])
    ok, message = verdict(changed, tree_files(root), reviews, APPROVER, sha)
    print(message)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
