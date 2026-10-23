#!/usr/bin/env python3
"""studied_approval.py <data.json> — who may approve a STUDIED PR.

A studied PR (scripts/ci/studied_check.py) is approved by ONE CODE OWNER, or by TWO INDEPENDENT CONTRIBUTORS WITH WRITE ACCESS. GitHub's ruleset can
say "one code owner" or "two approvals" but not "either", so the PR gate asks this. The workflow gathers the facts with the API (the token never
leaves the step) and writes them to a JSON file; this script only decides, so it is tested without a network:

  {"author": "tengoku-supervisor[bot]", "head": "<sha>", "owners": ["a", "b"],
   "committers": ["..."], "permissions": {"user": "write"},
   "reviews": [{"user": "x", "state": "APPROVED", "commit_id": "<sha>", "type": "User"}, ...]}   (oldest first)

Rules. A review counts only if it is on the current head (an approval of an older commit is stale). A user's latest APPROVED / CHANGES_REQUESTED /
DISMISSED decides where they stand (a later comment changes nothing). Anyone's outstanding request for changes blocks. The author, the App and anyone who
committed to the PR never count. Path 1: a code owner approves. Path 2: two distinct approvers who are not code owners, each with write, maintain or
admin permission (the maintainer's own accounts are code owners, so they take path 1 and never pad path 2: two accounts of one person are not two
independent contributors).
"""

from __future__ import annotations

import json
import sys

WRITE = {"write", "maintain", "admin"}


def standing(reviews: list[dict], head: str) -> dict[str, str]:
    """user -> APPROVED | CHANGES_REQUESTED, for the users whose latest deciding review stands on `head` (changes requested stands on any commit)."""
    out: dict[str, str] = {}
    for r in reviews:
        u, st = r.get("user"), r.get("state")
        if not u or st not in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            continue  # a comment, or a review not submitted yet, changes nothing
        if st == "DISMISSED":
            out.pop(u, None)
        elif st == "APPROVED" and r.get("commit_id") != head:
            out.pop(u, None)  # approved an older commit: that is not an approval of this one
        else:
            out[u] = st
    return out


def decide(data: dict) -> tuple[bool, str]:
    head = data.get("head")
    author = data.get("author", "")
    owners = set(data.get("owners") or [])
    out_of_play = {author, *(data.get("committers") or [])}
    perms = data.get("permissions") or {}
    types = {r.get("user"): r.get("type") for r in data.get("reviews") or []}
    st = standing(data.get("reviews") or [], head)
    blockers = sorted(u for u, s in st.items() if s == "CHANGES_REQUESTED" and u != author)
    if blockers:
        return False, f"changes are requested by {', '.join(blockers)}"

    def counts(u: str) -> bool:
        return u not in out_of_play and types.get(u) != "Bot" and not u.endswith("[bot]")

    approvers = sorted(u for u, s in st.items() if s == "APPROVED" and counts(u))
    owner_ok = [u for u in approvers if u in owners]
    if owner_ok:
        return True, f"approved by a code owner ({owner_ok[0]})"
    others = [u for u in approvers if u not in owners and perms.get(u) in WRITE]
    if len(others) >= 2:
        return True, f"approved by two independent contributors with write access ({', '.join(others[:2])})"
    have = ", ".join(f"{u} ({'code owner' if u in owners else perms.get(u) or 'no write access'})" for u in approvers) or "no approval yet"
    return False, f"needs one code owner's approval, or two approvals from independent contributors with write access (have: {have})"


def main() -> None:
    if len(sys.argv) != 2:
        print("usage: studied_approval.py <data.json>", file=sys.stderr)
        sys.exit(2)
    ok, why = decide(json.loads(open(sys.argv[1], encoding="utf-8").read()))
    print(("approval ok: " if ok else "::error::approval missing: ") + why)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
