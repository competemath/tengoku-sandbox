#!/usr/bin/env python3
"""promotion_notify.py <before> <after> — tell each contributor their theorems are trusted.

A push to main can carry several promotions (a merge-queue group). For every commit on main's first-parent line in
<before>..<after> that touches data/trusted/, this collects the records it made trusted, the staging file each one
left, and the pull request that added that record (its squash commit names it: "... (#N)"). Then it comments ONCE
on each contributor PR with every record of it now trusted, across the whole push. Records in a shared flat staging
file are attributed by reading that file's history as JSON (any spelling of the record). Exits non-zero if a
comment could not be posted, after trying every PR."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys

from _git import added_lines, changed_files, match, removed_lines, run

MAX_NAMES = 25
PR_RE = re.compile(r"\(#(\d+)\)\s*$")
SKIP_KINDS = ("tombstone", "tombstone_note", "credit_correction")


def record_names(lines) -> list[str]:
    out = []
    for text in lines:
        if not text.strip():
            continue
        try:
            r = json.loads(text)
        except ValueError:
            continue
        if isinstance(r, dict) and "name" in r and not any(k in r for k in SKIP_KINDS):
            out.append(str(r["name"]))
    return out


def per_pr_file_pr(path: str, before: str) -> str | None:
    """data/staging/<library>/<file>.jsonl: the PR whose commit added the file."""
    subjects = run("log", "--first-parent", "--diff-filter=A", "--format=%s", before, "--", path, check=False)
    found = [m.group(1) for m in (PR_RE.search(s) for s in subjects.splitlines()) if m]
    return found[-1] if found else None  # the oldest


# keyed by revision too: within one push a later promotion can take a record that an earlier commit of the same push
# added to the same file, which the history as of the earlier promotion does not show
_FLAT: dict[tuple[str, str], dict[str, str]] = {}


def flat_file_prs(path: str, before: str) -> dict[str, str]:
    """name -> the PR that first added it to a shared flat staging file, read from the file's history as JSON."""
    if (path, before) in _FLAT:
        return _FLAT[(path, before)]
    out: dict[str, str] = {}
    log = run("log", "--first-parent", "--reverse", "-p", "-U0", "--format=%x00%s", before, "--", path, check=False)
    pr = None
    for line in log.splitlines():
        if line.startswith("\x00"):
            m = PR_RE.search(line)
            pr = m.group(1) if m else None
        elif line.startswith("+") and not line.startswith("+++") and pr:
            for n in record_names([line[1:]]):
                out.setdefault(n, pr)
    _FLAT[(path, before)] = out
    return out


def main() -> None:
    before, after = sys.argv[1], sys.argv[2]
    commits = run("rev-list", "--reverse", "--first-parent", f"{before}..{after}", "--", "data/trusted", check=False).split()
    by_pr: dict[str, list[str]] = {}
    promotions: dict[str, set[str]] = {}
    unknown = 0
    for c in commits:
        subject = run("log", "-1", "--format=%s", c)
        m = PR_RE.search(subject)
        promotion = m.group(1) if m else None
        trusted: list[str] = []
        left: dict[str, str] = {}
        for _, p in changed_files(f"{c}^", c):
            if match(p, ["data/trusted/*.jsonl"]):
                trusted += record_names(t for _, t in added_lines(f"{c}^", c, p))
            elif match(p, ["data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
                for n in record_names(t for _, t in removed_lines(f"{c}^", c, p)):
                    left.setdefault(n, p)
        for n in trusted:
            path = left.get(n)
            pr = None
            if path:
                pr = per_pr_file_pr(path, f"{c}^") if path.count("/") == 3 else flat_file_prs(path, f"{c}^").get(n)
            if pr and pr != promotion:
                by_pr.setdefault(pr, []).append(n)
                if promotion:
                    promotions.setdefault(pr, set()).add(promotion)
            else:
                unknown += 1
    if not by_pr:
        print(f"no contributor PR to tell ({len(commits)} promotion commits, {unknown} records without a PR found)")
        return
    failed = []
    for pr, ns in sorted(by_pr.items(), key=lambda kv: int(kv[0])):
        ns = sorted(set(ns))
        shown = ", ".join(f"`{n}`" for n in ns[:MAX_NAMES]) + (f" and {len(ns) - MAX_NAMES} more" if len(ns) > MAX_NAMES else "")
        via = ", ".join(f"#{x}" for x in sorted(promotions.get(pr, ()), key=int))
        body = (
            f"**{len(ns)} of the records this PR added {'is' if len(ns) == 1 else 'are'} now trusted**"
            + (f" (promotion {via})" if via else "")
            + f": {shown}.\n\nTrusted means the whole tree builds with them on the pinned toolchain, with no `sorry` and only the "
            "standard axioms; their source and credit travel with them. Search them at https://competemath.com/tengoku."
        )
        if os.environ.get("TENGOKU_COMMENT_DRY"):
            print(f"would comment on #{pr}:\n{body}\n")
            continue
        r = subprocess.run(["gh", "pr", "comment", pr, "--body", body], check=False, capture_output=True, text=True)
        if r.returncode != 0:
            failed.append(pr)
            print(f"#{pr}: could not comment: {r.stderr.strip()[:200]}")
        else:
            print(f"#{pr}: {len(ns)} trusted")
    if unknown:
        print(f"{unknown} promoted records without a PR found (added by a direct push)")
    if failed:
        sys.exit(f"could not tell {', '.join('#' + p for p in failed)}")


if __name__ == "__main__":
    main()
