#!/usr/bin/env python3
"""fossa_check.py <owner/repo> <sha> — FOSSA's three verdicts on the PR's head commit must all be `success`.

FOSSA (a GitHub App) scans every PR head and reports three commit statuses: License Compliance (licence policy),
Dependency Quality (quality policy) and Security Analysis (known vulnerabilities in the dependencies). It reports on PR commits
only, never on a merge-queue entry, so none of them can be a check of the ruleset itself (a queue entry would wait for a status
that never comes: the reason `pr-gate` exists). This job reads them on the PR instead, and `pr-gate` depends on it.

A verdict that is not there yet is waited for (FOSSA takes a few minutes), up to FOSSA_WAIT_MINUTES; a verdict of `error` or
`failure` fails at once, and so does a verdict that never arrived: a gate that passes when FOSSA is silent is not a gate.
What FOSSA says is quoted, bounded and without a link unless the link is FOSSA's own.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time

from _git import fail

CONTEXTS = ("License Compliance", "Dependency Quality", "Security Analysis")
BAD = ("error", "failure")
REPO = re.compile(r"[A-Za-z0-9-]+/(?!\.{1,2}$)[\w.-]+")  # owner/name; a name of only dots would climb out of repos/<owner>/ in the API path
SHA = re.compile(r"[0-9a-f]{40}")
FOSSA_URL = "https://app.fossa.com/"


def judge(statuses: list[dict]) -> tuple[str, list[str]]:
    """The verdict on a list of commit statuses (the latest per context): "bad" when a context failed, "ok" when all three
    succeeded, "wait" otherwise; and one bounded line per context."""
    seen = {s.get("context"): s for s in statuses}  # only the three contexts below are looked up: other apps' statuses never count
    lines, states = [], []
    for ctx in CONTEXTS:
        s = seen.get(ctx)
        state = str(s.get("state")) if s else "not reported yet"
        states.append(state)
        line = f"{ctx}: {state}"
        if s and s.get("description"):
            line += f" ({str(s['description'])[:80]})"
        url = str(s.get("target_url") or "") if s else ""
        if state in BAD and url.startswith(FOSSA_URL):
            line += f" {url[:300]}"
        lines.append(line)
    if any(st in BAD for st in states):
        return "bad", lines
    return ("ok" if all(st == "success" for st in states) else "wait"), lines


def fetch(repo: str, sha: str) -> list[dict]:
    r = subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/{sha}/status?per_page=100", "--jq", ".statuses"], capture_output=True, text=True
    )
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:200] or "gh api failed")
    return json.loads(r.stdout or "[]")


def wait_for_verdict(repo, sha, minutes, *, fetch=fetch, sleep=time.sleep, clock=time.monotonic, interval=20):
    """Poll until the verdict is final or the time is up; returns (verdict, lines). "wait" is returned only after the time is up."""
    deadline = clock() + minutes * 60
    lines: list[str] = []
    while True:
        try:
            verdict, lines = judge(fetch(repo, sha))
        except (RuntimeError, ValueError) as e:  # a lookup that failed is asked again until the time is up
            verdict, lines = "wait", [f"could not read the statuses: {str(e)[:200]}"]
        if verdict != "wait" or clock() >= deadline:
            return verdict, lines
        sleep(interval)


def main(argv: list[str]) -> None:
    if len(argv) != 2 or not REPO.fullmatch(argv[0]) or not SHA.fullmatch(argv[1]):
        fail("usage: fossa_check.py <owner/repo> <40-hex sha>")
    minutes = float(os.environ.get("FOSSA_WAIT_MINUTES", "15"))
    verdict, lines = wait_for_verdict(argv[0], argv[1], minutes)
    if verdict == "bad":
        fail("FOSSA found problems in this PR's commit:\n" + "\n".join(lines))
    if verdict == "wait":
        fail(
            f"FOSSA did not report all three verdicts within {minutes:g} minutes (a missing verdict is not a pass); push again or re-run the gate:\n"
            + "\n".join(lines)
        )
    print("\n".join(lines) + "\nFOSSA: all three verdicts are success")


if __name__ == "__main__":
    main(sys.argv[1:])
