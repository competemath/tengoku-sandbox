#!/usr/bin/env python3
"""cache_fresh.py <base> [--limit N] [--wait MINUTES] — does the newest published cache match the base this merge group is built on?

The merge queue seeds its build from the newest published cache (plus the newest promoted top-up) and compiles the difference. When a change that touches
many modules has merged and its cache build has not published yet, that difference is most of the tree: a group builds for hours against a 40-minute check
limit, is ejected for it, and takes runners away from the very build it is waiting for. This counts the Lean modules that differ between what the cache is
for and the base, and only lets the group on when there are few enough. If not, it waits (up to --wait minutes) while a cache build is running and the pointer
may move; with no build running, or when the time is up, it fails with a message that says what happened.

Found on 2026-10-05: the seed moved into Tengoku/Seed/ (every module renamed), five approved intake PRs were queued before the rebuild published, and each would
have recompiled the seed from scratch.

    cache_fresh.py <base> [--limit 1000] [--wait 25]

Environment: GITHUB_REPOSITORY / TENGOKU_CACHE_SOURCE (where the pointer is), TENGOKU_STALE_LIMIT (the limit), GH_TOKEN (to see running builds);
for tests TENGOKU_CACHE_POINTER_FILES (JSON files read one per look instead of the pointer), TENGOKU_BUILDS_RUNNING (0/1), TENGOKU_POLL_SECONDS.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
import urllib.request

from _git import changed_files, fail, run

DEFAULT_LIMIT = 1000  # modules: the whole tree builds at about one a second on a runner, the queue's budget for a group is about 20 minutes
POINTER = "https://github.com/{repo}/releases/download/cache-latest/cache-latest.json"


def pointer(look: int) -> dict | None:
    """The cache-latest pointer (the newest cache and the promoted top-up), or None when it cannot be read."""
    files = os.environ.get("TENGOKU_CACHE_POINTER_FILES")
    try:
        if files:
            names = files.split(":")
            with open(names[min(look, len(names) - 1)], encoding="utf-8") as f:
                return json.load(f)
        repo = os.environ.get("TENGOKU_CACHE_SOURCE") or os.environ.get("GITHUB_REPOSITORY") or "competemath/tengoku"
        with urllib.request.urlopen(POINTER.format(repo=repo) + f"?t={int(time.time())}", timeout=30) as r:  # noqa: S310 (an https URL built above)
            return json.load(r)
    except Exception as e:
        print(f"warning: could not read the cache pointer ({e}); not judging", file=sys.stderr)
        return None


def sha(value: object) -> str | None:
    """A full commit id in canonical form, or None. The cache pointer is read from the network, so a commit from it reaches git only as a number's digits: a
    value that is not 40 hex digits (an option such as `--upload-pack=…` included) never becomes an argument."""
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", value):
        return None
    return format(int(value, 16), "040x")


def is_ancestor(a: str, b: str) -> bool:
    first, second = sha(a), sha(b)
    if first is None or second is None:
        return False
    return subprocess.run(["git", "merge-base", "--is-ancestor", first, second], capture_output=True, check=False).returncode == 0


def have(commit: str) -> bool:
    wanted = sha(commit)
    if wanted is None:
        return False
    if subprocess.run(["git", "cat-file", "-e", f"{wanted}^{{commit}}"], capture_output=True, check=False).returncode == 0:
        return True
    subprocess.run(["git", "fetch", "-q", "--no-tags", "--filter=blob:none", "origin", wanted], capture_output=True, check=False)
    return subprocess.run(["git", "cat-file", "-e", f"{wanted}^{{commit}}"], capture_output=True, check=False).returncode == 0


def reference(p: dict, base: str) -> str | None:
    """The commit the seeded tree will be for: the promoted top-up when it continues the newest cache and belongs to the base's history, else the cache.
    None when the cache is not in the base's history (cache.sh picks an older one then: nothing to judge here)."""
    cache = p.get("commit")
    if not cache or not have(cache) or not is_ancestor(cache, base):
        return None
    top = (p.get("topup") or {}).get("commit")
    if top and have(top) and is_ancestor(cache, top) and is_ancestor(top, base):
        return top
    return cache


def modules_behind(ref: str, base: str) -> int:
    """Lean modules the base has that the reference does not (added or changed; a removed module costs nothing to build; a rename is an addition)."""
    n = 0
    for status, path in changed_files(ref, base):
        if status != "D" and path.endswith(".lean") and (path == "Tengoku.lean" or path.startswith("Tengoku/")):
            n += 1
    return n


def builds_running() -> bool:
    forced = os.environ.get("TENGOKU_BUILDS_RUNNING")
    if forced is not None:
        return forced == "1"
    for status in ("in_progress", "queued"):
        r = subprocess.run(
            ["gh", "run", "list", "--workflow", "build.yml", "--status", status, "--json", "databaseId", "-q", "length"],
            capture_output=True,
            text=True,
            check=False,
        )
        if r.stdout.strip() not in ("", "0"):
            return True
    return False


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--limit", type=int, default=int(os.environ.get("TENGOKU_STALE_LIMIT") or DEFAULT_LIMIT))
    ap.add_argument("--wait", type=float, default=0, help="minutes to wait while a cache build is running")
    a = ap.parse_args()
    base = run("rev-parse", a.base).strip()
    deadline = time.time() + a.wait * 60
    poll = float(os.environ.get("TENGOKU_POLL_SECONDS") or 30)
    look = 0
    while True:
        p = pointer(look)
        if p is None:
            return  # unreadable: cache.sh get will say so; this check never blocks on its own failure
        ref = reference(p, base)
        if ref is None:
            print(f"cache {p.get('tag', '?')} is not in the history of the base: cache.sh will start from an older one; nothing to judge")
            return
        n = modules_behind(ref, base)
        if n <= a.limit:
            print(f"cache fresh enough: {n} module(s) differ between {ref[:9]} (cache {p.get('tag', '?')}) and the base (limit {a.limit})")
            return
        running = builds_running()
        if not running or time.time() >= deadline:
            fail(
                f"the newest published cache ({p.get('tag', '?')}, for {ref[:9]}) is {n} modules behind this group's base (limit {a.limit}): "
                f"a change that touches many modules has merged and its cache build has not published yet, so this group would recompile them and run out of time. "
                f"{'A cache build is running: ' if running else 'No cache build is running: '}re-queue once a cache newer than the change is published"
            )
        print(
            f"{time.strftime('%H:%M:%S')} the cache is {n} modules behind (limit {a.limit}); a cache build is running — waiting", flush=True
        )
        look += 1
        time.sleep(poll)


if __name__ == "__main__":
    main()
