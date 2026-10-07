#!/usr/bin/env python3
"""toolchain_watch.py [--write-registry] [--out DIR] — the pinned toolchain against Lean's own record of soundness bugs (docs/jinshi.md, head K).

Lean labels its soundness issues `soundness` (a false theorem could be accepted) and `runtime-soundness` (compiled code can go wrong).
For every such issue of leanprover/lean4 this asks GitHub: is it closed, by which commit, and does the tag the tree pins in
lean-toolchain carry that fix: the commit is an ancestor of the tag, or the tag's release branch holds a backport of it (a cherry-pick
keeps the title and its `(#N)`: the release branch's history since the previous minor release is indexed by that). A `soundness` fix the
pinned toolchain lacks is a `fail` (a false theorem could be accepted); a `runtime-soundness` one it lacks is a `warn` (compiled code,
not the kernel); an issue still open, or closed without a commit the API can see, is a `warn` to read; a fix the toolchain carries is
`info`.

The result is written as findings (DIR/toolchain.jsonl, the shape every Jinshi check uses) and, with --write-registry, as
tools/jinshi/lean-bugs.json: the snapshot that goes into the repository, so a reviewer reads the verdict without the API and a change
in it shows in a diff. Reads with `gh api` (anonymous works; GH_TOKEN raises the rate limit). No Lean runs.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = "leanprover/lean4"
LABELS = ("soundness", "runtime-soundness")
REGISTRY = ROOT / "tools" / "jinshi" / "lean-bugs.json"
# kernel soundness fixes merged before Lean began labelling them (August 2026), by pull request: the July 2026 projection bug
# (#14576, fixed by #14577) and its follow-ups, the opaque-value check, the lean4lean findings, the Nat.pow and Expr.data fixes
CURATED_FIX_PRS = {
    14577: "fix: missing check at kernel inductive declaration (issue #14576: wrong-structure projections prove False)",
    14607: "fix: missing check_no_metavar_no_fvar checks at inductive.cpp",
    14608: "fix: check universe parameters in mutual definitions",
    14609: "fix: mark exported stubs of partial definitions as unsafe",
    14613: "fix: recognize sorts as Prop up to universe normalization",
    14615: "fix: decide inductive predicates up to universe normalization",
    14616: "fix: reject declarations naming the kernel's _nested auxiliary types",
    14621: "chore: re-check declarations produced by the kernel nested inductive module",
    14498: "fix: kernel to check opaque values for fvars",
    10476: "fix: infer_let in the kernel (lean4lean, issue #10475)",
    10552: "fix: make Substring.beq reflexive (lean4lean, issue #10511)",
    8060: "fix: reducing Nat.pow, kernel interprets constant as Nat literal",
}


def api(path: str):
    """GET, every page: a list endpoint's pages are concatenated; a compare's pages (one object each) have their commits merged"""
    r = subprocess.run(["gh", "api", "--paginate", path], capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(f"gh api {path}: {r.stderr.strip()[:300]}")
    docs, text, i, dec = [], r.stdout.strip(), 0, json.JSONDecoder()
    while i < len(text):
        doc, i = dec.raw_decode(text, i)
        docs.append(doc)
        while i < len(text) and text[i].isspace():
            i += 1
    if not docs:
        return None
    if all(isinstance(d, list) for d in docs):
        return [x for d in docs for x in d]
    if all(isinstance(d, dict) and isinstance(d.get("commits"), list) for d in docs):
        first = dict(docs[0])
        first["commits"] = [c for d in docs for c in d["commits"]]
        return first
    return docs[0]


def pinned_tag() -> str:
    tc = (ROOT / "lean-toolchain").read_text().strip()
    return tc.split(":", 1)[1] if ":" in tc else tc


def tag_date(tag: str) -> str:
    try:
        return api(f"repos/{REPO}/releases/tags/{tag}")["published_at"]
    except RuntimeError:
        return ""


def closing_commit(number: int) -> str | None:
    """the commit GitHub recorded on the issue's `closed` event, when a commit or merged PR closed it"""
    for ev in api(f"repos/{REPO}/issues/{number}/events?per_page=100"):
        if ev.get("event") == "closed" and ev.get("commit_id"):
            return ev["commit_id"]
    # a PR that closed it by its message: the timeline has the cross-reference
    for ev in api(f"repos/{REPO}/issues/{number}/timeline?per_page=100"):
        src = (ev.get("source") or {}).get("issue") or {}
        pr = src.get("pull_request") or {}
        if ev.get("event") == "cross-referenced" and pr.get("merged_at"):
            return api(f"repos/{REPO}/pulls/{src['number']}")["merge_commit_sha"]
    return None


def previous_minor(tag: str) -> str:
    """v4.34.0-rc2 -> v4.33.0: where the release branch forked, give or take; the history since then is where a backport lives"""
    core = tag.lstrip("v").split("-")[0]
    major, minor, _ = core.split(".")
    return f"v{major}.{int(minor) - 1}.0"


def branch_titles(tag: str) -> set[str]:
    """the first lines of every commit of the tag's history since the previous minor release"""
    try:
        commits = api(f"repos/{REPO}/compare/{previous_minor(tag)}...{tag}")["commits"]
    except RuntimeError:
        return set()
    return {c["commit"]["message"].split("\n")[0].strip() for c in commits}


def backported(number: int, title: str, titles: set[str]) -> bool:
    """a cherry-pick of the PR: a commit of the release branch whose title ends with `(#number)` or equals the PR's title"""
    tail = f"(#{number})"
    return any(t.endswith(tail) or t == title for t in titles)


def in_tag(commit: str, tag: str) -> bool | None:
    """True when `commit` is an ancestor of `tag` (compare status ahead or identical), False when not, None when the API cannot say"""
    try:
        st = api(f"repos/{REPO}/compare/{commit}...{tag}")["status"]
    except RuntimeError:
        return None
    return st in ("ahead", "identical")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", type=Path, default=Path("jinshi-out"))
    ap.add_argument("--write-registry", action="store_true")
    a = ap.parse_args()
    tag = pinned_tag()
    released = tag_date(tag)
    titles = branch_titles(tag)
    print(f"release branch of {tag}: {len(titles)} commits since {previous_minor(tag)} indexed for backports")
    findings = []
    entries = []
    labelled = [(label, it) for label in LABELS for it in api(f"repos/{REPO}/issues?labels={label}&state=all&per_page=100")]
    seen = {it["number"] for _, it in labelled}
    curated = [("soundness (curated)", api(f"repos/{REPO}/issues/{n}")) for n in sorted(CURATED_FIX_PRS) if n not in seen]
    for label, it in labelled + curated:
        if True:
            n = it["number"]
            is_pr = "pull_request" in it
            entry = {
                "number": n,
                "title": it["title"],
                "label": label,
                "is_pr": is_pr,
                "state": it["state"],
                "created": it["created_at"][:10],
                "closed": (it.get("closed_at") or "")[:10],
                "url": it["html_url"],
                "fix_commit": None,
                "in_pinned": None,
                "backported": False,
            }
            after_pin = bool(released) and it["created_at"] > released
            if it["state"] == "open":
                sev, why = "warn", "open: no fix exists yet" + (" (opened after the pinned toolchain's release)" if after_pin else "")
            else:
                commit = api(f"repos/{REPO}/pulls/{n}")["merge_commit_sha"] if is_pr else closing_commit(n)
                entry["fix_commit"] = commit
                if not commit:
                    sev, why = "warn", "closed without a commit the API can see: read the issue"
                else:
                    contained = in_tag(commit, tag)
                    if contained is False and is_pr and backported(n, it["title"], titles):
                        contained, entry["backported"] = True, True
                    entry["in_pinned"] = contained
                    if contained is True:
                        sev, why = (
                            "info",
                            f"fixed by {commit[:9]}, which {tag} contains" + (" as a backport" if entry["backported"] else ""),
                        )
                    elif contained is False:
                        sev = "fail" if label.startswith("soundness") else "warn"
                        why = f"fixed by {commit[:9]} on master; {tag} does NOT contain it and its release branch has no backport: the pinned toolchain has this bug"
                    else:
                        sev, why = "warn", f"fixed by {commit[:9]}; the API could not compare it with {tag}"
            entries.append(entry)
            findings.append(
                {
                    "check": "toolchain",
                    "severity": sev,
                    "module": "",
                    "name": f"lean4#{n}",
                    "line": None,
                    "detail": f"[{label}] {it['title']} ({it['state']}, {it['created_at'][:10]}): {why}",
                }
            )
    a.out.mkdir(parents=True, exist_ok=True)
    with (a.out / "toolchain.jsonl").open("w", encoding="utf-8") as fh:
        for f in findings:
            fh.write(json.dumps(f, ensure_ascii=False) + "\n")
    counts = {s: sum(1 for f in findings if f["severity"] == s) for s in ("fail", "warn", "info")}
    print(f"toolchain {tag} (released {released[:10] or '?'}): {len(entries)} labelled issues; {counts}")
    for f in findings:
        if f["severity"] != "info":
            print(f"  {f['severity']}: {f['name']}: {f['detail'][:160]}")
    if a.write_registry:
        REGISTRY.parent.mkdir(parents=True, exist_ok=True)
        doc = {
            "$comment": "Lean's soundness-labelled issues against the pinned toolchain; written by scripts/jinshi/toolchain_watch.py --write-registry. "
            "in_pinned: the fixing commit is an ancestor of the pinned tag or a backport on its release branch (null: open, or the API could not say).",
            "toolchain": tag,
            "toolchain_released": released,
            "checked_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "issues": sorted(entries, key=lambda e: e["number"]),
        }
        REGISTRY.write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"registry: {REGISTRY.relative_to(ROOT)} ({len(entries)} issues)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
