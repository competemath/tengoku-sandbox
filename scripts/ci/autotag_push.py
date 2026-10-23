#!/usr/bin/env python3
"""autotag_push.py --repo OWNER/NAME --pr N --head SHA --artifact DIR [--dry-run] — add the tags the autotag-build workflow wrote to the PR's branch.

The trusted half of the autotag (scripts/ci/autotag.py): it runs from the repository's default branch, holds the bot's token and runs no code of the PR. The artifact is DATA from a job
that ran the PR's Lean, so nothing in it is believed:

  the PR     open, from a branch of this repository, its head is the commit the build tagged, and its author is one of the lane's Apps (AUTOTAG_ACTORS)
  the files  each is a module the PR ADDS (`Tengoku/**.lean`, not an umbrella file), at most MAX_MODULES of them; the artifact's copy differs from the PR's, `isnad_tag.equivalent`
             holds (what changed is tags and nothing a compiler reads, so the module has the same canonical form and the lane's build attestation, which covers the
             modules in that form, still covers it: scripts/ci/studied_check.py rebuilds the archive from `canonical_text`), and its tags are well formed and from
             the place the module lives (born_tagged.py)
  the push   one commit on the PR's branch, through the git data API, with the head as its only parent and a ref update that is not forced: if the branch moved in the
             meantime nothing is written. The commit is signed off by the bot (the DCO gate reads the trailer).

Whether a tag IS the id of its theorem is for the merge queue, which builds the modules and recomputes every tag (tag_verify.py).
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))  # scripts/ of the checkout this file is in
import isnad_tag as tg  # noqa: E402
from autotag import MAX_MODULES, actors  # noqa: E402
from born_tagged import ROOT_FILE, UMBRELLAS, module_errors  # noqa: E402

REPO = re.compile(r"[A-Za-z0-9_.-]{1,100}/[A-Za-z0-9_.-]{1,100}")
SHA40 = re.compile(r"[0-9a-f]{40}")
BRANCH = re.compile(r"[A-Za-z0-9._/-]{1,200}")
MODULE_PATH = re.compile(r"Tengoku/[^\x00-\x1f\\]{1,300}\.lean")

Api = Callable[..., object]


class Refused(Exception):
    pass


def gh_api(method: str, path: str, body: dict | None = None, raw: bool = False) -> object:
    """`gh api` with the token in GH_TOKEN. Raw: the file's bytes, not JSON."""
    cmd = ["gh", "api", "-X", method, path]
    if raw:
        cmd += ["-H", "Accept: application/vnd.github.raw"]
    if body is not None:
        cmd += ["--input", "-"]
    r = subprocess.run(cmd, input=json.dumps(body) if body is not None else None, capture_output=True, text=not raw, check=False)
    if r.returncode != 0:
        raise Refused(f"gh api {method} {path}: {(r.stderr if not raw else r.stderr.decode('utf-8', 'replace'))[:300]}")
    if raw:
        return r.stdout
    return json.loads(r.stdout) if r.stdout.strip() else {}


def safe_path(p: str) -> bool:
    return (
        bool(MODULE_PATH.fullmatch(p))
        and ".." not in p.split("/")
        and not p.startswith("/")
        and p not in UMBRELLAS
        and not ROOT_FILE.fullmatch(p)
    )


def artifact_files(directory: Path) -> dict[str, str]:
    """The tagged modules of the artifact: {path in the repository: text}. A symlink is never followed."""
    root = directory.resolve()
    out: dict[str, str] = {}
    for p in sorted(root.rglob("*.lean")):
        if p.is_symlink() or not p.is_file() or root not in p.resolve().parents:
            raise Refused(f"{p}: not a regular file inside the artifact")
        rel = str(p.relative_to(root))
        if not safe_path(rel):
            raise Refused(f"{rel}: not a path the autotag writes")
        try:
            out[rel] = p.read_text(encoding="utf-8")
        except UnicodeDecodeError as e:
            raise Refused(f"{rel}: not UTF-8") from e
    return out


def pr_files(api: Api, repo: str, pr: int) -> dict[str, str]:
    """{path: status} of the PR's files, as GitHub lists them (all pages)."""
    out: dict[str, str] = {}
    page = 1
    while True:
        rows = api("GET", f"repos/{repo}/pulls/{pr}/files?per_page=100&page={page}")
        if not isinstance(rows, list):
            raise Refused("the PR's file list is not a list")
        for r in rows:
            out[str(r["filename"])] = str(r["status"])
        if len(rows) < 100:
            return out
        page += 1


def check(api: Api, repo: str, pr: int, head: str, files: dict[str, str], env: dict[str, str]) -> dict:
    """Everything that must hold before anything is written. Returns the PR's JSON."""
    if not REPO.fullmatch(repo) or pr < 1 or not SHA40.fullmatch(head):
        raise Refused("repo, pr and head must be an owner/name, a number and a 40-hex commit")
    if not files:
        raise Refused("the artifact holds no module")
    if len(files) > MAX_MODULES:
        raise Refused(f"{len(files)} modules (cap {MAX_MODULES})")
    info = api("GET", f"repos/{repo}/pulls/{pr}")
    if not isinstance(info, dict):
        raise Refused("no such pull request")
    head_info = info.get("head") or {}
    if info.get("state") != "open":
        raise Refused("the PR is not open")
    if head_info.get("sha") != head:
        raise Refused(
            f"the PR's head moved on ({str(head_info.get('sha'))[:12]}, the build tagged {head[:12]}): a new run tags the new head"
        )
    if (head_info.get("repo") or {}).get("full_name") != repo:
        raise Refused("the PR's branch is not in this repository")
    author = ((info.get("user") or {}).get("login")) or ""
    if author not in actors(env):
        raise Refused(f"{author!r} is not one of the lane's Apps")
    ref = str(head_info.get("ref") or "")
    if not BRANCH.fullmatch(ref) or ref in ("main", "master") or ref.startswith("-"):
        raise Refused(f"the branch {ref!r} is not one the autotag writes to")
    listed = pr_files(api, repo, pr)
    for path, new in sorted(files.items()):
        if listed.get(path) != "added":
            raise Refused(f"{path}: not a module this PR adds (status {listed.get(path)!r})")
        raw = api("GET", f"repos/{repo}/contents/{path}?ref={head}", raw=True)
        old = raw.decode("utf-8") if isinstance(raw, bytes) else str(raw)
        if new == old:
            raise Refused(f"{path}: the artifact's copy is the PR's: nothing was tagged")
        if not tg.equivalent(old, new):
            raise Refused(f"{path}: changes more than tags")
        errors = module_errors(path, new)
        if errors:
            raise Refused("; ".join(errors[:3]))
    return info


def message(n: int, bot: str, email: str) -> str:
    return (
        f"isnad: tags for {n} module{'s' if n != 1 else ''} (born tagged)\n\n"
        "Written by scripts/isnad.py tag on the built tree (the autotag-build workflow) and checked against this PR's own files by "
        "scripts/ci/autotag_push.py: only tags changed, and the modules without them are the bytes the lane attested.\n\n"
        f"Signed-off-by: {bot} <{email}>\n"
    )


def push(api: Api, repo: str, pr: int, head: str, files: dict[str, str], env: dict[str, str], dry_run: bool = False) -> str:
    info = check(api, repo, pr, head, files, env)
    bot = env.get("TENGOKU_BOT") or "tengoku-bot"
    email = env.get("TENGOKU_BOT_EMAIL") or f"{bot}@users.noreply.github.com"
    if dry_run:
        return f"dry run: {len(files)} module(s) would be tagged on {info['head']['ref']}"
    commit = api("GET", f"repos/{repo}/git/commits/{head}")
    entries = []
    for path, text in sorted(files.items()):
        blob_ = api("POST", f"repos/{repo}/git/blobs", {"content": base64.b64encode(text.encode("utf-8")).decode(), "encoding": "base64"})
        entries.append({"path": path, "mode": "100644", "type": "blob", "sha": blob_["sha"]})  # type: ignore[index]
    tree = api("POST", f"repos/{repo}/git/trees", {"base_tree": commit["tree"]["sha"], "tree": entries})  # type: ignore[index]
    who = {"name": bot, "email": email}
    new = api(
        "POST",
        f"repos/{repo}/git/commits",
        {"message": message(len(files), bot, email), "tree": tree["sha"], "parents": [head], "author": who, "committer": who},  # type: ignore[index]
    )
    # not forced: a branch that moved since the check keeps what it has
    api("PATCH", f"repos/{repo}/git/refs/heads/{info['head']['ref']}", {"sha": new["sha"], "force": False})  # type: ignore[index]
    return f"tagged {len(files)} module(s): {new['sha'][:12]} on {info['head']['ref']}"  # type: ignore[index]


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--pr", type=int, required=True)
    ap.add_argument("--head", required=True)
    ap.add_argument("--artifact", required=True)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv[1:])
    try:
        print(push(gh_api, a.repo, a.pr, a.head, artifact_files(Path(a.artifact)), dict(os.environ), a.dry_run))
    except Refused as e:
        print(f"autotag_push: refused: {e}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
