#!/usr/bin/env python3
"""lake_cache.py — the queue's use of Lake's own artifact cache (`lake build -o`, `lake cache stage`, `lake cache unstage`), with GitHub
releases as the store.

Lake keys every build output by a hash of all its inputs, so a seeded or restored output is used only when the sources on disk hash to it:
a wrong label can cost a rebuild, never a wrong artifact. The nightly tarball stays the bulk seed (scripts/cache.sh get). What changed since
the nightly travels as ONE small file per merge, `d-<commit>.tar.zst` (the staging directory of `lake cache stage`, packed), on the release
`lake-deltas-<cache tag>` of the nightly it builds on; the nightly publishes its own mappings as `base.jsonl` on the cache release. A release
holds at most 1000 assets, so a day's merges fit and a new nightly starts a new release.

  restore [--want <commit>]                  after `cache.sh get`: apply the deltas of the merges between the nightly base and <commit> (HEAD)
                                             — `git rev-list --reverse base..want` ∩ the release's assets, oldest first, each attested —
                                             with `lake cache unstage`; what the store already knows goes to .lake/deltas-had.jsonl
  diff   --out <file> --had <file>... --to <file>
                                             this build's OWN new mappings: the lines of its `lake build -o` file that no earlier file has;
                                             line 1 (the file's header) stays line 1 — `lake cache stage` refuses a mappings file without it
  pack   --rev <sha> --new <file> --out <dir> [--assets N] [--budget-mb N]
                                             stage the new mappings, pack them as <dir>/d-<sha>.tar.zst — or, over the size budget or with the
                                             release nearly full, write <dir>/needs-nightly instead (the merge lands; a nightly follows)
  plan   --revs <file> --assets <file>       (pure) the delta assets to apply, oldest first
  check  --targets <file> --log <file> [--fail]
                                             (pure) modules the build COMPILED that are not its targets: restores that missed

Environment: TENGOKU_REPO (where deltas are published), TENGOKU_CACHE_SOURCE (where they are read; a sandbox may read the library's),
TENGOKU_VERIFY (require: an unattested or tampered delta is skipped and Lake compiles instead; warn: applied with a warning),
TENGOKU_DELTA_BUDGET_MB (default 1500), LAKE_CACHE_DIR (where Lake keeps the cache). Every network step is curl/gh and can be shimmed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

DELTA = re.compile(r"^d-([0-9a-f]{40})\.tar\.zst$")
BUILT = re.compile(r"\bBuilt\s+(\S+)")
LAKE = Path(".lake")
BASE_FILE = LAKE / ".cache-base"  # "<tag> <commit>", written by cache.sh get
APPLIED = LAKE / ".deltas-applied"  # one asset name per line
HAD = LAKE / "deltas-had.jsonl"  # base.jsonl + every applied delta's outputs.jsonl
STORE = LAKE / ".delta-store"
ASSET_CAP = 990  # a release holds at most 1000 assets; stop before the last ones, there may be uploads in flight
HTTPS_ONLY = ["--proto", "=https", "--tlsv1.2"]


def read_lines(path: str | Path) -> list[str]:
    return [ln.strip() for ln in Path(path).read_text(encoding="utf-8").splitlines() if ln.strip()]


# ---- pure ----------------------------------------------------------------------------------------------------------------


def plan(revs: list[str], assets: list[str]) -> list[str]:
    """The `d-<rev>.tar.zst` assets for the revisions in `revs` (oldest first) that exist; nothing else in the release is named by a revision."""
    have = {m.group(1): a for a in assets if (m := DELTA.match(a))}
    return [have[r] for r in revs if r in have]


def diff(out: list[str], had: set[str]) -> list[str]:
    """The header and the mappings of `out` that `had` does not contain, in order, without repeats. `out` is a mappings file's lines, header first."""
    if not out:
        raise ValueError("an empty mappings file has no header")
    header, body = out[0], out[1:]
    seen: set[str] = set()
    new = []
    for ln in body:
        if ln not in had and ln not in seen:
            seen.add(ln)
            new.append(ln)
    return [header, *new]


def compiled(log: str) -> set[str]:
    """Modules a Lake build log says it built (a module that was only replayed or restored is not built)."""
    return {m.group(1) for m in BUILT.finditer(log)}


def decide(size: int, assets: int, budget: int, cap: int = ASSET_CAP) -> str:
    """'publish', or why the merge lands without a delta: 'needs-nightly:over-budget' (the file would not fit the budget, or GitHub's 2 GiB) or
    'needs-nightly:release-full' (the day's release is nearly at GitHub's 1000 assets)."""
    if assets >= cap:
        return "needs-nightly:release-full"
    if size > budget:
        return "needs-nightly:over-budget"
    return "publish"


# ---- processes -----------------------------------------------------------------------------------------------------------


def run(*cmd: str, check: bool = True, capture: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, check=check, capture_output=capture, text=True)


def have_gh() -> bool:
    return shutil.which("gh") is not None and subprocess.run(["gh", "auth", "status"], capture_output=True).returncode == 0


def release_assets(repo: str, release: str) -> list[str] | None:
    """Asset names of a release, or None when the release does not exist (a nightly older than this design, or a sandbox without one)."""
    path = f"repos/{repo}/releases/tags/{release}"
    if have_gh():
        r = subprocess.run(["gh", "api", path], capture_output=True, text=True)
        if r.returncode != 0:
            return None
        body = r.stdout
    else:
        req = urllib.request.Request(f"https://api.github.com/{path}", headers={"Accept": "application/vnd.github+json"})
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:  # noqa: S310 (an https URL built above)
                body = resp.read().decode("utf-8")
        except Exception:
            return None
    try:
        return [a["name"] for a in json.loads(body).get("assets", [])]
    except Exception:
        return None


def download(repo: str, release: str, asset: str, dest: Path) -> bool:
    """One release asset by its direct URL (a plain download: no API call, no rate limit). False when it is not there."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    part = dest.with_suffix(dest.suffix + ".part")
    r = subprocess.run(
        ["curl", *HTTPS_ONLY, "-fsSL", "--retry", "2", "-o", str(part), f"https://github.com/{repo}/releases/download/{release}/{asset}"],
        capture_output=True,
    )
    if r.returncode != 0:
        part.unlink(missing_ok=True)
        return False
    part.replace(dest)
    return True


def verify(path: Path, repo: str, workflow: str) -> tuple[bool, str]:
    """(accepted, why). TENGOKU_VERIFY=require: only a file with a valid build attestation from `workflow` of `repo` is accepted; warn: an
    unverifiable file is accepted with a warning (gh absent, or no attestation yet)."""
    mode = os.environ.get("TENGOKU_VERIFY", "warn")
    if not have_gh():
        return (mode != "require", "gh not available: attestation not checked")
    r = subprocess.run(
        ["gh", "attestation", "verify", str(path), "-R", repo, "--signer-workflow", f"{repo}/.github/workflows/{workflow}"],
        capture_output=True,
        text=True,
    )
    if r.returncode == 0:
        return (True, "attestation verified")
    return (mode != "require", "no valid build attestation" + (" (TENGOKU_VERIFY=warn)" if mode != "require" else ""))


def git_revs(base: str, want: str) -> list[str]:
    return run("git", "rev-list", "--reverse", f"{base}..{want}").stdout.split()


# ---- restore -------------------------------------------------------------------------------------------------------------


def cmd_restore(a) -> int:
    t0 = time.time()
    repo = os.environ.get("TENGOKU_CACHE_SOURCE") or os.environ.get("TENGOKU_REPO") or "competemath/tengoku"
    if not BASE_FILE.exists():
        print("no unpacked base (.lake/.cache-base): run scripts/cache.sh get first", file=sys.stderr)
        return 1
    tag, _, base = BASE_FILE.read_text().strip().partition(" ")
    want = run("git", "rev-parse", a.want).stdout.strip()
    release = a.release or f"lake-deltas-{tag}"
    STORE.mkdir(parents=True, exist_ok=True)
    summary = {
        "base": base,
        "tag": tag,
        "want": want,
        "release": release,
        "applied": [],
        "skipped": [],
        "refused": [],
        "base_mappings": "present",
    }
    # the base's own mappings: what the store already knows, for the diff of this build's new lines
    if not HAD.exists() or a.fresh:
        bj = STORE / f"base-{tag}.jsonl"
        ok = bj.exists() or download(repo, tag, "base.jsonl", bj)
        accepted, why = verify(bj, repo, "build.yml") if ok else (False, "not published")
        if ok and accepted:
            HAD.write_text(bj.read_text(encoding="utf-8"), encoding="utf-8")
        else:
            HAD.write_text("", encoding="utf-8")
            summary["base_mappings"] = f"missing ({why}): the build computes them (lake build Tengoku.All -o)"
            (LAKE / ".base-missing").write_text(tag + "\n")
        APPLIED.write_text("", encoding="utf-8")
    applied = set(read_lines(APPLIED)) if APPLIED.exists() else set()
    revs = git_revs(base, want)
    assets = release_assets(repo, release)
    summary["revs"] = len(revs)
    if assets is None:
        summary["note"] = f"no release {release}: nothing merged since the base is restorable, Lake compiles it"
        assets = []
    for name in plan(revs, assets):
        if name in applied:
            continue
        f = STORE / name
        if not f.exists() and not download(repo, release, name, f):
            summary["skipped"].append(name)
            continue
        accepted, why = verify(f, repo, "queue-gate.yml")
        if not accepted:
            f.unlink(missing_ok=True)
            summary["refused"].append(f"{name}: {why}")
            continue
        if "warn" in why or "not checked" in why:
            print(f"warning: {name}: {why}", file=sys.stderr)
        with tempfile.TemporaryDirectory(prefix="delta-", dir=str(LAKE)) as d:
            subprocess.run(["bash", "-c", f'zstd -dc "{f}" | tar -x -C "{d}"'], check=True)
            r = subprocess.run(["lake", "cache", "unstage", d], capture_output=True, text=True)
            if r.returncode != 0:
                summary["refused"].append(f"{name}: lake cache unstage failed: {r.stderr.strip()[:200]}")
                continue
            outs = Path(d) / "outputs.jsonl"
            if outs.exists():
                with HAD.open("a", encoding="utf-8") as h:
                    h.write("".join(ln + "\n" for ln in read_lines(outs)[1:]))  # its header is the base's header already
        with APPLIED.open("a", encoding="utf-8") as ap:
            ap.write(name + "\n")
        applied.add(name)
        summary["applied"].append(name)
    summary["seconds"] = round(time.time() - t0, 1)
    print(json.dumps(summary))
    return 0


# ---- pack ----------------------------------------------------------------------------------------------------------------


def cmd_pack(a) -> int:
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    rows = read_lines(a.new)
    if len(rows) <= 1:
        (out / "empty").write_text("this group changed no build output\n")
        print(json.dumps({"decision": "empty", "files": 0, "bytes": 0}))
        return 0
    budget = int(a.budget_mb if a.budget_mb is not None else (os.environ.get("TENGOKU_DELTA_BUDGET_MB") or 1500)) * 1024 * 1024
    with tempfile.TemporaryDirectory(prefix="stage-") as d:
        stage = Path(d) / "stage"
        r = subprocess.run(["lake", "cache", "stage", a.new, str(stage)], capture_output=True, text=True)
        if r.returncode != 0:
            print(f"lake cache stage failed: {r.stderr.strip()[:300]}", file=sys.stderr)
            return 1
        files = sum(1 for p in stage.rglob("*") if p.is_file())
        delta = out / f"d-{a.rev}.tar.zst"
        # COPYFILE_DISABLE: a tar made on macOS otherwise carries AppleDouble `._*` entries, which read as modules on a Linux runner
        # (the chain test of 2026-10-13 saw 572 "modules" in a part of 286)
        subprocess.run(
            ["bash", "-c", f'tar -c -C "{stage}" . | zstd -T0 -3 -q -o "{delta}"'], check=True, env={**os.environ, "COPYFILE_DISABLE": "1"}
        )
    size = delta.stat().st_size
    decision = decide(size, int(a.assets or 0), budget)
    if decision != "publish":
        delta.unlink()
        (out / "needs-nightly").write_text(decision + "\n")
    print(json.dumps({"decision": decision, "files": files, "bytes": size, "asset": delta.name if decision == "publish" else None}))
    return 0


# ---- main ----------------------------------------------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--revs", required=True)
    p.add_argument("--assets", required=True)
    d = sub.add_parser("diff")
    d.add_argument("--out", required=True)
    d.add_argument("--had", nargs="+", required=True)
    d.add_argument("--to", required=True)
    c = sub.add_parser("check")
    c.add_argument("--targets", required=True)
    c.add_argument("--log", required=True)
    c.add_argument("--fail", action="store_true")
    r = sub.add_parser("restore")
    r.add_argument("--want", default="HEAD")
    r.add_argument("--release", default=None)
    r.add_argument("--fresh", action="store_true", help="forget what was applied before (a new base was unpacked)")
    k = sub.add_parser("pack")
    k.add_argument("--rev", required=True)
    k.add_argument("--new", required=True)
    k.add_argument("--out", required=True)
    k.add_argument("--assets", type=int, default=0, help="how many assets the day's release holds now")
    k.add_argument("--budget-mb", type=int, default=None)
    a = ap.parse_args(argv)

    if a.cmd == "plan":
        for name in plan(read_lines(a.revs), read_lines(a.assets)):
            print(name)
        return 0
    if a.cmd == "diff":
        had: set[str] = set()
        for f in a.had:
            had.update(read_lines(f))
        out = read_lines(a.out)
        rows = diff(out, had)
        Path(a.to).write_text("".join(ln + "\n" for ln in rows), encoding="utf-8")
        print(json.dumps({"build": len(out) - 1, "known": len(out) - len(rows), "new": len(rows) - 1}))
        return 0
    if a.cmd == "check":
        targets = set(read_lines(a.targets))
        built = compiled(Path(a.log).read_text(encoding="utf-8", errors="replace"))
        missed = sorted(built - targets)
        print(json.dumps({"targets": len(targets), "compiled": len(built), "misses": len(missed), "first": missed[:5]}))
        return 1 if (a.fail and missed) else 0
    if a.cmd == "restore":
        return cmd_restore(a)
    return cmd_pack(a)


if __name__ == "__main__":
    sys.exit(main())
