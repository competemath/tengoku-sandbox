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
REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")  # a release tag or an asset name: one path segment, no separators, no leading dot


def inside(path: str | Path) -> Path:
    """The absolute, symlink-free form of a path given on the command line, which must lie under the working directory or the temp directory
    (RUNNER_TEMP on a runner): a path argument never leaves the workspace, and being absolute it can never be read as an option by the tool it is
    handed to."""
    real = os.path.realpath(path)
    for root in (os.getcwd(), tempfile.gettempdir(), os.environ.get("RUNNER_TEMP") or tempfile.gettempdir()):
        base = os.path.realpath(root)
        if os.path.commonpath([base, real]) == base:
            return Path(real)
    raise ValueError(f"{str(path)!r} is outside the workspace and the temp directory")


def read_lines(path: Path) -> list[str]:
    return [ln.strip() for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip()]


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
    path = f"repos/{checked('repository', repo, REPO_RE)}/releases/tags/{checked('release', release, NAME_RE)}"
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


def checked(kind: str, value: str, rx: re.Pattern[str]) -> str:
    """A value that reaches a URL or a path: the tag in .lake/.cache-base and the repository come from a pointer file / the environment, so they are
    checked for the one shape they may have, never trusted to be a single path segment."""
    if not rx.fullmatch(value) or ".." in value:
        raise ValueError(f"{kind} {value!r} is not what it may be")
    return value


def download(repo: str, release: str, asset: str, dest: Path) -> bool:
    """One release asset by its direct URL (a plain download: no API call, no rate limit). False when it is not there."""
    checked("repository", repo, REPO_RE)
    checked("release", release, NAME_RE)
    checked("asset", asset, NAME_RE)
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


def unpack(archive: Path, dest: Path) -> None:
    """zstd -dc <archive> | tar -x -C <dest>, as two processes joined by a pipe (no shell, nothing interpolated)."""
    z = subprocess.Popen(["zstd", "-dc", str(archive)], stdout=subprocess.PIPE)
    t = subprocess.run(["tar", "-x", "-C", str(dest)], stdin=z.stdout, check=False)
    assert z.stdout is not None
    z.stdout.close()
    if z.wait() != 0 or t.returncode != 0:
        raise RuntimeError(f"could not unpack {archive.name}")


def pack_dir(src: Path, archive: Path) -> None:
    """tar -c -C <src> . | zstd -T0 -3 -q -o <archive>, no shell. COPYFILE_DISABLE: a tar made on macOS otherwise carries AppleDouble `._*`
    entries, which read as modules on a Linux runner (the chain test of 2026-10-13 saw 572 "modules" in a part of 286)."""
    t = subprocess.Popen(["tar", "-c", "-C", str(src), "."], stdout=subprocess.PIPE, env={**os.environ, "COPYFILE_DISABLE": "1"})
    z = subprocess.run(["zstd", "-T0", "-3", "-q", "-o", str(archive)], stdin=t.stdout, check=False)
    assert t.stdout is not None
    t.stdout.close()
    if t.wait() != 0 or z.returncode != 0:
        raise RuntimeError(f"could not pack {archive.name}")


def git_revs(base: str, want: str) -> list[str]:
    return run("git", "rev-list", "--reverse", f"{base}..{want}").stdout.split()


# ---- restore -------------------------------------------------------------------------------------------------------------


def parse_base(want_arg: str, release_arg: str | None) -> tuple[str, str, str, str, str]:
    """(repo, tag, base commit, wanted commit, release) from the environment and .lake/.cache-base, each checked. ValueError when one is not what it may be."""
    repo = os.environ.get("TENGOKU_CACHE_SOURCE") or os.environ.get("TENGOKU_REPO") or "competemath/tengoku"
    tag, _, base = BASE_FILE.read_text().strip().partition(" ")
    checked("repository", repo, REPO_RE)
    checked("cache tag", tag, NAME_RE)
    checked("base commit", base, re.compile(r"^[0-9a-f]{40}$"))
    try:
        want = run("git", "rev-parse", "--verify", want_arg + "^{commit}").stdout.strip()
    except subprocess.CalledProcessError as e:
        raise ValueError(f"{want_arg!r} is not a commit") from e
    return repo, tag, base, want, checked("release", release_arg or f"lake-deltas-{tag}", NAME_RE)


def load_base_mappings(repo: str, tag: str, summary: dict) -> None:
    """The base's own mappings (published with the nightly, attested): what the store already knows, for the diff of this build's new lines."""
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


def apply_delta(repo: str, release: str, name: str) -> str | None:
    """Fetch, verify and unstage one delta. None when it is applied, else why it is not: 'skipped' (not published) or 'refused: <reason>'."""
    f = STORE / name
    if not f.exists() and not download(repo, release, name, f):
        return "skipped"
    accepted, why = verify(f, repo, "queue-gate.yml")
    if not accepted:
        f.unlink(missing_ok=True)
        return f"refused: {name}: {why}"
    if "warn" in why or "not checked" in why:
        print(f"warning: {name}: {why}", file=sys.stderr)
    with tempfile.TemporaryDirectory(prefix="delta-", dir=str(LAKE)) as d:
        try:
            unpack(f, Path(d))
        except RuntimeError as e:
            return f"refused: {name}: {e}"
        r = subprocess.run(["lake", "cache", "unstage", d], capture_output=True, text=True)
        if r.returncode != 0:
            return f"refused: {name}: lake cache unstage failed: {r.stderr.strip()[:200]}"
        outs = Path(d) / "outputs.jsonl"
        if outs.exists():
            with HAD.open("a", encoding="utf-8") as h:
                h.write("".join(ln + "\n" for ln in read_lines(outs)[1:]))  # its header is the base's header already
    with APPLIED.open("a", encoding="utf-8") as ap:
        ap.write(name + "\n")
    return None


def cmd_restore(a) -> int:
    t0 = time.time()
    if not BASE_FILE.exists():
        print("no unpacked base (.lake/.cache-base): run scripts/cache.sh get first", file=sys.stderr)
        return 1
    try:
        repo, tag, base, want, release = parse_base(a.want, a.release)
    except ValueError as e:
        print(f"restore: {e}", file=sys.stderr)
        return 2
    STORE.mkdir(parents=True, exist_ok=True)
    summary: dict = {
        "base": base,
        "tag": tag,
        "want": want,
        "release": release,
        "applied": [],
        "skipped": [],
        "refused": [],
        "base_mappings": "present",
    }
    if not HAD.exists() or a.fresh:
        load_base_mappings(repo, tag, summary)
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
        why = apply_delta(repo, release, name)
        if why is None:
            applied.add(name)
            summary["applied"].append(name)
        elif why == "skipped":
            summary["skipped"].append(name)
        else:
            summary["refused"].append(why.removeprefix("refused: "))
    summary["seconds"] = round(time.time() - t0, 1)
    print(json.dumps(summary))
    return 0


# ---- pack ----------------------------------------------------------------------------------------------------------------


def stage_and_pack(new: Path, delta: Path) -> int | None:
    """lake cache stage <new> into a scratch directory and pack it as <delta>; the number of staged files, or None when Lake refuses."""
    with tempfile.TemporaryDirectory(prefix="stage-") as d:
        stage = Path(d) / "stage"
        r = subprocess.run(["lake", "cache", "stage", str(new), str(stage)], capture_output=True, text=True)
        if r.returncode != 0:
            print(f"lake cache stage failed: {r.stderr.strip()[:300]}", file=sys.stderr)
            return None
        files = sum(1 for p in stage.rglob("*") if p.is_file())
        pack_dir(stage, delta)
    return files


def cmd_pack(a) -> int:
    if not re.fullmatch(r"[0-9a-f]{40}", a.rev):
        print(f"--rev is a 40-hex commit id, not {a.rev!r}", file=sys.stderr)
        return 2
    out = a.out
    out.mkdir(parents=True, exist_ok=True)
    if len(read_lines(a.new)) <= 1:
        (out / "empty").write_text("this group changed no build output\n")
        print(json.dumps({"decision": "empty", "files": 0, "bytes": 0}))
        return 0
    budget_mb = a.budget_mb if a.budget_mb is not None else int(os.environ.get("TENGOKU_DELTA_BUDGET_MB") or 1500)
    delta = out / f"d-{a.rev}.tar.zst"
    files = stage_and_pack(a.new, delta)
    if files is None:
        return 1
    size = delta.stat().st_size
    decision = decide(size, int(a.release_assets or 0), budget_mb * 1024 * 1024)
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
    k.add_argument("--assets", dest="release_assets", type=int, default=0, help="how many assets the day's release holds now")
    k.add_argument("--budget-mb", type=int, default=None)
    a = ap.parse_args(argv)
    try:
        for attr in ("revs", "assets", "out", "had", "to", "targets", "log", "new"):
            if hasattr(a, attr):
                v = getattr(a, attr)
                setattr(a, attr, [inside(x) for x in v] if isinstance(v, list) else inside(v))
    except ValueError as e:
        print(f"lake_cache: {e}", file=sys.stderr)
        return 2

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
        a.to.write_text("".join(ln + "\n" for ln in rows), encoding="utf-8")
        print(json.dumps({"build": len(out) - 1, "known": len(out) - len(rows), "new": len(rows) - 1}))
        return 0
    if a.cmd == "check":
        targets = set(read_lines(a.targets))
        built = compiled(a.log.read_text(encoding="utf-8", errors="replace"))
        missed = sorted(built - targets)
        print(json.dumps({"targets": len(targets), "compiled": len(built), "misses": len(missed), "first": missed[:5]}))
        return 1 if (a.fail and missed) else 0
    if a.cmd == "restore":
        return cmd_restore(a)
    return cmd_pack(a)


if __name__ == "__main__":
    sys.exit(main())
