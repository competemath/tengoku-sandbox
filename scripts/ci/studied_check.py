#!/usr/bin/env python3
"""studied_check.py <base> <head> [--tar OUT.tar] — the checks of a STUDIED PR.

A studied PR carries theorems that Leak runs proved and that were rated four stars or more (Leak's memory, kept and shared by their author; the
intake job in competemath/emissary-archangel, .github/workflows/memory-intake.yml, re-derived every one of them and opened this PR as the studied
App). It adds, for ONE target `<t>` (`Ns` = its Pascal-case name):

  data/studied/<t>/manifest.jsonl          one JSON line per theorem; the tree's lines are a byte prefix of the PR's (append only)
  data/studied/<t>/bundles/<id16>.json     the bundle's report: what the intake job did (compiled, re-rated, Jinshi, reviewers)
  Tengoku/Studied/<Ns>/S<id12>.lean        one module per theorem, its declarations inside `namespace Tengoku.Studied.<Ns>.S<id12>`
  Tengoku/Studied/<Ns>.lean                the target's root file: one import per module
  Tengoku/Studied.lean                     gains `import Tengoku.Studied.<Ns>` when the target arrives for the first time (the very first studied
                                           PR creates it, and adds `import Tengoku.Studied` to Tengoku/All.lean: nothing else touches All.lean)

This runs no Lean. It checks, from the PR's git objects only:

  shape       one target; only those files; modules are new files; at most MAX_THEOREMS theorems; size caps
  manifest    name, statement, module, target, entry, stars (4 or 5), author, bundle, toolchain (= lean-toolchain), source `leak-memory`; one line per
              module and one module per line; the statement is the one the module declares; names unique and not the target's earlier ones
  lint        every module passes the content allow-list (scripts/ci/allowlist.py) after its header; the header only imports the tree; the declarations
              are inside the module's own namespace, so a studied theorem can never shadow another library's name
  report      the bundle id is the hash of target, author and entries; the intake job compiled every theorem, re-rated each at 4 stars or more (the
              producer's stars are only a claim), Jinshi's checks found no failure, no reviewer blocked, and every theorem carries the harness evidence the
              server judged (the run's ticket at least 30 minutes old, a known build, plausible counters that agree with the ticket's age)
  provenance  with --tar, the bundle archive is rebuilt from the PR's files for the workflow to check against the intake job's build attestation:
              the bytes that job built are the bytes in this PR

What is NOT checked here is the Lean itself (the merge queue builds the modules, sealed, and checks every theorem's axioms) and who may approve
(scripts/ci/studied_approval.py: one code owner, or two independent contributors with write access).
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))  # scripts/ of the checkout this file is in
import isnad_tag as tg  # noqa: E402
from _git import ROOT, blob, changed_files, fail, module_name, pascal, run  # noqa: E402
from allowlist import violations  # noqa: E402
from bundle_tar import write_tar  # noqa: E402
from lean_lex import code_only  # noqa: E402

MANIFEST_RE = re.compile(r"data/studied/([^/]+)/manifest\.jsonl")
TARGET_ID = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*")
ENTRY = re.compile(r"[0-9a-f]{8,64}")
AUTHOR = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,99}")
SHA256 = re.compile(r"[0-9a-f]{64}")
IMPORT_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$")
MODULE_LINE = re.compile(r"^\s*(?:module|prelude)\s*$")
TREE_IMPORT = re.compile(r"(?:Tengoku|Lean|Std|Init)(?:\.|$)")
MAX_THEOREMS = 10
# What a run's harness evidence has to look like (competemath.com app/lib/leak-memory/harness.ts judges the same bands when it keeps a theorem; the intake job
# records the result in the report, and this repeats the arithmetic on it so that a report that skips the server's judgement cannot pass). Keep in step.
MIN_RUN_S, MAX_RUN_S = 30 * 60, 49 * 3600
MEMORY_STRATEGY = re.compile(r"control-(?:honoured|flint|paragon|lucid)(?:-iv)?")
MAX_MODULE_BYTES = 60 * 1024
MAX_TOTAL_BYTES = 600 * 1024
TOP = "Tengoku/Studied.lean"
ALL = "Tengoku/All.lean"
LEAN = ".lean"


def untagged(raw: bytes | None) -> bytes | None:
    """A module's bytes as the intake job attested them: without isnad tags, in the canonical form (scripts/isnad_tag.py `canonical_text`); bytes that are not text
    are left as they are."""
    if raw is None:
        return None
    try:
        return tg.canonical_text(raw.decode("utf-8")).encode("utf-8")
    except UnicodeDecodeError:
        return raw


def studied_targets(files: list[tuple[str, str]]) -> set[str]:
    """The targets whose manifest the diff touches: what makes a PR a studied PR."""
    return {m.group(1) for _, p in files if (m := MANIFEST_RE.fullmatch(p))}


def is_studied(base: str, head: str) -> bool:
    return bool(studied_targets(changed_files(base, head)))


def tier(p: str, targets: set[str]) -> str | None:
    """`studied` for the paths a studied PR of these targets may own (classify.py), else None."""
    for t in targets:
        ns = pascal(t)
        if p.startswith(f"data/studied/{t}/") or p == f"Tengoku/Studied/{ns}.lean" or p.startswith(f"Tengoku/Studied/{ns}/"):
            return "studied"
    if targets and p in (TOP, ALL):  # the very first studied PR creates the top file and adds its one line to All.lean (checked below)
        return "studied"
    return None


def bundle_id(target: str, author: str, entries: list[str]) -> str:
    """What the intake job calls the bundle: stable for the same author, target and theorems, whatever order they were found in."""
    return hashlib.sha256((f"{target}\n{author}\n" + "\n".join(sorted(entries))).encode()).hexdigest()


def squash(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def check(base: str, head: str, tar_out: str = "") -> None:
    files = changed_files(base, head)
    targets = studied_targets(files)
    if len(targets) != 1:
        fail(f"a studied PR has exactly one data/studied/<target>/manifest.jsonl (found {sorted(targets)})")
    t = next(iter(targets))
    if not TARGET_ID.fullmatch(t):
        fail(f"target {t!r} is not a lowercase id (letters, digits, single hyphens)")
    ns = pascal(t)
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", ns):
        fail(f"target {t!r}: Tengoku/Studied/{ns}/ is not a Lean namespace")
    MANIFEST, ROOT_FILE = f"data/studied/{t}/manifest.jsonl", f"Tengoku/Studied/{ns}.lean"
    report_files = [p for _, p in files if re.fullmatch(rf"data/studied/{re.escape(t)}/bundles/[0-9a-f]{{16}}\.json", p)]
    mod_re = re.compile(rf"Tengoku/Studied/{ns}/S([0-9a-f]{{12}})\.lean")
    errors: list[str] = []
    first = blob(base, MANIFEST) is None  # the target arrives for the first time
    top_new = blob(base, TOP) is None  # ... and no studied theorem has ever arrived: this PR creates the top file

    # shape: only this target's files, modules and the report are new files, the manifest and root file may only grow
    for st, p in files:
        if p in report_files or mod_re.fullmatch(p):
            if st != "A":
                errors.append(f"{p}: a studied PR only adds this file (status {st})")
        elif p == MANIFEST:
            if st != ("A" if first else "M"):
                errors.append(f"{p}: status {st}, expected {'A' if first else 'M'}")
        elif p == ROOT_FILE:
            if st != ("A" if first else "M"):
                errors.append(f"{p}: status {st}, expected {'A' if first else 'M'}")
        elif p == TOP:
            if st != ("A" if top_new else "M") or not first:
                errors.append(f"{p}: only the first bundle of a target changes it, by one import line (status {st})")
        elif p == ALL:
            if not top_new or st != "M":
                errors.append(f"{p}: only the very first studied PR changes it, by `import Tengoku.Studied` (status {st})")
        else:
            errors.append(f"{p}: not part of {t}'s studied bundle")
    if len(report_files) != 1:
        errors.append(f"a studied PR adds exactly one bundle report data/studied/{t}/bundles/<16 hex>.json (found {len(report_files)})")
    modules = sorted(p for _, p in files if mod_re.fullmatch(p))
    if not modules:
        errors.append("no module: a bundle that carries no theorem is empty")
    if len(modules) > MAX_THEOREMS:
        errors.append(f"{len(modules)} theorems in one PR (cap {MAX_THEOREMS})")
    if errors:  # a PR that is not the right shape is not read any further
        fail("studied PR for " + t + ": " + "; ".join(errors[:12]))

    def show(path: str) -> str:
        return (blob(head, path) or b"").decode("utf-8")

    def lines_of(text: str) -> list[str]:
        if not text:
            return []
        parts = text.split("\n")
        return parts[:-1] if text.endswith("\n") else parts

    # the root files
    new_mods = [module_name(p[: -len(LEAN)]) for p in modules]
    wanted = {f"import {m}" for m in new_mods}
    root_lines = lines_of(show(ROOT_FILE))
    old_root = lines_of((blob(base, ROOT_FILE) or b"").decode("utf-8"))
    if sorted(ln.strip() for ln in root_lines if ln.strip() in wanted) != sorted(wanted):
        errors.append(f"{ROOT_FILE} must import each new module exactly once")
    if [ln for ln in root_lines if ln.strip() not in wanted] != old_root:
        errors.append(f"{ROOT_FILE} may only gain the imports of the new modules")

    def added(path: str) -> list[str]:
        return [
            ln for ln in run("diff", "-U0", f"{base}...{head}", "--", path).splitlines() if ln[:1] in "+-" and ln[:3] not in ("+++", "---")
        ]

    if first:
        if top_new:  # a new file: its lines are all added; it holds that one import (and comment lines)
            body = [ln for ln in lines_of(show(TOP)) if ln.strip() and not ln.lstrip().startswith(("--", "/-", "-/", "*"))]
            if body != [f"import Tengoku.Studied.{ns}"]:
                errors.append(f"{TOP} is created holding exactly `import Tengoku.Studied.{ns}` (found: {body[:3]})")
            if added(ALL) not in (["+import Tengoku.Studied"], ["+public import Tengoku.Studied"]):
                errors.append(f"{ALL} must gain exactly `import Tengoku.Studied` and change nothing else (diff: {added(ALL)[:4]})")
        elif added(TOP) != [f"+import Tengoku.Studied.{ns}"]:
            errors.append(f"{TOP} must gain exactly `import Tengoku.Studied.{ns}` and change nothing else (diff: {added(TOP)[:4]})")

    # the manifest: only gains lines
    old_bytes, new_bytes = blob(base, MANIFEST) or b"", blob(head, MANIFEST) or b""
    if not new_bytes.startswith(old_bytes) or (old_bytes and not old_bytes.endswith(b"\n")) or not new_bytes.endswith(b"\n"):
        errors.append("manifest.jsonl may only gain whole lines at its end")
        manifest_new = b""
    else:
        manifest_new = new_bytes[len(old_bytes) :]
    seen = {m.group(1) for m in re.finditer(r'"name":\s*"([^"]+)"', old_bytes.decode("utf-8", errors="replace"))}
    try:
        manifest = [json.loads(ln) for ln in manifest_new.decode("utf-8").splitlines() if ln.strip()]
    except Exception as e:  # noqa: BLE001
        manifest = []
        errors.append(f"manifest.jsonl is not JSON lines: {e}")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    authors: set[str] = set()
    entries: list[str] = []
    stars: dict[str, int] = {}
    bundles: set[str] = set()
    by_module: dict[str, dict] = {}
    for i, r in enumerate(manifest, 1):
        where = f"manifest line {i}"
        if not isinstance(r, dict):
            errors.append(f"{where}: not a JSON object")
            continue
        for k in ("name", "statement", "module", "target", "entry", "author", "bundle", "toolchain", "source"):
            if not isinstance(r.get(k), str) or not r[k].strip():
                errors.append(f"{where}: `{k}` missing")
        if r.get("target") != t:
            errors.append(f"{where}: target {r.get('target')!r}, expected {t!r}")
        if r.get("toolchain") != toolchain:
            errors.append(f"{where}: toolchain {r.get('toolchain')!r}, the tree is on {toolchain!r}")
        if r.get("source") != "leak-memory":
            errors.append(f"{where}: source {r.get('source')!r}, expected 'leak-memory'")
        if not isinstance(r.get("entry"), str) or not ENTRY.fullmatch(r["entry"]):
            errors.append(f"{where}: `entry` is not a hex id")
        if not isinstance(r.get("author"), str) or not AUTHOR.fullmatch(r["author"]):
            errors.append(f"{where}: `author` is not an account name")
        if not isinstance(r.get("bundle"), str) or not SHA256.fullmatch(r["bundle"]):
            errors.append(f"{where}: `bundle` is not a sha-256")
        if not isinstance(r.get("stars"), int) or isinstance(r.get("stars"), bool) or r["stars"] not in (4, 5):
            errors.append(f"{where}: `stars` is {r.get('stars')!r}; a studied theorem has 4 or 5")
        name = r.get("name") if isinstance(r.get("name"), str) else ""
        if name in seen:
            errors.append(f"{where}: {name} twice (or already in the target's manifest)")
        seen.add(name)
        mod = r.get("module")
        entry = r.get("entry") if isinstance(r.get("entry"), str) else ""
        want_mod = f"Tengoku.Studied.{ns}.S{entry[:12]}"
        if mod != want_mod or f"Tengoku/Studied/{ns}/S{entry[:12]}.lean" not in modules:
            errors.append(f"{where}: module {mod!r} is not {want_mod} (or its file is not in this PR)")
        elif mod in by_module:
            errors.append(f"{where}: module {mod} twice")
        else:
            by_module[mod] = r
        authors.add(str(r.get("author")))
        bundles.add(str(r.get("bundle")))
        entries.append(entry)
        if isinstance(r.get("stars"), int):
            stars[entry] = r["stars"]
    if len(manifest) != len(modules):
        errors.append(f"{len(manifest)} manifest lines for {len(modules)} modules: one each")
    if len(authors) > 1 or len(bundles) > 1:
        errors.append("one PR is one bundle: one author, one bundle id in every manifest line")

    # the report
    author = next(iter(authors)) if len(authors) == 1 else ""
    bundle = next(iter(bundles)) if len(bundles) == 1 else ""
    rp = report_files[0]
    try:
        rep = json.loads(show(rp))
        if not isinstance(rep, dict):
            raise ValueError("not an object")
    except Exception as e:  # noqa: BLE001
        rep = {}
        errors.append(f"{rp} is not a JSON report: {e}")
    if rep:
        if rep.get("schema") != "studied-bundle/1":
            errors.append(f"{rp}: schema {rep.get('schema')!r}, expected 'studied-bundle/1'")
        if rep.get("target") != t or rep.get("author") != author or rep.get("bundle") != bundle:
            errors.append(f"{rp}: target, author and bundle must be the manifest's")
        if bundle and not rp.endswith(f"/{bundle[:16]}.json"):
            errors.append(f"{rp}: named for bundle {bundle[:16]}")
        if bundle and author and bundle != bundle_id(t, author, entries):
            errors.append(f"{rp}: the bundle id is not the hash of its target, author and entries")
        if sorted(rep.get("entries") or []) != sorted(entries):
            errors.append(f"{rp}: `entries` are not the manifest's")
        pre = rep.get("preflight") if isinstance(rep.get("preflight"), dict) else {}
        if pre.get("compiled") != len(entries) or pre.get("entries") != len(entries):
            errors.append(
                f"{rp}: preflight must have compiled every entry ({pre.get('compiled')!r} of {pre.get('entries')!r}, {len(entries)} in the PR)"
            )
        rerated = {x.get("entry"): x.get("stars") for x in (rep.get("rerated") or []) if isinstance(x, dict)}
        for e, s in stars.items():
            if rerated.get(e) != s or not isinstance(s, int) or s < 4:
                errors.append(
                    f"{rp}: entry {e[:8]} is rated {s!r} in the manifest and {rerated.get(e)!r} by the intake job's own rating (it needs 4 or more, both)"
                )
        jin = rep.get("jinshi") if isinstance(rep.get("jinshi"), dict) else {}
        if jin.get("fail") != 0 or not isinstance(jin.get("checks"), list) or not jin["checks"]:
            errors.append(f"{rp}: Jinshi must have run (checks listed) and found no failure (fail: {jin.get('fail')!r})")
        rev = rep.get("review") if isinstance(rep.get("review"), dict) else {}
        verdicts = rev.get("verdicts") if isinstance(rev.get("verdicts"), list) else []
        if (
            not verdicts
            or rev.get("blocking") != 0
            or any(not isinstance(v, dict) or v.get("verdict") not in ("pass", "advisory") for v in verdicts)
        ):
            errors.append(f"{rp}: the reviewers must have given a verdict and none may block or reject (blocking: {rev.get('blocking')!r})")

    # the harness evidence of every theorem: friction against a script passed off as the harness, never proof (docs/leak-memory.md in compete-math)
    if rep:
        ev = rep.get("harness")
        if not isinstance(ev, list) or sorted(x.get("entry") if isinstance(x, dict) else "" for x in ev) != sorted(entries):
            errors.append(f"{rp}: `harness` must hold one evidence record per entry, the manifest's")
        else:
            for x in ev:
                tag = f"{rp}: harness of {str(x.get('entry'))[:8]}"
                ok_n, fail_n = x.get("verify_ok"), x.get("verify_fail")
                nums = [x.get(k) for k in ("ticket_age_s", "seconds", "verify_ok", "verify_fail", "searches", "attempts")]
                if any(not isinstance(n, int) or isinstance(n, bool) or n < 0 for n in nums):
                    errors.append(f"{tag}: counters must be whole numbers")
                    continue
                total_v = ok_n + fail_n
                if not isinstance(x.get("build"), str) or not SHA256.fullmatch(x["build"]) or x.get("build_verified") is not True:
                    errors.append(f"{tag}: the build must be a manifest id the server verified")
                elif not MIN_RUN_S <= x["ticket_age_s"] <= MAX_RUN_S:
                    errors.append(f"{tag}: the run's ticket is {x['ticket_age_s']} s old; a long-running effort is 30 minutes to 49 hours")
                elif x["seconds"] < MIN_RUN_S - 60 or abs(x["ticket_age_s"] - x["seconds"]) > max(300, 0.25 * x["ticket_age_s"]):
                    errors.append(f"{tag}: the receipt's time does not match the ticket's age")
                elif total_v < 10 or ok_n < 1 or not 0.02 <= fail_n / total_v <= 0.95:
                    errors.append(f"{tag}: the verification counts are not those of a prover run ({ok_n} passed, {fail_n} failed)")
                elif x["attempts"] < 1 or not isinstance(x.get("strategy"), str) or not MEMORY_STRATEGY.fullmatch(x["strategy"]):
                    errors.append(f"{tag}: not a memory strategy, or no attempt")

    # modules: the header, the namespace, the statement, the allow-list
    allowed_options = set(json.loads((ROOT / "schemas" / "allowed-options.json").read_text())["allowed"])
    command_keywords = set(json.loads((ROOT / "schemas" / "command-keywords.json").read_text())["commands"])
    total = 0
    for p in modules:
        try:
            text = show(p)
        except UnicodeDecodeError:
            errors.append(f"{p}: not valid UTF-8")
            continue
        total += len(text.encode())
        if len(text.encode()) > MAX_MODULE_BYTES:
            errors.append(f"{p}: {len(text.encode())} bytes (cap {MAX_MODULE_BYTES})")
        mod = module_name(p[: -len(LEAN)])
        lines = text.split("\n")
        code = code_only(text).split("\n")
        body = []
        for k, ln in enumerate(lines):
            m = IMPORT_LINE.match(code[k])
            if m and not TREE_IMPORT.match(m.group(1)):
                errors.append(f"{p}: imports {m.group(1)}, which is not the tree")
            body.append("" if m or MODULE_LINE.match(ln) else ln)
        opens = [k for k, ln in enumerate(code) if ln.strip() == f"namespace {mod}"]
        if len(opens) != 1 or [ln.strip() for ln in code if ln.startswith("namespace ")] != [f"namespace {mod}"]:
            errors.append(f"{p}: the declarations must be inside exactly one `namespace {mod}` and no other")
        last = [ln.strip() for ln in code if ln.strip()][-1:]
        if last != [f"end {mod}"]:
            errors.append(f"{p}: the last line must be `end {mod}`")
        if opens and any(IMPORT_LINE.match(code[k]) for k in range(opens[0] + 1, len(code))):
            errors.append(f"{p}: an import after the namespace opens")
        r = by_module.get(mod)
        if r and isinstance(r.get("statement"), str) and squash(r["statement"]) not in squash(text):
            errors.append(f"{p}: the manifest's statement is not what the module declares")
        for v in violations("\n".join(body), allowed_options, command_keywords)[:3]:
            errors.append(f"{p}: {v}")
    if total > MAX_TOTAL_BYTES:
        errors.append(f"{total} bytes of Lean (cap {MAX_TOTAL_BYTES})")
    if errors:
        fail("studied PR for " + t + ": " + "; ".join(errors[:12]) + (f"; and {len(errors) - 12} more" if len(errors) > 12 else ""))

    # the archive the intake job attested, rebuilt from this PR's files (scripts/ci/bundle_tar.py: the same function)
    if tar_out:
        # the intake job attested the modules as it built them, before their isnad tags existed (the autotag workflow writes them into the PR's branch,
        # docs/isnad.md "Born tagged"): the archive holds each module in its canonical form, which does not see tags, so the attestation covers the content and the
        # tags are judged apart (born_tagged.py offline, tag_verify.py against the build). The intake job builds its archive from the same function.
        members = {p: untagged(blob(head, p)) for p in modules}
        members["manifest.jsonl"] = manifest_new
        members["report.json"] = blob(head, rp)
        if any(v is None for v in members.values()):
            fail("a file of the bundle is not readable at the head")
        print(f"archive rebuilt: {tar_out} sha256 {write_tar(members, tar_out)}")
    print(f"studied ok: {t}: {len(modules)} theorems by {author}, bundle {bundle[:16]}")


def main() -> None:
    args = sys.argv[1:]
    if len(args) < 2:
        fail("usage: studied_check.py <base> <head> [--tar OUT.tar]")
    check(args[0], args[1], args[args.index("--tar") + 1] if "--tar" in args else "")


if __name__ == "__main__":
    main()
