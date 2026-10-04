#!/usr/bin/env python3
"""intake_check.py <base> <head> [--lint strict|proposed] [--tar OUT.tar] — the checks of an INTAKE PR.

An intake PR carries a factory bundle (competemath/emissary-archangel, scripts/bump): the Lean modules of ONE library that was not in the
tree, cut down to what the factory verified (Gate 2: each theorem's statement entails the original's, kernel-checked; no sorry, no
axioms beyond the three), a manifest of those theorems, and the library's import line in Tengoku/All.lean. This runs no Lean. It checks, from the PR's
git objects only:

  shape       one library; only its modules, its root file, its manifest and report, and ONE added line in Tengoku/All.lean; every file is
              new (a library already in the tree is not intaken again); size caps
  manifest    one JSON line per theorem: name, statement, module, library, toolchain (= lean-toolchain), module = a file of the PR, names unique
              and not already a trusted record of the tree or a theorem of an intake bundle in it
  lint        every module passes the content allow-list (scripts/ci/allowlist.py: known-inert commands, attributes, options; no code that
              runs while compiling) after its header; the header may only import the tree (Tengoku.*) and Lean/Std/Init.
              `--lint proposed` additionally allows notation commands (notation, infix, prefix, postfix, notation3, scoped, local)
  provenance  with --tar, the bundle archive is rebuilt from the PR's files (the factory's own reproducible tar) for the workflow to
              check against the factory's build attestation: the bytes the factory built are the bytes in this PR

What is NOT checked here is the Lean itself: the merge queue builds the library (sealed), and checks axioms of every theorem.
"""

from __future__ import annotations

import json
import re
import sys

from _git import ROOT, blob, changed_files, fail, pascal, run
from allowlist import violations
from bundle_tar import write_tar

args = sys.argv[1:]
base, head = args[0], args[1]
lint_mode = args[args.index("--lint") + 1] if "--lint" in args else "strict"
tar_out = args[args.index("--tar") + 1] if "--tar" in args else ""
MAX_FILES, MAX_BYTES = 20000, 400 * 1024 * 1024
ALL = "Tengoku/All.lean"
NOTATION_OK = re.compile(r"`(?:notation3?|infix[lr]?|prefix|postfix|scoped|local)`")
IMPORT_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$")
MODULE_LINE = re.compile(r"^\s*(?:module|prelude)\s*$")
TREE_IMPORT = re.compile(r"(?:Tengoku|Lean|Std|Init)(?:\.|$)")

files = changed_files(base, head)
libs = {m.group(1) for _, p in files if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}
if len(libs) != 1:
    fail(f"an intake PR has exactly one data/intake/<library>/manifest.jsonl (found {sorted(libs)})")
lib = next(iter(libs))
ns = pascal(lib)


def allowed_paths(p: str) -> bool:
    return p in (f"data/intake/{lib}/manifest.jsonl", f"data/intake/{lib}/report.json", f"Tengoku/{ns}.lean", ALL) or (
        p.startswith(f"Tengoku/{ns}/") and p.endswith(".lean")
    )


errors: list[str] = []
for st, p in files:
    if not allowed_paths(p):
        errors.append(f"{p}: not part of {lib}'s bundle")
    elif p != ALL and st != "A":
        errors.append(f"{p}: an intake PR only adds files (status {st}); a library already in the tree is not intaken again")
# a library already in the tree is not intaken again: its root file or directory must not exist at base (new files under an
# existing Tengoku/<Ns>/ are all status A, so the status check above does not see them)
if run("ls-tree", "--name-only", base, f"Tengoku/{ns}.lean", f"Tengoku/{ns}").strip():
    errors.append(f"{lib} is already in the tree (Tengoku/{ns} exists at base): a library is intaken once")
if len(files) > MAX_FILES:
    errors.append(f"{len(files)} files (cap {MAX_FILES}): split the bundle")


def show(path: str) -> str:
    """The blob as text; raises on a blob that is not UTF-8 (Lean source must be)."""
    return (blob(head, path) or b"").decode("utf-8")


# Tengoku/All.lean: exactly one new import line, nothing removed
all_diff = [ln for ln in run("diff", "-U0", f"{base}...{head}", "--", ALL).splitlines() if ln[:1] in "+-" and ln[:3] not in ("+++", "---")]
if all_diff != [f"+import Tengoku.{ns}"] and all_diff != [f"+public import Tengoku.{ns}"]:
    errors.append(f"{ALL} must gain exactly `import Tengoku.{ns}` and change nothing else (diff: {all_diff[:4]})")

# manifest
toolchain = (ROOT / "lean-toolchain").read_text().strip()
modules = {p for _, p in files if p.startswith(f"Tengoku/{ns}/")}
seen: set[str] = set()
try:
    manifest = [json.loads(ln) for ln in show(f"data/intake/{lib}/manifest.jsonl").splitlines() if ln.strip()]
except Exception as e:  # noqa: BLE001
    manifest = []
    errors.append(f"manifest.jsonl is not JSON lines: {e}")
# what is in the tree: the trusted records and the theorems of the intake bundles already merged. Staging and tentative records are not
# built into the tree (the generator renames a clash when one is promoted), so a name they share with this bundle proves nothing
existing: set[str] = set()
tree_files = [
    f
    for tier in ("trusted", "intake")
    for f in (ROOT / "data" / tier).glob("**/*.jsonl")
    if f.stem != lib and f.parent.name != lib  # the library's own records are what this bundle translates
]
for f in tree_files:
    for m in re.finditer(r'"name":\s*"([^"]+)"', f.read_text(errors="replace")):
        existing.add(m.group(1))
if not manifest:
    errors.append("the manifest has no theorem: a bundle that carries none is empty")
for i, r in enumerate(manifest, 1):
    where = f"manifest line {i}"
    if not isinstance(r, dict):
        errors.append(f"{where}: not a JSON object")
        continue
    for k in ("name", "statement", "module", "library", "toolchain"):
        if not isinstance(r.get(k), str) or not r[k].strip():
            errors.append(f"{where}: `{k}` missing")
    if r.get("library") != lib:
        errors.append(f"{where}: library {r.get('library')!r}, expected {lib!r}")
    if r.get("toolchain") != toolchain:
        errors.append(f"{where}: toolchain {r.get('toolchain')!r}, the tree is on {toolchain!r}")
    mod = r.get("module")
    if not isinstance(mod, str) or f"{mod.replace('.', '/')}.lean" not in modules:
        errors.append(f"{where}: module {mod} is not a file of this PR")
    name = r.get("name") if isinstance(r.get("name"), str) else ""  # a non-string name was reported above; it is never hashed
    if name in seen:
        errors.append(f"{where}: {name} twice")
    seen.add(name)
    # a record's name is the declaration as written in its file (inside `namespace X`, `theorem foo` is stored as `foo`; `hφ₀` as `h`): a bare
    # bundle name equal to one proves nothing about the real names; only a qualified name is compared (the merge queue's build decides the rest)
    if "." in name and name in existing:
        errors.append(f"{where}: {name} is already a trusted record or a bundle theorem of the tree (a bundle must not declare it again)")

# lint
allowed_options = set(json.loads((ROOT / "schemas" / "allowed-options.json").read_text())["allowed"])
total = 0
for p in sorted(p for _, p in files if p.endswith(".lean") and p != ALL):
    try:
        text = show(p)
    except UnicodeDecodeError:
        errors.append(f"{p}: not valid UTF-8")
        continue
    total += len(text)
    body = []
    for ln in text.split("\n"):
        m = IMPORT_LINE.match(ln.split("--", 1)[0])  # a comment after the module name is part of the line
        if m and not TREE_IMPORT.match(m.group(1)):
            errors.append(f"{p}: imports {m.group(1)}, which is not the tree")
        body.append("" if m or MODULE_LINE.match(ln) else ln)
    vs = violations("\n".join(body), allowed_options)
    if lint_mode == "proposed":
        vs = [v for v in vs if not NOTATION_OK.search(v)]
    for v in vs[:3]:
        errors.append(f"{p}: {v}")
if total > MAX_BYTES:
    errors.append(f"{total} bytes of Lean (cap {MAX_BYTES})")
if errors:
    fail(f"intake PR for {lib}: " + "; ".join(errors[:12]) + (f"; and {len(errors) - 12} more" if len(errors) > 12 else ""))

# the archive the factory attested, rebuilt from this PR's files (scripts/ci/bundle_tar.py: the same function as the factory's)
if tar_out:
    members = {}
    for _, p in files:
        if p == ALL:
            continue
        raw = blob(head, p)  # the blob's own bytes: text mode would turn CRLF into LF and choke on invalid UTF-8
        if raw is None:
            fail(f"{p} is not readable at {head}")
        members[p.split("/", 3)[3] if p.startswith("data/intake/") else p] = raw
    print(f"archive rebuilt: {tar_out} sha256 {write_tar(members, tar_out)}")
print(f"intake ok: {lib}: {len(modules)} modules, {len(manifest)} theorems, lint {lint_mode}")
