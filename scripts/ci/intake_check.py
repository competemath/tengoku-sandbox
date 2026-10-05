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

An EXTEND PR (class `extend`) is the next part of a library that arrived in parts (competemath/emissary-archangel scripts/bump/bundle_layers.py: a library of thousands of
modules cannot be built by the queue in one PR, so it is cut into parts that each import only the seed and the parts before). It is recognised by the new file
data/intake/<library>/parts/NNN.json (the part's report) and gets the same checks on the part, and that it continues what is in the tree:

  shape       the library is in the tree already; new modules (A), the library's root file (M) and manifest (M), the part's report (A), nothing else, and Tengoku/All.lean untouched;
              NNN is the next part (the intake PR is part 1); a part has at most MAX_PART_MODULES modules
  root file   gains exactly one `import` line per new module and changes nothing else
  manifest    only gains lines (the tree's manifest is a byte prefix of the PR's); the new lines are checked as an intake manifest is, and their names are not the library's own either
  provenance  the part's archive: its modules, the root file, the new manifest lines and the report, as the factory built them

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

MAX_PART_MODULES = (
    400  # the queue builds a part inside its 40-minute check: about 3 seconds a module on a 4-core runner, measured on lean-pool
)
files = changed_files(base, head)
libs = {m.group(1) for _, p in files if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}
if len(libs) != 1:
    fail(f"an intake PR has exactly one data/intake/<library>/manifest.jsonl (found {sorted(libs)})")
lib = next(iter(libs))
ns = pascal(lib)
part_files = [p for _, p in files if re.fullmatch(rf"data/intake/{re.escape(lib)}/parts/\d{{3}}\.json", p)]
extending = bool(part_files)
if len(part_files) > 1:
    fail(f"an extend PR adds one part, not {len(part_files)}: {part_files}")
MANIFEST, UMBRELLA = f"data/intake/{lib}/manifest.jsonl", f"Tengoku/{ns}.lean"


def allowed_paths(p: str) -> bool:
    if extending:
        return p in (MANIFEST, UMBRELLA, part_files[0]) or (p.startswith(f"Tengoku/{ns}/") and p.endswith(".lean"))
    return p in (MANIFEST, f"data/intake/{lib}/report.json", UMBRELLA, ALL) or (p.startswith(f"Tengoku/{ns}/") and p.endswith(".lean"))


errors: list[str] = []
for st, p in files:
    if not allowed_paths(p):
        errors.append(f"{p}: not part of {lib}'s " + ("part" if extending else "bundle"))
    elif extending:
        want = "M" if p in (MANIFEST, UMBRELLA) else "A"
        if st != want:
            errors.append(f"{p}: an extend PR {'modifies' if want == 'M' else 'adds'} this file (status {st})")
    elif p != ALL and st != "A":
        errors.append(f"{p}: an intake PR only adds files (status {st}); a library already in the tree is not intaken again")
in_tree = bool(run("ls-tree", "--name-only", base, UMBRELLA, f"Tengoku/{ns}").strip())
if extending:
    # a part continues a library that is in the tree: its root file and manifest are there, and this is the next part (the intake PR was part 1)
    if not in_tree or blob(base, MANIFEST) is None:
        errors.append(f"{lib} is not in the tree (no Tengoku/{ns}.lean and manifest at base): an extend PR continues a library that is")
    done = [
        int(m.group(1))
        for q in run("ls-tree", "-r", "--name-only", base, f"data/intake/{lib}/parts").split("\n")
        if (m := re.search(r"/(\d{3})\.json$", q))
    ]
    wanted = max(done, default=1) + 1
    got = int(part_files[0][-8:-5])
    if got != wanted:
        errors.append(f"this is part {got:03d}, the next one is {wanted:03d}: parts merge in order")
else:
    # a library already in the tree is not intaken again: its root file or directory must not exist at base (new files under an
    # existing Tengoku/<Ns>/ are all status A, so the status check above does not see them)
    if in_tree:
        errors.append(f"{lib} is already in the tree (Tengoku/{ns} exists at base): a library is intaken once")
if len(files) > MAX_FILES:
    errors.append(f"{len(files)} files (cap {MAX_FILES}): split the bundle")


def show(path: str) -> str:
    """The blob as text; raises on a blob that is not UTF-8 (Lean source must be)."""
    return (blob(head, path) or b"").decode("utf-8")


# Tengoku/All.lean: exactly one new import line, nothing removed (an extend PR leaves it alone: the library is in it already)
all_diff = [ln for ln in run("diff", "-U0", f"{base}...{head}", "--", ALL).splitlines() if ln[:1] in "+-" and ln[:3] not in ("+++", "---")]
if not extending and all_diff != [f"+import Tengoku.{ns}"] and all_diff != [f"+public import Tengoku.{ns}"]:
    errors.append(f"{ALL} must gain exactly `import Tengoku.{ns}` and change nothing else (diff: {all_diff[:4]})")

# manifest
toolchain = (ROOT / "lean-toolchain").read_text().strip()
modules = {p for _, p in files if p.startswith(f"Tengoku/{ns}/")}
seen: set[str] = set()
manifest_new = b""  # an extend PR's new manifest lines, as bytes (the archive holds exactly these)
if extending:
    # the manifest only gains lines: the tree's is a byte prefix of the PR's, and what follows is the part's
    old_bytes, new_bytes = blob(base, MANIFEST) or b"", blob(head, MANIFEST) or b""
    if not new_bytes.startswith(old_bytes) or (old_bytes and not old_bytes.endswith(b"\n")):
        errors.append(
            "manifest.jsonl may only gain lines at its end: the tree's lines are changed or reordered, or the last one has no line break"
        )
        manifest_new = b""
    else:
        manifest_new = new_bytes[len(old_bytes) :]
    seen = {
        m.group(1) for m in re.finditer(r'"name":\s*"([^"]+)"', old_bytes.decode("utf-8", errors="replace"))
    }  # the library's own earlier theorems
try:
    manifest = [json.loads(ln) for ln in (manifest_new.decode("utf-8") if extending else show(MANIFEST)).splitlines() if ln.strip()]
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
if extending:
    # the part's report says which part it is, of which library; the root file gains an import per new module, and nothing else changes
    try:
        rep = json.loads(show(part_files[0]))
        if rep.get("part") != int(part_files[0][-8:-5]) or rep.get("library") != lib:
            errors.append(f"{part_files[0]} says part {rep.get('part')!r} of {rep.get('library')!r}")
    except Exception as e:  # noqa: BLE001
        errors.append(f"{part_files[0]} is not a JSON report: {e}")
    new_mods = sorted(
        p[: -len(".lean")].replace("/", ".") for p in (q for _, q in files) if p.startswith(f"Tengoku/{ns}/") and p.endswith(".lean")
    )
    if len(new_mods) > MAX_PART_MODULES:
        errors.append(f"{len(new_mods)} modules in one part (cap {MAX_PART_MODULES}): cut the bundle into smaller parts")
    norm = lambda ln: re.sub(r"^\s*public\s+", "", ln.strip())  # noqa: E731
    wanted_lines = {f"import {m}" for m in new_mods}
    head_lines = show(UMBRELLA).split("\n")
    if sorted(norm(ln) for ln in head_lines if norm(ln) in wanted_lines) != sorted(wanted_lines):
        errors.append(f"{UMBRELLA} must import each new module exactly once")
    if [ln for ln in head_lines if norm(ln) not in wanted_lines] != (blob(base, UMBRELLA) or b"").decode("utf-8").split("\n"):
        errors.append(f"{UMBRELLA} may only gain the imports of the new modules")
if not manifest:
    errors.append(
        "the manifest has no theorem: " + ("a part that carries none is empty" if extending else "a bundle that carries none is empty")
    )
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
    fail(
        f"{'extend' if extending else 'intake'} PR for {lib}: "
        + "; ".join(errors[:12])
        + (f"; and {len(errors) - 12} more" if len(errors) > 12 else "")
    )

# the archive the factory attested, rebuilt from this PR's files (scripts/ci/bundle_tar.py: the same function as the factory's)
if tar_out:
    members = {}
    for _, p in files:
        if p == ALL:
            continue
        raw = blob(head, p)  # the blob's own bytes: text mode would turn CRLF into LF and choke on invalid UTF-8
        if raw is None:
            fail(f"{p} is not readable at {head}")
        if extending and p == MANIFEST:
            raw = manifest_new  # the part's archive holds its own lines only
        members["report.json" if extending and p == part_files[0] else p.split("/", 3)[3] if p.startswith("data/intake/") else p] = raw
    print(f"archive rebuilt: {tar_out} sha256 {write_tar(members, tar_out)}")
if extending:
    print(f"extend ok: {lib}: part {part_files[0][-8:-5]}, {len(modules)} modules, {len(manifest)} theorems, lint {lint_mode}")
else:
    print(f"intake ok: {lib}: {len(modules)} modules, {len(manifest)} theorems, lint {lint_mode}")
