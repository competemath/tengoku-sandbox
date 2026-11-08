#!/usr/bin/env python3
"""nanoda.py — the fourth kernel of mutants.py's differential fuzzing (docs/jinshi.md, "mutants"): Nanoda
(github.com/ammkrn/nanoda_lib), an independent type checker written in Rust that shares no code with Lean's own
kernel or with lean4lean (both built against Lean's own data structures and `.olean` format). Nanoda never touches
an `.olean`: it reads a standalone dump of the proof term, lean4export's ndjson format — exactly the pair
`.github/workflows/independent-check.yml` already runs nightly over the whole tree; this module runs the same pair
per mutant instead, scoped to one module at a time.

Two prebuilt binaries, neither built here: building them is the sandbox CI's job (a Rust toolchain and
`cargo build --release` for nanoda; a second Lean package, `lake build`, for lean4export), and cannot be done or
verified from a contributor's own machine (CLAUDE.md: no local Lean builds). `.github/workflows/jinshi.yml` builds
both at pinned commits — the same commits `independent-check.yml` already uses — and exports:

  JINSHI_LEAN4LEAN     unchanged: a built digama0/lean4lean binary (mutants.py's third kernel)
  JINSHI_LEAN4EXPORT   a built leanprover/lean4export binary
  NANODA_BIN           a built ammkrn/nanoda_lib `nanoda_bin` binary

mutants.py's judge() adds the "nanoda" column only when NANODA_BIN is set (mirroring JINSHI_LEAN4LEAN for
lean4lean): neither variable set, nothing in this module ever runs, and the self-test's existing 3-kernel (or
2-kernel, without lean4lean) behaviour is unchanged.

Nat/String literals: nanoda's kernel-extension fast path for them is off by default and has no size cap, so the
config this module writes always sets `"nat_extension": true, "string_extension": true` — without it, ordinary
`Nat` arithmetic in a mutant's statement would make nanoda disagree with the other three kernels on nearly every
mutant that carries a literal, a false "fail" that has nothing to do with the mutation under test.

Trusted heads (native_decide and the compiler's word): a mutant whose export mentions `Lean.ofReduceBool`,
`Lean.ofReduceNat` or `Lean.trustCompiler` is SKIPPED, not judged — see `TRUSTED_HEADS` below for why.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# Lean's prelude declares these seven axioms in every environment (propext, Classical.choice, Quot.sound, sorryAx)
# or adds them when native_decide / the compiler's word stands in for a kernel reduction (Lean.ofReduceBool,
# Lean.ofReduceNat, Lean.trustCompiler). independent-check.yml already gives nanoda exactly this list for the whole
# tree (nanoda hard-errors on anything else: "unpermitted_axiom_hard_error": true); Jinshi/Forensics.lean's
# `trustedKind` names the same three compiler-trust axioms. Keep this list in that order and in sync with both.
PERMITTED_AXIOMS = [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "sorryAx",
    "Lean.ofReduceBool",
    "Lean.ofReduceNat",
    "Lean.trustCompiler",
]

# A declaration that rests on one of these never asked the kernel to check the thing it claims: the kernel took
# the compiler's word (native_decide) for a Bool or Nat answer and recorded that trust as an axiom application,
# not as a reduction. Lean's own kernel and lean4lean both run the SAME native reduceBool/reduceNat evaluator, so
# a mutation that changes what the compiled code would answer (while leaving the literal the proof asserts
# unchanged, or vice versa) is still caught by both of them. Nanoda has no such evaluator and never will: it only
# ever sees the axiom name on PERMITTED_AXIOMS and admits the application outright, exactly as it admits `sorryAx`.
# So nanoda would either spuriously REJECT every mutant descended from a native_decide-backed theorem (if the
# axiom were left off permitted_axioms — a configuration bug, not a finding) or spuriously ACCEPT a mutation that
# the other three kernels correctly refuse (a false "disagreement" the other way, since nanoda never re-evaluates
# the compiled code). Either way a mutant that touches a trusted head is not a fair test of nanoda as a judge: it
# is a known, pre-existing trust gap of the whole `native_decide` mechanism, not a bug this round is looking for.
# Skipped here, before nanoda ever runs, so it can never register as a "fail" (a disagreement) in mutants.py.
TRUSTED_HEADS = ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")

# the kernel did not get to judge (export or binary problem), vs. a genuine type error nanoda reported: an export
# nanoda could not even open, or a binary that is missing/not executable, is not a kernel disagreement.
NOT_RUN = ("No such file", "does not exist", "Permission denied", "cannot find", "No such process")


def _write_config(export_path: Path, config_path: Path) -> None:
    config_path.write_text(
        json.dumps(
            {
                "export_file_path": str(export_path),
                "use_stdin": False,
                "permitted_axioms": PERMITTED_AXIOMS,
                "unpermitted_axiom_hard_error": True,
                "num_threads": 1,
                "nat_extension": True,
                "string_extension": True,
                "print_success_message": True,
                "pp_to_stdout": True,
            },
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )


def nanoda_verdict(module: str, work_dir: Path, env: dict, timeout: int) -> tuple[str, str]:
    """accept | reject | timeout | error | skip (see TRUSTED_HEADS), and the tail of whichever step produced it.

    `env` must carry JINSHI_LEAN4EXPORT and NANODA_BIN (mutants.py's judge() only calls this when both are set,
    exactly like lean4lean's JINSHI_LEAN4LEAN) and the LEAN_PATH the other kernels already get, so `module` resolves
    (mutants.py's `_env`: the mutants' out_dir is already on it). `work_dir` holds this module's export and config
    (a subdirectory of out_dir, not out_dir itself: lean4export's output is not a module leanchecker should ever
    see on the same LEAN_PATH entry).
    """
    lean4export = env.get("JINSHI_LEAN4EXPORT", "")
    nanoda_bin = env.get("NANODA_BIN", "")
    if not lean4export or not nanoda_bin:
        return "error", "JINSHI_LEAN4EXPORT or NANODA_BIN is not set"
    work_dir.mkdir(parents=True, exist_ok=True)
    export_path = work_dir / f"{module}.export"
    try:
        r = subprocess.run(["lake", "env", lean4export, module], cwd=ROOT, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return "timeout", "lean4export timed out"
    if r.returncode or not r.stdout.strip():
        tail = " | ".join((r.stdout + r.stderr).strip().splitlines()[-3:])[:300]
        return "error", f"lean4export could not export {module} (exit {r.returncode}): {tail}"
    export_path.write_text(r.stdout, encoding="utf-8")
    if any(head in r.stdout for head in TRUSTED_HEADS):
        return "skip", "the export mentions a trusted head (native_decide or the compiler's word); see TRUSTED_HEADS above"
    config_path = work_dir / f"{module}.nanoda.json"
    _write_config(export_path, config_path)
    try:
        r = subprocess.run([nanoda_bin, str(config_path)], cwd=ROOT, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    text = (r.stdout + r.stderr).strip()
    tail = " | ".join(text.splitlines()[-3:])[:300]
    if r.returncode == 0:
        return "accept", tail
    if any(k in text for k in NOT_RUN):
        return "error", tail
    # unpermitted_axiom_hard_error: true (above) means an axiom outside PERMITTED_AXIOMS fails the run the same way
    # a genuine type error would; that is a configuration gap (this list is stale, or a mutation operator can
    # introduce a declared axiom — Jinshi/Mutants.lean's operators do not), not a kernel disagreement to report.
    # NOTE (unverified pending a first live CI run — docs/jinshi.md, "mutants"): nanoda's exact wording for this
    # case has not been observed yet; this heuristic may need the real phrase once one is.
    if "axiom" in text.lower() and ("not permit" in text.lower() or "unpermitted" in text.lower()):
        return "error", tail
    return "reject", tail
