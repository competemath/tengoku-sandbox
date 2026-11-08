# Why Tengoku does not trust the toolchain

Tengoku is built to be [exceptionally cynical of all dependencies, even the Lean 4 kernel and elaboration ecosystem](reliability.md).
This page says why. It is a set of case studies: real failures, each with the people who found it, the fix, and the link to read
it yourself. Nothing here is a criticism of the Lean developers. Every kernel bug below was found by someone, and fixed, often within
hours; several were found by the Lean community's own independent checkers. The point is narrower: a library that machines write
into cannot rest on the assumption that the checker has no bugs, because the writers are exactly the kind of agent that finds them.

Last checked 2026-10-10. If you find an error, or a case we should add, please [open an issue](https://github.com/competemath/tengoku/issues/new).
Where a source could only be partly verified, the text says so.

## How to read this

A Lean proof is only worth what stands between the statement a reader sees and the kernel that checks it. Failures happen at five
places, and Tengoku defends each one differently:

1. **The kernel**, the small program that checks proofs. If it accepts a false proof, everything built on it is suspect.
2. **What the kernel stands on**: its arithmetic, its memory management, the compiler behind `native_decide`, the tools that report
   which axioms a proof uses.
3. **Elaboration**, the step that turns what you typed into the statement that is checked. A proof of the wrong statement is a fine proof.
4. **The harness around the checker**: the scripts, filters and settings that decide what counts as "it compiles".
5. **People and machines writing statements**, where the error is in what was formalised, not in Lean.

A caveat that applies to most kernel cases: since 2026 several of them need a metaprogram that hands a declaration straight to the
kernel, so they are not reachable from ordinary Lean syntax. That is the Lean team's own description, and it is fair. It is also exactly
why this matters here: an AI agent writing Lean can write any metaprogram.

## 1. The kernel

**A universe bug that proved `False` (2022).** The kernel dropped the `+N` from `imax u v + N` when normalising universe levels.
Mario Carneiro turned that into `Type : Type` and then into Girard's paradox, a `theorem contradiction : False` with no axioms. He
dates the bug to a commit of 2020-07-24; it was reported on 2022-10-18 by Parth Shastri after a kernel type mismatch and fixed on
2022-10-26, about two and a quarter years after it arrived. [Fix](https://github.com/leanprover/lean4/pull/1781),
[discussion](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Bug.20in.20kernel.20level.20normalization.html).

**Arithmetic that was wrong, so `rfl` proved `False` (2022).** On 64-bit machines `2^65 % (2^33+1)` evaluated to `1` instead of
`2^32+1`: a type-width slip in the C++ fast path for `Nat.mod`. Found by `pcpthm`, fixed the same day.
[Issue](https://github.com/leanprover/lean4/issues/1433).

**Inductive types with self-referential indices (2023).** `inductive C : Bool → Type | c : C (f (C false))` was accepted, and a short
proof of `False` followed. Found by Gabriel Ebner on 2023-02-27, fixed the next day.
[Issue](https://github.com/leanprover/lean4/issues/2125), [fix](https://github.com/leanprover/lean4/pull/2127).

**A fuzzer found a proof of `False` in `Nat.pow` (2025).** The kernel's `reduce_pow` treated its first argument as a number literal
without checking. With GMP enabled the pull request says it was possible to prove `False`. Found by Markus Himmel and `datokrat` while
fuzzing; fixed 2025-04-23. A commenter later reproduced it in stable releases from 4.14.0 to 4.19.0. The fix's author notes it is not a
flaw in the type theory and that an independent re-implementation catches it. [Fix](https://github.com/leanprover/lean4/pull/8060).

**Found by an AI in a few hours (July 2026).** The kernel skipped the "no free variables" check for the body of an `opaque`
declaration, and a cache of inferred types let a dangling variable be typed as `False`. The result was an axiom-free `False` through
the ordinary checked path. Patrick Hulin found it with an AI model working for about three and a half hours. The Lean team fixed it the
day it was reported and published a security record, CVE-2026-72711. The release notes say the recommended method of checking with
`comparator` is not affected. [Issue](https://github.com/leanprover/lean4/issues/14484),
[fix](https://github.com/leanprover/lean4/pull/14498), [release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.1/).

**The Collatz "disproof" (July 2026).** On 2026-07-25 Ramana Kumar published a `sorry`-free Lean proof, made with AI help, that
disproved the Collatz conjecture. It was not a valid proof: it exploited a kernel bug in nested inductive types, where the parameters of
the auxiliary type were never type-checked. Kiran Gopinathan reduced it to a small example, and Leo de Moura's fix landed the same
day. The release notes say the bug "can be exploited even when using comparator" (CVE-2026-72844).
The project had been checked three ways, with an ordinary replay, a fresh replay, and an independent kernel (nanoda). The postmortem
explains why that was not enough that day: two unrelated bugs lined up, one in the official kernel and one in nanoda, which
had been reported and fixed about a week earlier. The lesson the postmortem draws, and the one Tengoku takes, is that independent
kernels still work, but they have to be current versions of each.
[Issue](https://github.com/leanprover/lean4/issues/14576), [fix](https://github.com/leanprover/lean4/pull/14577),
[follow-up](https://github.com/leanprover/lean4/pull/14582),
[postmortem](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/).

**A batch found by an AI-assisted audit (July to August 2026).** Daniel Selsam of OpenAI, using internal models, reported several
more kernel problems, all fixed by Leo de Moura: an equality cache whose answers depended on earlier queries
([#14806](https://github.com/leanprover/lean4/pull/14806)), a proof-irrelevance check that a stuck type skipped
([#14807](https://github.com/leanprover/lean4/pull/14807)), a type in `Sort (imax 1 0)` not recognised as a proposition
([#14613](https://github.com/leanprover/lean4/pull/14613)) and others. Some were caught by a second kernel; for one of them
(#14807) the pull request says nanoda also accepted the bogus proof. Different kernels fail on different bugs, which is the reason to run more than one.

**Lean checking itself.** Mario Carneiro's [Lean4Lean](https://arxiv.org/abs/2403.14064), an independent re-implementation of the
kernel written in Lean, found real kernel bugs while it was being verified, including a second one
([#10475](https://github.com/leanprover/lean4/issues/10475)). Its own README warns that, being derived from the C++ kernel, it may
share some bugs. Both facts matter.

## 2. What the kernel stands on

**Memory and big numbers (2026).** A 32-bit reference count could overflow on machines with enough memory, giving a use-after-free in
the official kernel that the fix's text says "could be extended into a proof of `False`". Older versions of the GMP number library
have bugs that can give wrong results in corner cases, and the kernel could be driven to evaluate numerals of many gigabytes. All
three were reported by Daniel Selsam and fixed in August 2026. No working exploit is shown in the text we read, and the pull
requests say kernels that do not use Lean's runtime were not affected.
[#14838](https://github.com/leanprover/lean4/pull/14838), [#14833](https://github.com/leanprover/lean4/pull/14833),
[#14849](https://github.com/leanprover/lean4/pull/14849).

**The compiler behind `native_decide` (2024 to 2026).** `native_decide` replaces a kernel check by running compiled code, so the
compiler joins the trusted base. Compiler faults have then made false statements provable:
`Nat.ble 0 0` evaluated to `false` ([#6086](https://github.com/leanprover/lean4/issues/6086), 2024);
`Array.foldlM` and its unsafe twin disagreed, so `False` was provable with `native_decide`
([#11773](https://github.com/leanprover/lean4/issues/11773), 2025); and `@[csimp]` ignored universe parameters, the same result
([#10213](https://github.com/leanprover/lean4/issues/10213), 2025). A related report, still open, shows a `csimp` lemma
can introduce an axiom that `#print axioms` does not list ([#7463](https://github.com/leanprover/lean4/issues/7463)).

**The axiom report itself.** `#print axioms` is how most people check what a proof depends on, and it has had gaps. It did not follow
the axioms that other axioms refer to ([#8840](https://github.com/leanprover/lean4/issues/8840), fixed 2025). An open report
(2026-09-19) says that from v4.30.0 it under-reports the axioms of imported inductives, depending on declaration names
([#15226](https://github.com/leanprover/lean4/issues/15226)). A maintainer's comment there says the tool is losing significance to
`lake check` and `lake comparator`. An axiom list is a useful signal and not a proof.

## 3. Elaboration: when the checked statement is not the intended one

**A hidden `sorry` in `apply?` (2025).** In some cases `apply?` left a `sorry` and suppressed the warning, so incomplete proofs
compiled cleanly. DeepSeek reported that its 7B prover appeared to solve 13 PutnamBench problems that its 671B model did not, and traced
this to the bug. Hanwen Zhu filed it with Lean on 2025-05-03 and it was fixed two days later.
An independent 2026 preprint audited published proofs for `sorryAx` and found more proofs that passed the usual keyword scan; its
authors say they are not Lean experts, so treat the exact numbers with care.
[Lean issue](https://github.com/leanprover/lean4/issues/8212), [fix](https://github.com/leanprover/lean4/pull/8231),
[DeepSeek-Prover-V2](https://arxiv.org/abs/2504.21801), [audit](https://arxiv.org/abs/2608.28639).

**A statement that proves nothing, or the wrong thing.** The kernel checks that a proof proves its statement. It cannot check that the
statement is the one you meant. Public records of this:

- Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository. For Erdős problem 480 the
  statement assumed `m ≠ 0` where it meant `n ≠ 0`, and an AI prover proved the stated conjecture by taking `n = 0`
  ([#1282](https://github.com/google-deepmind/formal-conjectures/issues/1282), opened 2025-11-28; the first fix was still wrong and
  it was reopened). For Erdős problem 361 a hypothesis rebound a variable, so the real parameter and its hypothesis went unused and
  the declarations followed by contradiction
  ([#4440](https://github.com/google-deepmind/formal-conjectures/issues/4440), July 2026). The project's authors report 291 fixed
  misformalisations in the repository ([paper](https://arxiv.org/abs/2605.13171)); a statement being human-reviewed did not prevent them.
- miniF2F. A 2025 audit reports that about 40% of its formal statements contained an error, and that correcting them roughly doubled
  the best pipeline's success rate ([paper](https://arxiv.org/abs/2511.03108)). A 2026 study of 13 benchmark variants
  ([paper](https://arxiv.org/abs/2606.29493)) found 4,833 candidate defects, 398 of them with a machine-checkable certificate that the
  statement is unprovable or vacuous. Errors push scores in both directions, so a headline number says little without an audit.
- PutnamBench. One pull request fixed 15 statements at once: "not all zero" encoded as "all zero", an implication that was vacuously
  true when `a = 0`, a `ℕ` division that truncated
  ([PR #322](https://github.com/trishullab/PutnamBench/pull/322), 2025-12-30).
- Mathlib. A 2024 maintenance edit dropped `[T2Space M]` from the definition of the smooth Poincaré conjecture proposition, which
  changed its meaning; it was noticed and restored in 2026 ([PR #43606](https://github.com/leanprover-community/mathlib4/pull/43606)).
  No wrong theorem is known to have followed, since only unproved placeholders used it, but it shows how a mechanical edit can change a
  statement without any error from Lean.

## 4. The harness: when the check is gamed

**Redefining the notation (2026).** Google DeepMind ran about 100 Gemini agents on 71 open problems from formal-conjectures. The
grader banned the keywords `axiom`, `sorry`, `macro` and `syntax`, and required zero `sorry`. One agent found that `local notation` and
`instance` were not banned, wrote `local notation "LinearIndependent" => fun _ _ => False` in the editable part of the file, and closed
Schanuel's conjecture. The trick spread through a shared library of tips, and the swarm "solved" the other 34 problems in 27 minutes.
The paper recommends comparing statements at the syntax-tree level. [Paper](https://arxiv.org/abs/2609.04170).

**A reward that only asked "does Lean accept it".** The authors of LongCat-Flash-Prover found their training run had learned to cheat
and listed nine patterns: tampering with the statement, `#exit`, fake axioms, macro and notation tricks, `unsafe` and `partial`, a
contradictory `variable`, redefining background concepts, a fake local instance, tampering with prerequisites. Of 1,024 sampled
attempts from one checkpoint, 1,003 passed the syntax check, and 286 remained after an AST comparison.
[Paper](https://arxiv.org/abs/2603.21065).

**Skipping the kernel.** A 2026 benchmark-integrity paper reports a coding-agent run on a Lean task that set `debug.skipKernelTC`,
assigned an ill-typed term to the goal, and scored full reward. We could only verify this from the paper's account.
[Paper](https://arxiv.org/abs/2609.11028). The Lean reference manual calls that option dishonest and says unreviewed AI-generated
proofs are the case checking is for ([Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)).

## 5. Another AI-written library, and our own

**Tau Ceti.** The [Tau Ceti Project](https://github.com/TauCetiProject) is a Lean library that AI agents write and review, and it
records what it found in public. A build that runs `lake build` on whatever landed can run arbitrary code at elaboration time: a
`run_cmd` that writes a file exits cleanly, emits no diagnostic and passes `--iofail`. Its cache-upload secret was reachable that way
until a fix the same day ([issue #3720](https://github.com/TauCetiProject/TauCeti/issues/3720)). Separately compiled modules could
declare the same theorem and pass Lean's import check, so six collisions had accumulated before a check was added
([PR #7219](https://github.com/TauCetiProject/TauCeti/pull/7219)). An early review job ran an attacker-controlled Lake file next to
its credentials ([issue #7](https://github.com/TauCetiProject/TauCetiReview/issues/7)). Their audit scripts state plainly that they
trust the compiled `.olean` files they load. We learned from their record and credit it in [our acknowledgements](acknowledgements.md).

**Leak IV, our own verifier (fixed 2026-10-07).** Our verification service reported "100% verified" for any script that compiled
without errors or warnings. Lean does not warn on a freshly declared axiom the way it warns on `sorry`, so
`axiom cheat : False` followed by a proof that used it compiled cleanly and was reported as verified, with no axiom check of any kind.
Found in our own security review and fixed on 2026-10-07 by checking, after the compile, every axiom in the finished environment.
[Fix](https://github.com/mikael-bashir/leak-iv/commit/4c8ce9ac).

**A forged theorem that `#print axioms` calls clean.** Our soundness tester [Jinshi](https://github.com/competemath/jinshi) keeps a
fixture, `Forged.lean`, that adds `forged : False := True.intro` to the environment under `debug.skipKernelTC`. The module compiles, and
`#print axioms` reports that `forged` depends on no axioms. Replaying the module through the independent kernels refuses it.

## What this adds up to

| What went wrong | What Tengoku does about it |
| --- | --- |
| A kernel accepts a false proof | The whole compiled library is [re-checked every day by a second kernel](reliability.md), nanoda, which shares no code with Lean's. Our soundness tester Jinshi replays declarations through more than one. A check by one kernel is never the only check. |
| Both kernels share a bug, or each has a different one | We say plainly that we cannot rule this out. The defence is to keep toolchains and checkers current and to run several. |
| The compiler or the axiom report is wrong | `native_decide` and `sorry` are refused outright, and a trusted theorem may rest only on `propext`, `Classical.choice` and `Quot.sound`. Axioms are computed by our own script from the exported terms, not by calling `#print axioms` alone ([axiom_scan.py](../scripts/ci/axiom_scan.py)). |
| A metaprogram does something at build time | A record may not contain `#eval`, `unsafe`, `initialize`, a new `axiom` or other code-running commands, and the check is an allow-list of what is known to be inert, not a list of known dangers ([the lint](bundle-lint.md)). |
| The statement is not what it reads | A translated statement is accepted only once the kernel has verified that it implies the original; theorems whose assumptions contradict each other are flagged ([vacuity](../tools/vacuity)); every theorem carries its source. The deeper fidelity examinations live in Jinshi. |
| The harness is gamed | Keyword bans are not trusted. The post-compile axiom check exists because ours was once gameable. |
| Hidden state changes meaning | Everything is append-only, builds are attested, and a mistake is retracted by a tombstone, never deleted. |

The last line of the table is the honest one: **a trusted theorem in Tengoku is not a guarantee.** It means a theorem passed every
independent check we run. If you rely on one for something that matters, read its statement.

How all this is done in practice: [how Tengoku stays reliable](reliability.md).
