# Jinshi — limiting the chance that a Lean 4 bug makes a theorem of Tengoku untrue

*Jinshi* (進士) was the degree of the highest imperial examination, the one most candidates failed. Here it is the name of the
tree's soundness tester: a set of independent examinations a module sits, each one aimed at a different way in which a
theorem the kernel accepted could still be false, or not the theorem its text appears to state. A module that passes every
examination of a round holds the Jinshi grade for that round.

Jinshi is **not** a style linter. The merge queue already refuses `sorry`, non-standard axioms, code that runs at compile time,
contradictory hypotheses, unresolved imports and leaked instances (docs/testing.md); the nightly independent check
re-types every declaration with nanoda. Jinshi examines what is left: the ways a *true-looking* theorem is not what it claims.

## 1. The threat model

A theorem `T` is in the tree, the pinned toolchain's kernel accepted its proof, and yet the mathematical claim a reader takes
`T` to make is false. Every way this can happen that we know of falls under one of five heads:

| Head | How a false claim survives | Examination |
|---|---|---|
| **K — the kernel or the artefacts** | a soundness bug in Lean's kernel; a declaration that reached the environment without the kernel (`addDeclWithoutChecking`, `debug.skipKernelTC`); a tampered or stale `.olean` the cache replays; compiled code trusted as proof (`native_decide`, `Lean.ofReduceBool`, `trustCompiler`, `implemented_by`, `extern`, `csimp`) | **tawatur**: every declaration re-checked by more than one kernel (`leanchecker`, the toolchain's own replay from a fresh environment; nanoda, independent Rust); the trusted-computing-base inventory |
| **E — elaboration** | the elaborated statement is not the statement the text reads as: an auto-bound implicit (the tree compiles with Lean's default `autoImplicit true`, so a typo in a statement becomes a universally quantified variable and the theorem claims less than it reads); a numeral or division that defaulted to `ℕ` (`1/2 = 0`); truncated `ℕ`/`ℤ` subtraction and division; `Real.sqrt`, `log`, `⁻¹` on arguments no hypothesis constrains | **fidelity**: each module of the round re-elaborated with `autoImplicit` and `relaxedAutoImplicit` off, every "unknown identifier" is a statement that was silently quantified; a scan of each elaborated statement for defaulted numerals, truncated arithmetic and junk-value functions |
| **N — names and notation** | a library declares `Nat.Prime`, `Real.sqrt`, `Finset.sum` in its own namespace and `open` makes its statements resolve to that one; a library redefines `∑`, `\|x\|`, `≤` by `notation`/`infix` (allowed in the `proposed` and `wide` lint modes) | **shadow**: every constant of a library whose name suffix is a name of the seed, and the theorems whose statements use it; every notation a library introduces whose token already has a meaning |
| **D — definitions** | the statement is about the library's own definitions and one of them is not what its name says: `def RiemannHypothesis : Prop := True`, a predicate that ignores its arguments, a structure with no fields, a `Decidable` instance that always says `isTrue` | **dossier**: for each theorem, the library-local definitions its statement depends on, printed, and those that are trivial flagged |
| **T — triviality** | the theorem is true but says nothing: its conclusion is one of its hypotheses, `True`, `a = a`, `p ↔ p` | **content**: the elaborated statement checked for these forms (vacuity, the dual, is the gate's) |

Heads K and E are where Lean's own behaviour, rather than an author's mistake, makes the claim false; they are the primary
goal, and the ones the existing gates do not cover. N, D and T are the ways an author (or a translation pipeline) produces a
true-looking theorem by accident, and they matter because an autonomous pipeline will do by accident what no person would
do on purpose.

## 2. The examinations

Each examination is independent, runs over a *round* of the tree (section 4), and writes one JSON line per finding:
`{"check": ..., "severity": "fail"|"warn"|"info", "module": ..., "name": ..., "line": ..., "detail": ...}`. `fail` is a
finding that, if confirmed, means a theorem is not what it claims; `warn` wants a reader; `info` is the dossier.

| Check | Program | What it does | Severity |
|---|---|---|---|
| `replay` | `scripts/jinshi/run.py` → `leanchecker <module>` | the toolchain's own kernel re-adds every declaration of the module to the environment of its imports: an `.olean` whose contents the kernel would not accept, or that bypassed the kernel, fails here | fail |
| `lean4lean` | `scripts/jinshi/run.py` → `lean4lean <module>` | the same replay by [lean4lean](https://github.com/digama0/lean4lean), a kernel written in Lean (derived from the C++ one, so not independent in design, but a second implementation); built by the workflow on the pinned toolchain with the Batteries commit the tree seeded | fail |
| `autoimplicit` | `scripts/jinshi/run.py` → `lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>` | re-elaborates the module with auto-bound implicits off; every `unknown identifier` names a statement in which Lean quantified a name the author never bound. A module that itself sets `autoImplicit true` is reported as opting in | fail |
| `tcb` | `TengokuJinshi.lean` | the trusted-computing-base inventory of the round: every `unsafe`, `partial`, `opaque`, `implemented_by`, `extern`, `axiom`, `initialize`, and every declaration whose type lives in the elaborator's monads; a theorem whose statement mentions one | warn (statement) / info (inventory) |
| `shadow` | `TengokuJinshi.lean` | a library constant whose name, minus any prefix, is a name the seed declares; the theorems of the library whose statements mention it | warn |
| `arith` | `TengokuJinshi.lean` | in the elaborated statements of a library's theorems: `ℕ`/`ℤ` subtraction and division, numerals typed `ℕ` next to `ℝ`/`ℚ`/`ℂ`, `Real.sqrt`/`Real.log`/`⁻¹`/`/` whose argument no hypothesis bounds (the seed is exempt: its lemmas state these operations deliberately, they are the foundation the rest builds on; a library's theorem meets them by accident) | warn |
| `dossier` | `TengokuJinshi.lean` | for each theorem of a library, the library-local constants its statement depends on, each printed; one that reduces to `True`/`False`, ignores its arguments, or is a structure without fields is flagged | fail (trivial) / info |
| `content` | `TengokuJinshi.lean` | a conclusion that is a hypothesis, `True`, `a = a`, `p ↔ p` | warn |
| `toolchain` | `scripts/jinshi/toolchain_watch.py` | Lean's own `soundness` and `runtime-soundness` issues against the pinned toolchain: each one's fix is an ancestor of the pinned tag or a backport on its release branch, or the toolchain has the bug; the snapshot is `tools/jinshi/lean-bugs.json` | fail (soundness) / warn (runtime) |
| `nanoda` | `.github/workflows/independent-check.yml` (exists) | the whole tree re-typed by a kernel that shares no code with Lean | fail |

Together `replay`, `lean4lean` and `nanoda` are the *tawatur* of kernels: a kernel bug would have to be shared by three
implementations before a false theorem survives them all. The fixture `tools/jinshi/fixtures/Forged.lean` shows why the replay
matters: it adds `forged : False := True.intro` to the environment under `debug.skipKernelTC`, the module compiles, and Lean's own
`#print axioms` reports that `forged` depends on no axioms, so an axiom check alone would trust it; leanchecker and lean4lean both
refuse the module, and the self-test requires that they do.

## 3. What Jinshi can and cannot promise

It lowers the probability that a Lean 4 bug, or an elaboration surprise, leaves a false claim in the tree; it does not make
it zero. A kernel bug shared by every checker survives; so does a statement that is exactly what its author meant and still
mathematically uninteresting. `fidelity` finds a quantified typo only when the module compiles without it: a typo that
happens to name a real constant is not found. The dossier shows a reader the definitions; it does not judge whether they
are the right ones.

## 4. Rounds

The tree is tested a tenth at a time, on the maintainer's word. `scripts/jinshi/partition.py` deals every module into ten
rounds, per seed topic and per library (a sub-folder of ten modules or more is a stratum of its own), and the deal is
frozen in `tools/jinshi/partition.tsv`, so a module keeps its round as the tree grows. Round 0 holds 874 of the 8,780
seed modules and 191 of the 1,889 translated ones. The tree's own programs and scripts are in every round. Only round 0 is
open; the next opens when the maintainer says so.

```bash
python3 scripts/jinshi/partition.py --round 0 --json round0.json    # the round's modules and the counts per stratum
```

## 5. Running

Local, no cache (the fixtures, against Lean's own library): `python3 scripts/jinshi/selftest.py` compiles
`tools/jinshi/fixtures/Cases.lean`, runs every examination on it and compares the findings with `expected.tsv`: every planted
fault must be found and nothing else reported; then `Forged.lean` must be refused by leanchecker (and by lean4lean when
`JINSHI_LEAN4LEAN` names its binary). This is what `pr-tests` runs when the recipe changes.

A round, on a built tree (the attested cache; this is what the `jinshi` workflow does in the sandbox):

```bash
scripts/cache.sh get && lake build Tengoku.All
lake build tengoku-jinshi
python3 scripts/jinshi/run.py --round 0 --out jinshi-out      # replay, autoimplicit and the environment checks; summary.md and *.jsonl
```

## 6. Status

Built (one file per examination under `Jinshi/`, with its own fixture and table under `tools/jinshi/fixtures/`): the partition, `tcb`, `shadow`, `arith`, `dossier`, `content`, `replay`, `lean4lean`, `autoimplicit`,
`toolchain`, the workflow. On 2026-10-07 the registry showed every `soundness` fix in the pinned `v4.34.0-rc2` (the July 2026 kernel fixes are its
ancestors; the two of 18 August are backports on its release branch) and two `runtime-soundness` fixes of September 2026 that it
lacks (reference-count overflow in the runtime, not the kernel: the next toolchain bump takes them).
Not yet: the per-module Jinshi grade as a tag; notation overloading under `shadow`; the dossier for the seed's own definitions.
