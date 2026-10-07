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
| `reproduce` | `scripts/jinshi/run.py` (the same re-elaboration) | the re-elaborated module's `.olean` compared byte for byte with the one the attested cache ships: a difference is a compiled artefact that is not what the source gives (tampering, a stale cache, or a non-reproducible compile) | warn |
| `autoimplicit` | `scripts/jinshi/run.py` → `lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>` | re-elaborates the module with auto-bound implicits off; every `unknown identifier` names a statement in which Lean quantified a name the author never bound. A module that itself sets `autoImplicit true` is reported as opting in | fail |
| `tcb` | `TengokuJinshi.lean` | the trusted-computing-base inventory of the round: every `unsafe`, `partial`, `opaque`, `implemented_by`, `extern`, `axiom`, `initialize`, and every declaration whose type lives in the elaborator's monads; a theorem whose statement mentions one | warn (statement) / info (inventory) |
| `shadow` | `TengokuJinshi.lean` | a library constant whose name, minus any prefix, is a name the seed declares; the theorems of the library whose statements mention it | warn |
| `nearname` | `TengokuJinshi.lean` | a library constant whose name is almost a seed name: a character that reads as an ASCII letter or digit but is not one, or an invisible one (fail); a suffix of the name that is a seed name once case, primes, underscores and trailing digits are ignored, or one edit away from a seed name of the same namespace (warn); the theorems of the library whose statements use such a name | fail (homoglyph) / warn |
| `arith` | `TengokuJinshi.lean` | in the elaborated statements of a library's theorems: `ℕ`/`ℤ` subtraction and division, numerals typed `ℕ` next to `ℝ`/`ℚ`/`ℂ`, `Real.sqrt`/`Real.log`/`⁻¹`/`/` whose argument no hypothesis bounds (the seed is exempt: its lemmas state these operations deliberately, they are the foundation the rest builds on; a library's theorem meets them by accident) | warn |
| `dossier` | `TengokuJinshi.lean` | for each theorem of a library, the library-local constants its statement depends on, each printed; one that reduces to `True`/`False`, ignores its arguments, or is a structure without fields is flagged | fail (trivial) / info |
| `content` | `TengokuJinshi.lean` | a conclusion that is a hypothesis, `True`, `a = a`, `p ↔ p` | warn |
| `duplicate` | `TengokuJinshi.lean` | the same statement proved twice: every theorem of the environment is indexed by its elaborated statement with binder names and universe parameter names erased (the identity of docs/isnad.md, without its hash), and each theorem of the round is looked up; a library's theorem that proves again what the seed already has, or what the same library already has, is a warning; two libraries (or the seed twice) proving one statement is *tawatur*, several proofs of one claim | warn (seed, same library) / info (tawatur) |
| `instdrift` | `TengokuJinshi.lean` | for each theorem (the seed included), every instance-implicit argument of its elaborated statement is compared with what instance synthesis returns in the environment of the run: the tree is one environment that keeps growing, and a module compiled later (a library, or the seed itself) that registers a global instance of the same class makes the same statement text elaborate to a different term (another norm, order, decidability), so the theorem, true for the instance it was proved with, no longer applies to what a reader now writes; a class for which no instance is found today is reported once per theorem | warn (a different instance today) / info (none today) |
| `unusedhyp` | `TengokuJinshi.lean` | a propositional hypothesis in a theorem's statement (a named binder, not a variable or an instance) that the proof term never mentions, and that no later binder's type nor the conclusion mentions: the theorem holds without it, the statement promises less than was proved (the seed included: this examines proofs, not statements; a `sorry` is skipped) | warn |
| `options` | `scripts/jinshi/run.py` (text, no Lean) | a module's `set_option` lines: a heartbeat or recursion limit raised above the default or set to no limit (the module compiles only with extra budget: fragile under any toolchain change), a `debug.*` option, `autoImplicit true`, a linter switched off | warn / info |
| `roundtrip` | `TengokuJinshi.lean` | what the reader sees against what the kernel checked: each theorem's statement is printed as a reader sees it (the default options, full names), read back as a term, re-elaborated as a type with auto-bound implicits off, and compared with the elaborated statement by `isDefEq`; the seed is examined too. A text that does not parse (a private or hygienic name shown as `x✝`) or does not elaborate (a proof shown as `⋯`) is reported; one that elaborates to a different statement (a notation that hides an argument, an invisible coercion, an instance that resolves differently, a numeral whose type the text does not show) is the finding, with both statements printed | warn (different) / info (unreadable, universes only) |
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

Built (one file per examination under `Jinshi/`, with its own fixture and table under `tools/jinshi/fixtures/`): the partition, `tcb`, `shadow`, `arith`, `dossier`, `content`, `instdrift`, `replay`, `lean4lean`, `autoimplicit`,
Built (one file per examination under `Jinshi/`, with its own fixture and table under `tools/jinshi/fixtures/`): the partition, `tcb`, `shadow`, `arith`, `dossier`, `content`, `unusedhyp`, `replay`, `lean4lean`, `autoimplicit`,
Built (one file per examination under `Jinshi/`, with its own fixture and table under `tools/jinshi/fixtures/`): the partition, `tcb`, `shadow`, `arith`, `dossier`, `content`, `roundtrip`, `replay`, `lean4lean`, `autoimplicit`,
`toolchain`, the workflow. On 2026-10-07 the registry showed every `soundness` fix in the pinned `v4.34.0-rc2` (the July 2026 kernel fixes are its
ancestors; the two of 18 August are backports on its release branch) and two `runtime-soundness` fixes of September 2026 that it
lacks (reference-count overflow in the runtime, not the kernel: the next toolchain bump takes them).
Not yet: the per-module Jinshi grade as a tag; notation overloading under `shadow`; the dossier for the seed's own definitions.
