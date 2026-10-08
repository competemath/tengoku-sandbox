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
| `reproduce` | `scripts/jinshi/run.py` (a second compile, with lake's own options) | the module's `.olean` compared byte for byte with the one the attested cache ships: a difference is a compiled artefact that is not what the source gives (tampering, a stale cache, or a non-reproducible compile) | warn |
| `mutants` | `scripts/jinshi/run.py --checks mutants` → `tengoku-jinshi --check mutants --mutants-out DIR` → `scripts/jinshi/mutants.py` | differential kernel fuzzing seeded from the tree's own proofs (Jinshi/Mutants.lean): for the first 20 theorems of each module (JINSHI_MUTANTS_PER_MODULE, by name), eight mutation operators at fixed positions, no randomness: two same-typed arguments of an application swapped, a subterm replaced by another of the same type, `Eq.refl a` made `Eq.refl b`, an argument dropped, a proof replaced by a proof of another proposition, a universe level raised, a `Nat` literal of the statement raised with the proof kept, a subterm eta-expanded (well-typed: every kernel must accept). Each mutant `<theorem>_mut<k>` is judged by Lean's kernel in the examination's own process (verdict and refusal kind: info), written UNCHECKED as a module of its own, `JinshiMutants.<Module>.M<k>` (one declaration, importing the module), and judged by `leanchecker` and `lean4lean`, one kernel run per mutant, plus a fourth, opt-in judge, `nanoda` (`scripts/jinshi/nanoda.py`; independent of Lean's own code, reads a `lean4export` dump instead of an `.olean`) when `NANODA_BIN` and `JINSHI_LEAN4EXPORT` name their binaries (the workflow builds both; unset, nothing changes). A mutant whose export touches a `native_decide`-style trusted head is `nanoda`'s `skip`, not a verdict, and never counts as a disagreement (nanoda.py, `TRUSTED_HEADS`: nanoda only ever sees the axiom, never the compiled code it stands for). Kernels that disagree on a mutant (the skips aside): one of them has a bug, the module is the reproducer. Off unless `--checks` names it (it writes files and runs kernels); the fixture opts in with `jinshi: mutants` in its module doc | fail (disagreement) / warn (a kernel timed out) / info |
| `autoimplicit` | `scripts/jinshi/run.py` → `lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>` | re-elaborates the module with auto-bound implicits off; every `unknown identifier` names a statement in which Lean quantified a name the author never bound. A module that itself sets `autoImplicit true` is reported as opting in. Greek letters, the idiom for a type variable, are `warn` not `fail`; a non-Greek name within one or two edits of an identifier already in scope at that point (the declaration's own binders, or an earlier `variable` block) is flagged in the detail as a likely typo, not a genuine free variable | fail |
| `tcb` | `TengokuJinshi.lean` | the trusted-computing-base inventory of the round: every `unsafe`, `partial`, `opaque`, `implemented_by`, `extern`, `axiom`, `initialize`, and every declaration whose type lives in the elaborator's monads; a theorem whose statement mentions one | warn (statement) / info (inventory) |
| `shadow` | `TengokuJinshi.lean` | a library constant whose name, minus any prefix, is a name the seed declares; the theorems of the library whose statements mention it | warn |
| `nearname` | `TengokuJinshi.lean` | a library constant whose name is almost a seed name: a character that reads as an ASCII letter or digit but is not one, or an invisible one (fail); a suffix of the name that is a seed name once case, primes, underscores and trailing digits are ignored, or one edit away from a seed name of the same namespace (warn); the theorems of the library whose statements use such a name | fail (homoglyph) / warn |
| `arith` | `TengokuJinshi.lean` | in the elaborated statements of a library's theorems: `ℕ`/`ℤ` subtraction and division, numerals typed `ℕ` next to `ℝ`/`ℚ`/`ℂ`, `Real.sqrt`/`Real.log`/`⁻¹`/`/` whose argument no hypothesis bounds (the seed is exempt: its lemmas state these operations deliberately, they are the foundation the rest builds on; a library's theorem meets them by accident) | warn |
| `arithUniverse` | `Jinshi/ArithUniverse.lean` | self-contained, synthetic, reads no corpus module: (A) a hand-written family of `max`/`imax`/`succ` level-algebra identities over params `u,v,w` and offsets 0..4 (commutativity, associativity, subsumption of a smaller offset of the same param, the `imax _ zero`/`imax _ (succ _)` case split), each checked against an independent semantic model (a level evaluated under an assignment of its params to small `Nat`s, over the whole 0..4 grid) and then against the kernel's own `isDefEq` on `Sort l1 =?= Sort l2`; (B) closed `Nat` literal triples for `add/sub/mul/div/mod/pow/land/lor/xor/shiftLeft/shiftRight`, including boundary values (`2^32`, `2^63`, shift/pow exponents to 100) and underflow/divide-by-zero cases, each checked by `Jinshi.decideOne` against an expected result computed independently in Python. One summary `info` line per run with tried/agreed/disagreed/capped counts for each sub-check | fail (a pair the model proves equivalent that the kernel's isDefEq refuses; a Nat case `decideOne` does not confirm) / warn (the generator's own pair fails its grid check, never the kernel's fault) / info (summary; a case capped by the heartbeat limit) |
| `dossier` | `TengokuJinshi.lean` | for each theorem of a library, the library-local constants its statement depends on, each printed; one that reduces to `True`/`False`, ignores its arguments, or is a structure without fields is flagged | fail (trivial) / info |
| `content` | `TengokuJinshi.lean` | a conclusion that is a hypothesis, `True`, `a = a`, `p ↔ p` | warn |
| `duplicate` | `TengokuJinshi.lean` | the same statement proved twice: every theorem of the environment is indexed by its elaborated statement with binder names and universe parameter names erased (the identity of docs/isnad.md, without its hash), and each theorem of the round is looked up; a library's theorem that proves again what the seed already has, or what the same library already has, is a warning; two libraries (or the seed twice) proving one statement is *tawatur*, several proofs of one claim | warn (seed, same library) / info (tawatur) |
| `entailed` | `Jinshi/Entailed.lean` | the entailment oracle: for each theorem (the seed's too) the tree itself is asked to prove the statement from OTHER theorems, by Lean's library search (the engine of `exact?`) on a fresh goal of the statement with the theorem and every constant of its module excluded as candidates, the seed's lemmas tried first, the subgoals a lemma leaves closed from the hypotheses alone, unification at `instances` transparency (a lemma whose conclusion merely computes to the statement does not entail it) and the glue of logic (`Eq.refl`, `Eq.symm`, `Eq.mp`, …) never a candidate; a proof found is a certificate only once `Meta.check` and `isDefEq` with the statement confirm it, and its size is recorded. A library theorem entailed by the seed's lemmas alone is a consequence of what the tree already had, a translation that adds no new claim (warn); one entailed by another library's theorem is tawatur of libraries, by another module of its own library redundancy (info); a seed theorem that is a one-step consequence of other seed theorems is info. Silence means the search did not close it within the cap (`JINSHI_ENTAILED_HEARTBEATS`, default 50000k per theorem; `JINSHI_ENTAILED_MAX`, default 50 theorems per module), not that the claim is new; a summary line per run gives the counts | warn (entailed by the seed) / info |
| `instdrift` | `TengokuJinshi.lean` | for each theorem (the seed included), every instance-implicit argument of its elaborated statement is compared with what instance synthesis returns in the environment of the run: the tree is one environment that keeps growing, and a module compiled later (a library, or the seed itself) that registers a global instance of the same class makes the same statement text elaborate to a different term (another norm, order, decidability), so the theorem, true for the instance it was proved with, no longer applies to what a reader now writes; a class for which no instance is found today is reported once per theorem | warn (a different instance today) / info (none today) |
| `unusedhyp` | `TengokuJinshi.lean` | a propositional hypothesis in a theorem's statement (a named binder, not a variable or an instance) that the proof term never mentions, and that no later binder's type nor the conclusion mentions: the theorem holds without it, the statement promises less than was proved (the seed included: this examines proofs, not statements; a `sorry` is skipped) | warn |
| `necessity` | `Jinshi/Necessity.lean` | the complement of `unusedhyp`, on statements: for each theorem (the seed included) every propositional hypothesis is JUSTIFIED when a counterexample shows the theorem fails without it: values for the variables, from a small domain (`Nat` 0..4, `Int` -2..2, `Bool`, `Fin k` with k ≤ 8, `Prop`, `List Nat`/`List Bool` of length ≤ 2; at most 2000 assignments per theorem, the smallest first), under which every other hypothesis holds and the conclusion fails, each closed proposition evaluated as `decide` does (no proof involved). A hypothesis neither used by the proof nor justified is one the theorem may hold without; when every hypothesis of a theorem is justified the theorem is exactly as general as it reads (the badge). An assignment under which every hypothesis holds and the conclusion fails is a statement that evaluates to false. A theorem with a variable of another type, more than 6 variables or 6 hypotheses, or a hypothesis a later binder or the conclusion mentions, is not examined, and says so; `JINSHI_NECESSITY_MAX` caps the theorems examined per module (default 100) | fail (evaluates to false) / warn (neither used nor justified) / info |
| `options` | `scripts/jinshi/run.py` (text, no Lean) | a module's `set_option` lines: a heartbeat or recursion limit raised above the default or set to no limit (the module compiles only with extra budget: fragile under any toolchain change), a `debug.*` option, `autoImplicit true`, a linter switched off | warn / info |
| `roundtrip` | `TengokuJinshi.lean` | what the reader sees against what the kernel checked: each theorem's statement is printed as a reader sees it (the default options, full names), read back as a term, re-elaborated as a type with auto-bound implicits off, and compared with the elaborated statement by `isDefEq`; the seed is examined too. A text that does not parse (a private or hygienic name shown as `x✝`) or does not elaborate (a proof shown as `⋯`) is reported; one that elaborates to a different statement (a notation that hides an argument, an invisible coercion, an instance that resolves differently, a numeral whose type the text does not show) is the finding, with both statements printed | warn (different) / info (unreadable, universes only) |
| `forensics` | `Jinshi/Forensics.lean` | what the proof term of each theorem (the seed's too) says about how the kernel accepted it, in one walk of the term: a `Nat` literal ≥ 2^64 in the proof or the statement (the kernel's bignum arithmetic, where the pinned toolchain's registry has a fix "bound the size of Nat numerals computed by the kernel"); `decide`/`of_decide_eq_true`/`Nat.decEq`-family on a proposition of more than 200 nodes (a decision procedure the kernel evaluated); nested `Eq.mpr`/`Eq.mp`/`cast`/`Eq.rec` deeper than 50; a proof of more than 500× the statement's nodes (automation output, fragile) or a `rfl`-class proof of a statement of 30 nodes or more (definitional unfolding is the whole proof); a proof that mentions `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`/`sorryAx` or an `unsafe`/`implemented_by`/`extern` constant (the kernel checked the Lean definition, not the code that runs; the Nat operations the kernel computes itself are exempt). A term past 2,000,000 nodes is reported as such and its ratio not judged | warn (literals, trusted heads) / info |
| `nested` | `Jinshi/Nested.lean` | an inventory of nested inductive declarations: every inductive of an examined module (the seed included) whose `InductiveVal.numNested > 0`. A nested inductive is one with a constructor argument wrapping the type being defined inside another type former (`List (Tree α)` nests `Tree` inside `List`); the kernel does not check this directly, it builds an auxiliary unnested inductive, type-checks that, and rewrites ("restores") the result into the nested form — a translation step the kernel's own source defensively re-checks, since a mistake in it could reach the environment undetected. A best-effort structural walk of each constructor names which argument has the nested occurrence and of what shape. This is not independent verification: every declaration of the module, nested inductives included, is already re-type-checked at the whole-module level by `replay` and `lean4lean`; `nested` exists only to make them visible and searchable (a maintainer, or a differential-fuzzing pass, can specifically target the kernel's restoration step) | info |
| `importance` | `Jinshi/Importance.lean` | how much of the tree stands on each theorem: the proofs of the whole environment are counted by the constants they use, giving every examined theorem its in-degree and the number of modules that use it (`info`); a theorem used by 25 or more proofs is load-bearing and listed per module, most used first. Every other examination's report is read against this one: a finding on a load-bearing theorem outranks a hundred on leaves. |
| `lineage` | `Jinshi/Lineage.lean` | the same proof twice: every proof term of 12 or more nodes is fingerprinted with its binder names and binder kinds erased and its universe parameters numbered, and every examined theorem is matched against the whole environment's fingerprints. A library theorem whose proof is a seed theorem's, verbatim, is `warn` (provenance to record, whether or not the statement was taken too); the same proof in two libraries or twice in one is `info`. `rfl` is everybody's proof and is never fingerprinted. |
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
`JINSHI_LEAN4LEAN` names its binary). The fixture's mutant modules are then judged the same way `mutants` judges the tree's
own (leanchecker, lean4lean, and nanoda too when `NANODA_BIN` and `JINSHI_LEAN4EXPORT` name their binaries — neither set
locally, so this step does not need a Rust toolchain or a second Lean package to run). This is what `pr-tests` runs when the
recipe changes.

A round, on a built tree (the attested cache; this is what the `jinshi` workflow does in the sandbox):

```bash
scripts/cache.sh get && lake build Tengoku.All
lake build tengoku-jinshi
python3 scripts/jinshi/run.py --round 0 --out jinshi-out      # replay, autoimplicit and the environment checks; summary.md and *.jsonl
```

## 6. Status

Built, one file per examination under `Jinshi/` with its own fixture and table under `tools/jinshi/fixtures/`: the partition;
`replay`, `lean4lean`, `autoimplicit`, `reproduce`, `options`, `toolchain` and `mutants` in the driver; `tcb`, `shadow`,
`nearname`, `arith`, `dossier`, `content`, `decide`, `duplicate`, `instdrift`, `unusedhyp`, `roundtrip`, `forensics`,
`importance`, `lineage`, `necessity`, `entailed` and the generator of `mutants` in the executable; the round in shards. On
2026-10-07 the registry showed every `soundness` fix in the pinned `v4.34.0-rc2` (the July 2026 kernel fixes are its ancestors;
the two of 18 August are backports on its release branch) and two `runtime-soundness` fixes of September 2026 that it lacks
(reference-count overflow in the runtime, not the kernel: the next toolchain bump takes them).

Round 0 (2026-10-07, eight shards, 932 modules) ran the driver's checks over the whole round: no kernel refused anything the
tree ships (the one `lean4lean` refusal was a realized `congr_simp` name, now classified); the tree compiles with `autoImplicit`
on and several libraries lean on it (`Imoshortlist`, `Tautology`, the seed's `Std`, `Tactic` and `Testing` folders); two modules
raise their budgets. The executable's examinations were lost that round to an uncaught heartbeat cap (fixed); `mutants`,
`entailed` and `necessity` have not yet run on the tree and are costed per theorem, so a round names them explicitly.

Not yet: the per-module Jinshi grade as a tag; notation overloading under `shadow`; the dossier for the seed's own definitions;
the examinations at pull-request time on the PR's own modules, with the near-name and notation report as one comment.
