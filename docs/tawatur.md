# Tawatur: a proposal

> **This is a proposal, not a status the tree has.** Nothing in the gates, the queue or the tags uses it. `scripts/tawatur.py` is a reference implementation of the
> independence test on closure data, with tests; there is no extractor yet that produces that data from the compiled tree, and no theorem is, or is called, tawatur.
> The research issue is competemath/tengoku#283.

*Tawatur* is the hadith term for a report handed down by so many independent chains that a shared error is not plausible. The proposal is an optional status above *trusted*:
a statement that has several proofs which do not lean on one another.

## The idea in four lines

- A **statement** is what an isnad id names (`docs/isnad.md`): two theorems with the same id state the same thing. Each theorem of the tree with that id is a **proof** of it.
- A proof's **closure** is every constant its proof term reaches, transitively.
- Two proofs are **independent** when they come from different libraries (distinct chains of provenance) and their closures are disjoint after a set **X** is ignored.
- A statement is **tawatur** when at least *k* of its proofs are pairwise independent and each has enough substance (*k* is 3 or 4: the maintainer's call, 4 in the first
  statement of the idea, 3 acceptable).

## Why X is the whole question

Every proof reaches the kernel's axioms, Lean's core and, in practice, Mathlib's foundations, so closures are never literally disjoint. X is what independence is judged *after*:

| Layer of X | Content | State |
|---|---|---|
| forced | the three axioms and the logical constants; Lean's core, **by the module that defines a constant** (`Init`, `Std`, `Lean`: `Nat.succ` is in `Init.Prelude`, its name says nothing), falling back to the namespace of the name when the input has no module; the constants of the statement itself | in `scripts/tawatur.py` |
| pinned foundation list | the part of Mathlib every proof of everything stands on (order, algebraic hierarchy, `Finset`, `Set`, …) | **open**: to be calibrated, not guessed |
| substance floor | a proof with fewer than *F* constants outside X (a one-liner `simp`) does not count | parameter, default 5 |
| distinct provenance | proofs from one library are one chain, whatever their closures | in the tool |

The calibration is empirical, against labelled pairs: duplicates that are only aliases of one proof must fail the test, genuinely independent proofs must pass. On 2026-10-04,
over 12,416 theorems of the six libraries then in the tree, the statement groups were 69: 51 aliases, 11 similar, 7 independent. A foundation list that is too small calls
aliases independent; one that is too large calls nothing independent.

## What it would and would not tell you

It reduces the chance that **one wrong lemma or one wrong definition used by a proof** makes a false theorem look established: a second proof that shares none of that
cannot be wrong in the same way. It says nothing about:

- a **misformalised statement**: all proofs prove the same wrong sentence; the isnad id names the sentence, not the intention;
- a **bug in the kernel** (the independent re-check by `nanoda` is the defence, not proof counts);
- anything inside X: if the foundation list is wrong, the test is wrong.

So it is a statement about *proofs*, never about the truth of the statement's source; the docs of any status built on it must say so.

## Where the tree stands today

No statement has more than three proofs in the tree and the independent ones are fewer, so the set is **empty today**. That is a measurement, and the reason this is a
proposal: a status nothing can attain yet is not worth building into the gates. It becomes testable when (a) the sweep has tagged the tree, so every theorem has its id, and
(b) there is an extractor.

## What a first implementation would be

1. A Lean executable like `tengoku-isnad` that, for the theorems whose id occurs twice or more in the tree, prints `{id, name, lib, closure, statement_closure}` (the closure is
   `Expr.getUsedConstants` followed to a fixed point over theorem and definition bodies; the groups are few, so the cost is small).
2. `scripts/tawatur.py report` on that file, with the calibrated foundation list as `--ignore`.
3. The result is **index data**, not a docstring and not a gate: `@isnad-runtime tawatur=true proofs=3` shown in the infoview and on the site only when attained, never written
   into a module (a tag is about what a theorem *is*; this changes when another proof arrives).
4. How a further proof of an existing statement enters the append-only library: as an alias theorem under its own name (a duplicate statement is wanted, `docs/isnad.md`), so
   nothing new is needed in the classes.

## The reference implementation

```bash
python3 scripts/tawatur.py report --k 3 --floor 5 [--ignore NAME]... [--ignore-prefix Mathlib.Order.]... [--all] < closures.jsonl
```

The closures come on standard input, one line per proof (no file name is read from the command line; a foundation list kept in a file is passed as `$(sed 's/^/--ignore /' foundation.txt)`): `{"id", "name", "lib", "closure": [...], "statement_closure": [...], "modules": {constant: defining module}}` (the last two optional). The output has one JSON line per statement that has two or more
proofs: its proofs, the ones with substance, the number of constants every pair shares, the largest independent set (Bron-Kerbosch on the independence graph) and whether it
reaches *k*. `scripts/tests/test_tawatur.py` fixes the behaviour: shared constants, same library, the substance floor, the forced layer, the statement's own constants, a
caller's X, and that the *largest* independent set is found, not the first.

## Decisions for the maintainers

*k* (3 or 4); whether `from=translated` proofs of one upstream count as one chain even when their libraries differ; the foundation list and who may change it (a change
re-evaluates every statement); whether a status that cannot be attained yet belongs in `docs/isnad.md`'s table at all.
