# How a theorem becomes trusted, and what that does and does not mean (draft)

This page defines the words the README uses, step by step, and says plainly what each check cannot do.

## The words

| Word | Meaning |
|---|---|
| **record** | one theorem (or definition) in the library's data files: its Lean statement and proof, the source it came from (a link at a fixed commit), its licence, and its credit |
| **tier** | where a record stands: **tentative**, **staging** or **trusted** |
| **tentative** | a real proof from a real source, indexed and searchable, not yet translated or re-checked here |
| **staging** | translated onto the library's toolchain and accepted by the translation checks, awaiting promotion |
| **trusted** | built into the library and passed every check below (with the exceptions in [known gaps](#known-gaps)) |
| **gate** | the checks that run on every pull request, before anything is merged |
| **merge queue** | the step that builds a change together with the whole library before it can merge |
| **promotion** | the step that moves a record from staging to trusted, after a fresh build and two more checks |
| **translation** | rewriting a theorem from the Lean version it was proved on to the library's version, by an automated pipeline that is partly driven by an AI agent; checked twice (below) |

## The path

```mermaid
flowchart LR
  A["theorem + credit line<br/>(a record)"] --> B["gate"] --> C["merge queue"] --> D["tentative / staging"] --> E["promotion"] --> F(["trusted"])
```

1. **Gate.** The record has the right shape; its source is on the list of accepted sources (with their licences); it carries an `Author:` line naming the human and any AI used; its Lean is checked for constructs that run code when the library compiles (a list of banned constructs, and an allow-list of `set_option`s; a stricter allow-list of everything a record may contain is proposed); it contains no secrets. Every pull request passes through it, the maintainer's included.
2. **Merge queue.** For records heading to trusted, the new modules are built together with the whole compiled library, with every named declaration checked for `sorry` and for any axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
3. **Translation checks** (for records translated from another Lean version). Check one: the translated script compiles in the library's environment with no errors, no warnings and no `sorry`. Check two: the original is replayed from an export of its own module into the same environment, and the kernel accepts `fun h => h : T_translated → T_original` (the translation proves at least what the original proved, under the original's own names).
4. **Promotion.** A fresh build of the record's module against the compiled library, the axiom check again, and a **vacuity** check: the theorem's hypotheses are tested for contradiction, and a theorem whose hypotheses imply `False` is refused unless a person acknowledges it with a reason.
5. **Nightly independent check.** Every declaration of the compiled library (about 745,000 on the latest run, from a 110-million-line export) is checked again by [nanoda](https://github.com/ammkrn/nanoda_lib), a type checker written separately from Lean, and a separate program computes the axioms every constant rests on.

## What "trusted" does not mean

- **Not that the statement says what its source says.** The kernel checks that a proof proves a statement; nothing here checks that the statement faithfully encodes the informal claim. Translation adds one more place for this to go wrong. (An [audit](https://arxiv.org/abs/2606.29493) of five widely used Lean benchmarks found exactly this kind of defect.)
- **Not that a translation is equivalent to its original.** Check two shows the translated statement implies the original; it can be stronger. Lean and Mathlib change meanings between versions, which is why each theorem keeps a link to its original.
- **Not that the vacuity check is complete.** It finds hypotheses from which `False` can be derived; it cannot prove that hypotheses are satisfiable.
- **Not that the second checker covers everything.** nanoda checks the declarations that Lean's exporter (lean4export) writes, so it guards against a bug in Lean's kernel; it trusts the exporter, and it does not check the elaborator or the statement.
- **Not that a person reviewed it.** Mathlib's line-by-line review is a stronger and different standard. Tengoku builds on Mathlib and does not claim to replace it; anything Mathlib-suitable belongs upstream.

## What is kept

Records are append-only. A mistake is retracted by a tombstone with a category (duplicate, incorrect, superseded, licence, other) and a note (moving a record out of trusted would need a category of its own: *demoted*); credit changes only on documented evidence of plagiarism. Copyleft sources are not accepted, and a source whose licence is found incompatible is removed.

## Known gaps

Counted on 2026-10-02. They are why the README says "built into the library" only where it is true.

- **Not every trusted name is matched in the nightly check.** The check matches 136,444 of the 161,646 distinct trusted names to declarations in the compiled library, and all of those rest only on the standard axioms. The other 25,202 are mostly Mathlib search-index entries (by topic: algebra, data, analysis, …) that are not matched by name; the check counts them and does not fail on them.
- **CompeteMath's 262 problems.** They are marked trusted and are in the v1.0.0 dataset, but the library has no module for them: they were verified by the Leak IV verifier on Lean v4.29.1 and v4.32.0, not on the library's toolchain. 103 of them use `native_decide`, which trusts the compiler, and one (`quadratic_echo`) contains `sorry`. The gate that bans these constructs only judges the lines a pull request adds, so it never saw records added in bulk. Until they are re-checked, they are an exception to everything above; the proposal is to move them to *tentative*.
