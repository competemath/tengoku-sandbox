# Native: the tree's own content

`Tengoku/Native/` holds **novel content as Lean modules**: CompeteMath's own certified theorems, results Leak proved, and what people write for the tree, as opposed to
`Tengoku/Seed/` (Mathlib and the packages seeded with it) and `Tengoku/<Library>/` (translations of other people's libraries). Where a module lives decides the `from=`
of its isnad tag (`docs/isnad.md`): `seed`, `novel` for Native, `translated` for a library. Native modules build on the seed and on each other, never the other way
round: the seed and the translated libraries do not import Native.

Since the content is ours, it may be **reorganised**: an isnad id never depends on the module a theorem is in, so moving a theorem to a better file changes nothing that
identifies it. (A Native module is still not deleted by a PR: a theorem that was in the tree and is retracted is retracted by a tombstone, not by disappearing.)

## What may go in

A module of `Tengoku/Native/` has a credit (`Authors: …` in its header comment), imports only `Tengoku` and other Native modules, and passes the content allow-list of the intake
class in its strictest mode (`scripts/ci/allowlist.py`: known-inert commands, no `notation`, no macros, no code that runs while compiling, no way to trust the compiler). In
particular a theorem proved by `native_decide` (or `ofReduceBool`, `trustCompiler`) **is not in Native, and is not rewritten to fit**: the lint refuses the words, the merge queue's
axiom check refuses the axiom they leave behind, and the importer below leaves such records out. There is no `sorry`, and no isnad tag (the sweep writes tags and recomputes them).

## The class

A **native PR** (`docs/pr-classes.md`, section 8; `scripts/ci/native_check.py`) adds or edits modules under `Tengoku/Native/`, keeps `Tengoku/Native.lean` (the umbrella: one `import` per
module) in step, and, with the first one, adds `import Tengoku.Native` to `Tengoku/All.lean`. It comes from `TENGOKU_BOT` like every generated class, has at most 400 modules, and is
judged from git objects (nothing of the PR runs). The merge queue builds the PR's modules (the whole of Native when one is edited), checks the axioms of every theorem and writes the leak
report. Opening the class to other contributors, who would write Lean rather than records, is a decision for the maintainers; until then a contributor's theorem comes in as a record
(`CONTRIBUTING.md`) and Leak's certified ones are imported as below.

## Importing records

`scripts/native_import.py` turns trusted records (written for `import Mathlib`, with their own proof) into modules:

```bash
python3 scripts/native_import.py data/trusted/competemath.jsonl --out /tmp/native
```

Every record sits in a namespace of its own, `Native.<Source>.P<N>` for problem N (`P<N>_2` for a second record of the same problem), so a helper definition, an `open` or a
`set_option` in front of a theorem touches nothing else, and gets the docstring `competemath.com problem N.`. The area of a record, hence its module
(`Tengoku/Native/Competemath/NumberTheory1.lean`, …), is guessed from the words of its statement. A record that trusts the compiler or is unfinished, has no theorem of its own, or
repeats a name is left out and listed in `native-import.json`. The modules are checked by compiling them (Leak IV for a draft, the merge queue for the PR).
