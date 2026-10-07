# How a theorem gets into Tengoku

From an idea to a trusted theorem, in the order it happens. Each step names the file that does it.

## 1. Pick something worth adding

- A goal from [GOALS.md](../GOALS.md): results people have asked for, with what they build on.
- Your own theorems, or a translation of a library that is already registered.
- A whole library: register it (step 8) and the pipeline translates it for you.

## 2. Write the records

One new file, `data/staging/<library>/<anything>.jsonl`, one theorem per line: its name, statement, proof,
where it comes from (`source_url`) and the toolchain ([AGENTS.md](../AGENTS.md) lists every field).

- Put your credit in the statement's docstring: a line starting with `Author:`, naming you and any AI you used.
  Nobody can remove that line later.
- Mark the results your PR is about with `"headline": true`, at most ten. They are shown first.

## 3. Open the pull request

Sign off every commit (`git commit -s`), push, open the PR, and press **Merge when ready**. You do not need to
build anything locally: the merge queue builds your theorems (step 5).

## 4. The gate checks it, in a few minutes

[pr-gate.yml](../.github/workflows/pr-gate.yml) runs these checks and posts one comment saying what passed, what
failed and what to do:

| Check | What it looks at |
|---|---|
| [classify](../scripts/ci/classify.py) | What kind of PR this is (theorems, a retraction, tooling, docs), from the files it touches. It labels the PR, and the kind decides which checks run. One kind per PR; docs may come along with any. |
| [records](../scripts/ci/validate_records.py) | Each record is well formed, comes from an allowed source, declares the name it claims, and is not already in the library; at most ten headlines, each credited. |
| [append-only](../scripts/ci/append_only.py) | Data files only grow: nothing already there is changed. |
| [content-lint](../scripts/ci/lint_banked.py) | No construct that runs code (`#eval`, `unsafe`, `native_decide`, new `axiom`s …). |
| [credits](../scripts/ci/credits.py) | No credit or source line is removed. |
| [dco](../scripts/ci/dco.py) | Every commit is signed off. |
| secrets | No password or key anywhere in the change. |
| [fossa](../scripts/ci/fossa_check.py) | FOSSA's licence, dependency-quality and vulnerability verdicts on your commit are all green (it can take a few minutes to report). |
| [vacuity](../scripts/ci/vacuity.py) | A theorem whose assumptions contradict each other proves nothing; say so in the PR description if it is intended. |
| [goals](../scripts/ci/goals_check.py) | If you changed GOALS.md: its format, and that every theorem it names exists. |
| [workflows](../scripts/ci/workflow_rules.py) | If you changed a workflow: pinned actions. |

A failed check re-runs when you push a fix.

## 5. Review, then the merge queue

- CodeRabbit, an AI reviewer, comments on the PR. Every conversation must be resolved before it merges:
  fix what applies or reply why not, then press **Resolve conversation**.
- The merge queue ([queue-gate.yml](../.github/workflows/queue-gate.yml)) builds only your theorems, against the
  whole compiled library, and checks that none uses `sorry` or any axiom beyond Lean's standard three.
- If it fails, the queue comments with the first error and a hint, and labels the PR `ejected`. Push the fix and the
  PR goes back into the queue by itself.

## 6. In the library, as staging

Once merged, your records are in `data/staging/`: checked, but not yet trusted.

## 7. Trusted

Promotion builds each file again from scratch, checks vacuity once more, moves the records to `data/trusted/` and
regenerates their Lean modules. You get a comment on your PR listing which of your theorems are now trusted
([promotion-notify.yml](../.github/workflows/promotion-notify.yml)). The search and verify services pick up the
new library within minutes.

**Trusted means:** your theorem's module builds from scratch against the compiled library on the pinned toolchain,
it uses no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), its assumptions are not contradictory, and its
source, licence and credit travel with it. It is never deleted: a mistake is retracted with a tombstone that stays
in the history, with a note on where to look instead.

## 8. Adding a whole library

A tooling PR that adds the library to `schemas/sources.json` (its repository, the commit, its Lean roots) and its
licence. Once merged, Emissary-Archangel, the translation pipeline, picks it up within a quarter of an hour: it
builds the library on GitHub's runners, makes every file self-contained, translates each theorem into the
library's toolchain, and opens staging PRs from branches `bank/<library>/…`. It comments on your registration PR
when it starts. Those PRs go through steps 4–7 like any other.
