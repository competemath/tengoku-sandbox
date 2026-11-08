# Contributing to Tengoku

Everything lands through a pull request; a gate checks the shape of the
change in about three minutes, and a merge queue compiles exactly the
mathematics it adds. You never build the whole tree; a maintainer approves each
pull request before it merges, and looks closer when a check flags something. [How Tengoku is
tested](docs/testing.md) explains every check; this page is the short list of
the easiest way to do each thing.

## Add theorems

1. Write your records, one JSON object per line, into a **new file**
   `data/staging/<library>/<anything>.jsonl` (`schemas/record.schema.json`
   is the shape; a record of a library that has a corpus in
   `schemas/sources.json` needs `source_path` and `context`, or it is never
   compiled). Your credit docstring (README, *Contributors*) is the first lines
   of `statement`. One file per PR: two PRs appending to the same file cannot
   both sit in the queue.
2. Optional: check it builds before you push (the merge queue builds it anyway):
   ```
   scripts/cache.sh get
   git clone --filter=blob:none <corpus repo> corpora/<library>   # repo + commit in schemas/sources.json
   python3 scripts/generate.py --corpus corpora/<library> --libraries <library> \
     --candidate <source_path> --candidate-names <your record names, comma-separated>
   lake build Tengoku.<Library>.<Path>._candidate_<File>
   ```
3. Optional: mark up to ten of your records as headline theorems
   (`"headline": true`); each must credit its author with an `Author:` line in
   its docstring.
4. `git commit -s` (the sign-off is required), push, open the PR, and turn on
   *Merge when ready*. The gate comments on the PR with anything it found;
   the queue builds your candidate module and merges.
   The merge also waits for a maintainer's approval and for every review
   conversation to be resolved,
   including the AI reviewer's (CodeRabbit): read each comment, fix
   what applies or reply saying why not, and press **Resolve conversation**.
5. The promote bot later moves your records to `data/trusted/`, regenerates
   the module and deletes your per-PR file in its own PR. Your name, and the
   `source_url`, stay on the record forever.

## Retract a theorem

Nothing is ever deleted. Append a tombstone line to
`data/trusted/<library>.jsonl`:

```
{"tombstone": "<name>", "category": "duplicate", "reason": "…", "by": "<you>", "at": "<ISO date>"}
```

`category` is one of `duplicate`, `incorrect`, `superseded`, `licence`, `other`,
and never changes. The generator drops the record from its module and from
every candidate; the bot's next promotion regenerates the module. History stays
in the file.

Say where to look instead with a note. Unlike the tombstone it can change as
the library changes: append a newer note and it replaces the old one (the old
one stays as history).

```
{"tombstone_note": "<name>", "note": "follows from …", "see": ["tengoku:Some.Theorem", "https://…"], "by": "<you>", "at": "<ISO date>"}
```

## Correct a credit (plagiarism only)

Credit changes only when there is evidence of plagiarism. The record is never
edited; append a correction and the generated module shows the corrected
credit with a link to the evidence:

```
{"credit_correction": "<name>", "credit": "Author: …", "evidence": "https://…", "by": "<you>", "at": "<ISO date>"}
```

## Add a source library

A tooling PR that adds the source to `schemas/sources.json` (its URL prefix,
its licence, and its `corpora` entry: repository and commit the generator
reads source files from). Records from it come in a second PR.

## Change the tooling

Scripts, workflows, schemas and the Lean tool programs are `tooling`. Install
the hooks once (`pipx install pre-commit && pre-commit install`); CI runs the
same `.pre-commit-config.yaml`, the unit tests and `actionlint`, so what
passes locally passes there. New or changed behaviour comes with a test that
fails without it, in `scripts/tests/` or `scripts/ci/tests/`; run them with
`python3 -m unittest discover -s scripts/tests` and
`python3 -m unittest discover -s scripts/ci/tests -p 'test_*.py'` (after
`pip install --require-hashes -r scripts/ci/requirements/yaml.txt`, the PyYAML the workflow-rules tests
need, pinned by hash as CI installs it).
A change to a gate script that reads what a PR supplies also runs its fuzz targets, in pr-tests and again in the
merge queue (`python3 scripts/ci/fuzz/run.py --all --replay` runs them locally; [How Tengoku is
tested](docs/testing.md#fuzzing)). `CODEOWNERS` review applies. Run the scenario
campaign against the sandbox before touching `scripts/ci/` or the workflows
(`scripts/ci/campaign/README.md`).

## Fix docs

`README.md`, `CONTRIBUTING.md` and `docs/**` are `docs`; they may ride along
with any other change.

## A theorem whose assumptions can never all hold

The gate builds the theorems a PR adds and tries to derive `False` from each
one's hypotheses alone. If it can, the theorem is vacuously true: it proves
nothing, and the PR fails with the clashing hypotheses named. Fix the statement
and push, or, if the empty hypothesis set is intended, add one line per theorem
to the PR description and the gate re-runs:

```
Vacuous-Ack: <theorem name>: <why it is intended>
```

The name as your record writes it is enough; the gate's message shows the full
name with the namespaces the module opens around it, which works too.
`tools/vacuity/` runs the same check on any built project.

## When a check fails

Read the gate's comment on your PR: it names the check and the step, quotes
the error, and says what to do. Push the fix; the comment updates. If the PR
was in the queue, re-queue it after the fix (`gh pr merge --squash --auto`).
If you believe the check is wrong, use the **Report a gate bug** link in the
comment — it opens an issue with everything filled in.

## Depend on another PR

Put `Depends-On: #123` in your description. Your PR waits until #123 is
merged or queued ahead of it; the gate re-runs when the description or the
branch changes.

## For maintainers

- **The promote bot** is the only identity whose PRs may touch generated
  files (`promotion` class); the account is named in the `TENGOKU_BOT`
  repository variable. The queue still regenerates and diffs what it touches.
- **Porting tooling changes**: prove them in the sandbox
  (`competemath/tengoku-sandbox`) with the campaign, then open the same
  change here.
- **Caches** are built nightly by CI on Linux; `scripts/cache.sh put` refuses
  to pack on macOS. Merging a workflow change while a build runs makes that
  build relaunch on the tip instead of publishing.
- **Gate-bug issues** are the feedback loop: a confirmed false positive
  becomes a unit test and a fix.
