# How Tengoku is tested

Tengoku's promise is one sentence: **a trusted theorem is in the tree, and the
tree builds on the pinned toolchain with no errors, no `sorry`, and no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.** Everything below exists
to keep that sentence true for every change from anyone, without a human in
the loop for the common case, and to say clearly what went wrong when it is
not true.

There are six layers. Each one is cheap enough to run where it runs, and each
catches something the others cannot.

| Layer | Where | Runs on | Catches | Typical time |
|---|---|---|---|---|
| Unit tests of the gate scripts | `scripts/ci/tests/test_gates.py`, `scripts/tests/` | your machine, CI (`tooling-tests`) | a gate script that does not do what it claims | 5 s |
| Fuzzing of the gate scripts | `scripts/ci/fuzz/` | a PR or merge group that changes a covered script (`tooling-tests`, `queue-build`); weekly for longer (`fuzz.yml`) | an input from a PR that makes a gate script crash or print a workflow command | nothing for most changes, 1–2 min when it runs |
| Pre-commit hooks | `.pre-commit-config.yaml` | your machine, CI (`lint-python`) | lint, formatting, secrets, banked content — the same list in both places | seconds |
| The PR gate | `.github/workflows/pr-gate.yml` | every pull request | wrong shape of change: two purposes, edits to append-only data, forbidden constructs, missing credits, secrets, missing sign-off, unmet dependencies | 2–3 min |
| The merge queue | `.github/workflows/queue-gate.yml` | every merge group | wrong mathematics: a proof that does not compile, a `sorry`, a non-standard axiom, a hand-edited generated file | 3–7 min |
| The independent check | `.github/workflows/independent-check.yml` | nightly, and on demand for any commit of `main` | a bug in Lean's own kernel, or a record that slipped something past both gates: every declaration of the tree type-checked again by nanoda, every constant's axioms recomputed from the export | ~45 min |
| The scenario campaign | `scripts/ci/campaign/` | a sandbox copy of the repo, on demand | a check that passes when it should fail — the tests of the tests | ~3 h for everything |

The nightly cache build (`.github/workflows/build.yml`) is not a test but the
queue depends on it: it compiles the tree once a day, publishes the result as
a release, and signs every part with a build-provenance attestation that the
queue verifies before unpacking. The attestation is also a file of the release,
`tengoku-cache.intoto.jsonl` (`tengoku-snapshot.intoto.jsonl` in a numbered
release), so a download can be checked offline:
`gh attestation verify <file> -R competemath/tengoku --bundle <that file>`.

## 1. The PR gate

Runs on `pull_request` (and on merge groups, where it repeats the cheap
checks). No Lean runs here; the whole thing is done in about three minutes.
The jobs, in the order they matter:

- **classify** reads `git diff --name-status` and assigns the PR one class from
  the paths it touches: `content` (records under `data/tentative/` or
  `data/staging/`), `tombstone` (a retraction appended to `data/trusted/`),
  `tooling` (scripts, workflows, schemas, the Lean tool programs, seeded
  modules), `docs`, or `promotion` (the bot moving records to trusted and
  regenerating modules). Two classes fail, except `docs` rides along with
  anything. Files the generator writes (`Tengoku/<Library>/**`,
  `Tengoku/All.lean`, `data/stats.json`) are never accepted from a person.
- **data-rules** (content, tombstone, promotion): `append-only` — every byte
  of an existing data file stays and new lines go at the end; `records` — each
  added record has the required fields, an allowed `source_url`, an identifier
  name that its statement declares, no duplicate against the PR or against
  trusted, and a corpus library's staging record carries `source_path` and
  `context` (without them it would never be compiled); `content-lint` — no
  `import`, `#eval`, `run_cmd`, `initialize`, `unsafe`, `native_decide`,
  `axiom`, `IO.Process`, or `set_option` off the allowlist inside a record.
- **credits**: no removed or changed line carrying an authorship or provenance
  marker (`Authors:`, `Copyright`, `source_url`, …). Scripts, workflows and
  schemas are exempt because they name those keys.
- **vacuity**: every theorem the queue would compile is checked for hypotheses that
  can never all hold (`False` derivable from them alone); such a theorem must be
  acknowledged in the description (`Vacuous-Ack: <theorem>: <why>`). Runs before
  the queue so that an author sees it.
- **secrets**: TruffleHog for verified credentials, plus the same
  `detect-secrets` pattern scan as the pre-commit hook over every changed
  file and over the added lines of data files, so a token inside a record is
  caught too.
- **dco**: every commit carries `Signed-off-by:`.
- **depends**: `Depends-On: #N` lines in the description point at PRs that
  are merged or already in the queue.
- **fossa**: FOSSA's three verdicts on the PR's head commit (License
  Compliance, Dependency Quality, Security Analysis) are all `success`. FOSSA
  reports on PR commits only, never on a merge-queue entry, so it cannot be a
  required check of the ruleset itself (a queue entry would wait for a status
  that never comes); this job waits for the verdicts (up to 15 minutes) and
  `pr-gate` depends on it. A verdict that never arrives fails: silence is not a
  pass. `scripts/ci/fossa_check.py` reads the statuses of the commit, nothing
  of the PR runs.
- **lint-python**, **tooling-tests** (tooling only): `pre-commit run
  --all-files`, the unit tests, `actionlint` on the workflows.
- **sorry-advisory**: lists `sorry`/`admit` in the change, in the gate comment
  below; never blocks, because the queue is the authority on proofs.
- Every job above checks out the base branch's **tip** for its scripts (the
  workflow's `SCRIPTS`), and measures the diff against the base commit the
  event recorded (`BASE`). A gate script merged after a PR was pushed is
  therefore in force for that PR too, with no push needed.
  The one job that compiles the PR's records (`vacuity`) lays the PR's data
  changes over that tip (the PR's data files, then main's versions of the ones
  the PR did not change), so what main changed since the PR's base stays; a
  file both changed fails the job instead of building stale records.
- **pr-gate**: the required check. Passes only when every job of the PR's
  class passed. It also posts **one comment per PR**, updated in place: each
  failed check with its step, the first lines of its error, what the check
  looks for, what to do, and — for the checks that reason about paths, text
  patterns or other services — a prefilled *Report a gate bug* issue link,
  because those checks can be wrong themselves.

**Reading untrusted data and holding a write token are never the same job.**
Every job that reads the PR's commits (or the queue entry's) holds a read-only
token and runs main's scripts on them as data. The jobs that can write are two,
and neither touches the PR's commits: `label` (takes the class as an output and
accepts only the fixed class names) and `pr-gate` (stops stale queue runs and
writes the one comment, which quotes other jobs' output as data, inside a code
fence the quote cannot close). The queue entry is re-checked by `queue-recheck`,
a read-only job, and `pr-gate` only reports its result.
`workflow_rules.py` enforces it (rule `write-and-pr`), so a later edit cannot
quietly bring the two together again; CodeQL's `untrusted-checkout` alerts on
this workflow pointed at exactly the three jobs that did.

Every `run:` step in every workflow runs under `bash -e -o pipefail`, so a
piped command's failure fails the step. That default exists because the
campaign found two checks whose findings never failed their job.

## 2. The merge queue

Runs on `merge_group`. GitHub forms groups of up to five PRs and tests them
cumulatively; a failing group loses its newest PR and the rest are retried.

1. **Cheap checks again** (classify, lint) on the merged result.
2. **Seed the cache**: `scripts/cache.sh get` fetches the newest published
   cache that is an ancestor of the merge commit and verifies each part's
   attestation (`TENGOKU_VERIFY=warn` until every published cache carries one,
   then `require`). Nothing is compiled that the cache already has.
3. **Corpus and candidates**: for every library the group touches,
   `scripts/ci/queue_targets.py` clones the corpus pinned in
   `schemas/sources.json` and runs `scripts/generate.py --candidate
   <source_path> --candidate-names <the group's own records>` — a candidate
   module holds the file's trusted records plus only this group's new ones,
   so an older broken staging record of the same file cannot sink someone
   else's PR.
4. **Build only the candidates**: `lake build <candidate modules>`; a
   `sorry` anywhere in the output fails the step with the record named.
5. **Axioms**: `lake exe tengoku-axioms --module <candidate>` walks every
   declaration of the module with Lean's `collectAxioms`; anything beyond the
   three standard axioms fails. This is the check that catches `decide
   +native`, which compiles cleanly and adds an axiom silently.
6. **Regeneration diff**: the library of every generated module the group
   touches is regenerated and compared; a hand edit cannot survive. Only the
   group's own files are compared, since `main` may lag the generator
   between promotions.
7. **Ejection comment**: when the group fails, the newest PR gets a comment
   with the file, line and column, the source line, the record name, a hint
   keyed on the error class (unknown identifier, type mismatch, unsolved
   goals, `sorry`, heartbeats, axiom, forbidden construct, regeneration), the
   run link, and the same *Report a gate bug* link.

**The cache build has priority over workflow changes.** A group that touches
`.github/workflows/` waits (up to 35 minutes) for any running cache build to
finish before its checks run; content and promotion groups never wait, since
they do not disturb a build. Without this, a busy queue of tooling PRs could
defeat the nightly's relaunch every night and no cache would ever publish. The
build itself relaunches on the tip up to twice.

### A cache that matches the base

The queue starts from the newest published cache (and the promoted top-up) and compiles the difference. After a change that touches many modules, and before its
cache build has published, that difference is most of the tree: a group would build for hours against the 40-minute limit. `scripts/ci/cache_fresh.py` counts the
Lean modules that differ between what the cache is for and the base (limit 1,000, or the repository variable `TENGOKU_STALE_LIMIT`); over the limit it waits up to
5 minutes while a cache build is running (the wait comes out of the queue's 40 minutes, with the seed, the build and the pack still to come: the
arithmetic is pinned by a test), and otherwise fails with a message that says it is not the author's change. On the real commits of 2026-10-05
(cache from before the seed's move, base = the move) it counts 9,992 modules; on a normal day 230 to 305. Its tests are scenario tests on synthetic histories, and
each rule has a mutation that fails them.

### The top-up

After the checks above, the queue restores the tree to the group's own commit, builds the whole
library as main will have it (from the nightly cache plus the newest top-up, so only the group's
own changes compile) and publishes the compiled difference before the merge is allowed. A failed
publish ejects the PR with a comment that says it was not the author's fault. The full story,
including how the services follow it and what was tested, is in [top-ups](topups.md).

### The independent check

Nightly, and on demand for any commit of `main` (`gh workflow run independent-check.yml -f commit=<sha>`):
lean4export writes every declaration of the compiled tree (Lean's core, the seed, every library), about
110 million lines, and two programs that share no code with Lean read it.

- [nanoda](https://github.com/ammkrn/nanoda_lib), an independent type checker written in Rust, checks every
  declaration again (745,847 on the tree today, about 9 minutes) in a sandbox without network. It admits the
  seven axioms Lean's prelude declares in every environment; any other axiom is a hard error.
- `scripts/ci/axiom_scan.py` computes, from the same export, the axioms every constant rests on. It fails if
  anything rests on `sorryAx`, if a trusted record rests on anything but `propext`, `Classical.choice` and
  `Quot.sound`, if a record of a library the tree compiles is missing from the export, or if the export
  declares an axiom outside the prelude. The queue asks Lean the same question with `collectAxioms`; this
  answer comes from the exported terms alone.

A kernel bug, or a record that fooled the gate and the queue, would have to fool both.

### Fuzzing

The gate scripts read what a PR supplies: its records, its Lean, its workflow files, text they print back into
the log. `scripts/ci/fuzz/` holds a [fuzz target](../scripts/ci/fuzz/_harness.py) for each that states a property
and feeds the script generated inputs until the property breaks:

| Target | Code under test | Property, for any input |
|---|---|---|
| `log_text` | `_git.plain`, `_git.annotation` | no line of the printed text can start a workflow command (`::`), and an annotation decodes back to the text |
| `lean_lex` | `lean_lex.code_only`, `_git.declared_names`, `_git.unplaced` | nothing raises, and `code_only` keeps every line break |
| `records` | `validate_records.py`, `lint_banked.py` | each passes or fails with its own message, never with a traceback |
| `workflow_rules` | `workflow_rules.py` | the checker never raises, and nothing it prints for a finding can start a workflow command |

A PR that changes a file a target covers runs that target in `pr-tests` (the PR's own code), and the merge queue
runs it again on the merged result and ejects the group if it fails, so the merge waits for it. A change that
covers no target runs nothing. Each run is [atheris](https://github.com/google/atheris) (coverage-guided,
libFuzzer) with a fixed number of inputs from a fixed seed, starting from the target's corpus
(`scripts/ci/fuzz/corpus/<target>/`; the repository's own workflows seed `workflow_rules`): a run is reproducible on
the same Python (the PR's and the queue's Pythons differ, so their runs explore differently), in about a minute and a half when every target runs (each is capped at 90 seconds, a guard for a
slow runner). [ClusterFuzzLite](https://google.github.io/clusterfuzzlite/) runs every
target each week, twenty minutes in all, shared by the four (about five minutes each; `.github/workflows/fuzz.yml`, built
by `.clusterfuzzlite/`).

Written against the gate as it was, the targets found four bugs, fixed with them: `plain` let a run of colons
through (`:::` became `: ::`); a record that is not a JSON object (`5`, `"x"`, `[1]`) ended `validate_records.py`
and `lint_banked.py` in a traceback; `workflow_rules.py` printed a YAML error, which quotes the file, into its
annotation unescaped, so a PR's workflow file could put its own workflow commands in the gate's log; and
`steps: 5` or YAML nested thousands deep crashed it.

### SonarQube Cloud (advisory)

[SonarQube Cloud](https://sonarcloud.io/project/overview?id=competemath_tengoku) reads the repository's own code, the
Python and shell under `scripts/` and `tools/` and what is under `.github/` (the workflows and Dependabot's
configuration; `sonar-project.properties` says what is left
out: the tests, the campaign's fake-credential fixtures, the fuzz corpus), and reports bugs, security hotspots,
maintainability and duplication. It has no Lean analyser, so the tree and the records are not scanned.

It is **advisory**: `.github/workflows/sonar.yml` is not a required check, the merge queue never waits for it, and a
failing quality gate blocks nothing. It runs on every pull request (a data-only one has nothing new to analyse and
passes in seconds) and, for code changes, on `main`, which keeps the baseline that "new code" is measured against
current. The default gate judges new code only: reliability, security and maintainability ratings, duplication, and
whether new security hotspots are reviewed.

**Coverage** is measured, not estimated: `sonar.yml` runs the unit tests (`scripts/tests` and `scripts/ci/tests`, the
same two commands as `pr-tests.yml`) under coverage.py and uploads the report. `.coveragerc` says how: branches too; the
gate scripts the tests run as subprocesses are measured as well (`patch = subprocess`); and every file under `scripts/`
and `tools/` counts, so a script no test imports shows as 0% instead of being left out. The figure is Python only (Sonar
has no coverage for the shell scripts or the workflows), it counts what the unit tests reach, not the fuzzers or the
Lean build, and the fuzz targets (they run under atheris in `fuzz.yml`) are the one thing left out. To see the same
numbers locally: `pip install --require-hashes --only-binary :all: -r scripts/ci/requirements/yaml.txt -r scripts/ci/requirements/coverage.txt`, then
`coverage run -m unittest discover -s scripts/tests`, the same for `scripts/ci/tests`, `coverage combine`,
`coverage report`.

The same report goes to [Codecov](https://codecov.io/gh/competemath/tengoku) (the history, the per-file view, the badge)
when the run has the `CODECOV_TOKEN` secret. It is informational (`codecov.yml`): its comment and statuses never fail
a check.

Its dependency analysis (SCA) is off. It would run `pip install -r` on every requirements file it finds, inside the
job that holds the token, and it failed on the first scan because `scripts/ci/requirements/` pins one package at
different versions for different jobs; FOSSA already scans the dependencies.

The token is the repository secret `SONAR_TOKEN`, one per repository, given to the scan step alone. A pull request
from a fork, and one Dependabot opens, gets no secrets, and its run skips the scan instead of failing.

## 3. What each check does and does not catch

- The gate reasons about **shape**, the queue about **mathematics**. A wrong
  proof always passes the gate and is always ejected by the queue; a
  mis-shaped PR never reaches the queue.
- Text rules have false positives by construction: the content lint matches a
  forbidden word inside a comment or string, the credits rule matches any
  removed line containing `Authors:`. The verdict comment says so and offers
  the report link.
- The secrets scan finds key ids, tokens and private keys inside JSON
  strings; it does not find a bare AWS secret-key value in one (the keyword
  rule needs the plain `key = value` form).
- The promotion class is granted by actor (`TENGOKU_BOT` repository variable)
  and then re-checked by the queue's regeneration diff, so even a correctly
  identified bot cannot hand-edit a generated file.
- A tombstone retracts a record everywhere the generator looks, including
  candidates; the bot's next promotion regenerates the module.
- Nothing here checks that a translation *means* the same as its source;
  that is Emissary-Archangel's job before a record is staged.

## 4. Reading a failure

**On the PR**: the checks list names the failed job; the verdict comment
names the step, quotes the error (`FAIL: …` lines become check-run
annotations, which the comment reads while the run is still in progress),
and says what to do. Push a fix and the gate re-runs; the comment updates in
place, and on success reads "all checks passed".

**In the queue**: the PR leaves the queue, auto-merge is disarmed, and the
ejection comment explains the failure. After fixing, re-queue with `gh pr
merge --squash --auto` or the *Merge when ready* button.

**If you think a check is wrong**: the *Report a gate bug* link opens an
issue with the PR, run, step and message filled in. A maintainer looks at
every one; a confirmed false positive becomes a unit test and a fix.

## 5. Running the tests yourself

```
python3 -m unittest scripts.ci.tests.test_gates -v        # 27 synthetic-repo cases
python3 -m unittest discover -s scripts/tests -v           # generator, promotion, stats
pipx install pre-commit && pre-commit run --all-files      # exactly what lint-python runs
python3 scripts/ci/fuzz/run.py --all --replay              # the fuzz targets, without atheris (seeds + 2,000 mutations)
python3 scripts/ci/fuzz/run.py --changed origin/main HEAD  # what CI runs (Linux: pip install --require-hashes -r scripts/ci/requirements/fuzz.txt)
```

To see what the queue will do with your records before you push:

```
scripts/cache.sh get                                       # newest cache; compiles nothing
git clone --filter=blob:none <corpus repo> corpora/<library>   # repo and commit from schemas/sources.json
python3 scripts/generate.py --corpus corpora/<library> --libraries <library> \
  --candidate <source_path> --candidate-names <your record names>
lake build Tengoku.<Library>.<Path>._candidate_<File>
lake build tengoku-axioms && lake env .lake/build/bin/tengoku-axioms --module Tengoku.<Library>.<Path>._candidate_<File>
```

## 6. The scenario campaign (the tests of the tests)

`scripts/ci/campaign/` opens real PRs against a sandbox copy of the repo and
checks that every check decides what it should. `gate.sh` holds 66
scenarios, each a one-line fixture with a precondition check (a fixture that
produced no change, or whose diff lacks the expected text, is refused) and
an expected failing job. `queue.sh` runs the merge-queue scenarios: every
ejection class one at a time, twelve clean PRs queued together, a broken PR
between two clean ones, a fix followed by a re-queue, a bulk promotion, a
hand edit disguised as a promotion. `guard4.sh` lands a workflow change on
`main` in the middle of a cache build and checks that the build relaunches on
the tip instead of publishing a tag the job token is not allowed to create.

The first full run (2026-09-15/16) found seven checks that passed when they
should have failed, all fixed the same night. The record of what ran and what
it found lives in the CompeteMath repository:
[`tests/tengoku-search/NOTES.md`](https://github.com/mikael-bashir/compete-math/blob/main/tests/tengoku-search/NOTES.md)
("Overnight campaign"). Run the campaign after any change to
`scripts/ci/`, the workflows or `schemas/`; it is the only thing that can
tell you a check has gone silent.

## 7. Adding a test

- A rule about records or paths: a case in `scripts/ci/tests/test_gates.py`.
  The `Repo` helper makes a throwaway git repository with one staging record,
  one trusted record, one generated module and one seeded module; write the
  change, commit, run the script, assert the exit code and the message.
- A rule about generated modules or promotion: `scripts/tests/`, with a
  fake `lake` on `PATH` where a build would be needed.
- A gate script that reads what a PR supplies: a fuzz target, `scripts/ci/fuzz/fuzz_<name>.py`, with `COVERS`
  (the files whose change runs it), `RUNS`, a `TestOneInput` that raises when the property breaks, and seeds in
  `corpus/<name>/`. `scripts/ci/tests/test_fuzz.py` replays every target, and should show yours catching the bug
  it is written against.
- A rule about the whole pipeline: one `sc` line in
  `scripts/ci/campaign/gate.sh`, or a `run_one` line in `queue.sh`, and run it
  against the sandbox.
- Every interesting bug gets a test that targets exactly it, and the test is shown to fail on the buggy version (revert the fix, or put the old
  recipe back) before it is trusted. The tests live in the repository and run in CI: for the tooling (`scripts/ci/tests`, `scripts/tests`), for the
  content (a check on what lands in the tree, such as `imports_resolve.py`) and for whatever usually breaks.

## 8. Enforcement

`main`'s ruleset has no bypass, not even for admins. `pr-gate` and `queue-gate` are required, and branches must be up to date. The merge
queue tests every group on the newest `main`, so no PR ever needs *Update branch* (tried in tengoku-sandbox#287). Every
PR needs one approval, from someone other than whoever pushed last, plus code-owner review and every review thread
resolved. History is linear, with no force pushes and no deletion, and nothing is pushed to `main` directly. The banking pipeline
opens pull requests like everyone else: Emissary-Archangel's cloud translation opens the content PRs (new staging
records), and `.github/workflows/promote.yml` opens the promotion PRs, when it is dispatched (it has no schedule since 2026-10-05: libraries arrive as factory bundles), as the bot named in the `TENGOKU_BOT`
variable (its token is the `TENGOKU_BOT_TOKEN` secret; only the step that pushes and opens the PR sees it). Each
promotion run builds up to `max_files` source files' modules on the attested cache, keeps staging changes to pure
removals, and waits for its PR before the next batch. `scripts/promote-loop.sh` is the same thing for a laptop.

### Who may change the tests

CI tests and CI configuration are owned by the maintainer's **second account only** (`.github/CODEOWNERS`, last section): every workflow
(pre-commit, PR, merge queue, scheduled), every gate script with its tests and fuzz targets, the hook and analysis configuration, the lint
allow-list, the vacuity tool, and any test file anywhere (`test_*.py`, `*_test.py`, `conftest.py`). The main account, which an agent may drive,
owns none of them, so its approval does not count for a change to them, and an author cannot approve their own pull request: a change to a test or a
check is made, or refused, by the person who drives the second account. The ruleset also dismisses an approval when new commits are pushed and
requires the last push to be approved by someone else, so a reviewed change cannot be swapped afterwards.
`scripts/ci/tests/test_codeowners.py` pins this: it finds every test and CI file by what it is, not by CODEOWNERS' patterns, and fails when one is
not owned by the second account alone (a new test directory, a renamed workflow, a loosened line), and when the main account owns any of them.

What this does not cover: repository settings. An account with admin rights can edit the ruleset itself, which is outside any file in the repository.
Keeping admin rights on the second account only closes that.
