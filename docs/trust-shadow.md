# Trust program, shadow mode

Three public repositories decide how far to trust AI-made content, from evidence that anyone can re-check:
[tengoku-wounder](https://github.com/competemath/tengoku-wounder) tests the gates themselves with planted defects,
[tengoku-praiser](https://github.com/competemath/tengoku-praiser) writes down the reasons to trust (and prints a plain-language
trust card), [tengoku-juridicator](https://github.com/competemath/tengoku-juridicator) weighs it all with a fixed rulebook.
This repository runs them **in shadow**: advisory, silent, blocking nothing.

## What happens on a PR

`.github/workflows/trust-shadow.yml` runs when `pr-gate` finishes on a PR (main's copy of the file; the PR's code is never
checked out or run).

1. **Gate health.** The wounder's planted-defect cases for the *static* layer run against `scripts/ci/canary_gate.py`, which
   is the compiled-tier content lint (`allowlist.py`) as a yes/no. A defect the lint lets through, or a known-good case it
   refuses, is a failure; a gate that is not proven healthy accepts nothing.
2. **Evidence.** `scripts/ci/trust_shadow.py gather` runs main's own `lint_banked.py`, `sorry_scan.py` and `classify.py` over
   the PR as git objects and reads the commit's check runs. Required checks (`pr-gate`) become mechanical records; the other
   checks are noted and weigh nothing.
3. **Judgement.** The juridicator decides under `scripts/ci/trust-shadow-policy.json` (what each class of PR must show; no
   merit-based lowering of scrutiny). The praiser renders the trust card into the run summary.
4. **Ledger.** One verdict line is appended to `ledger.jsonl` on the `trust-ledger` branch (hash-chained, compare-and-swap
   writes through the contents API; the job with that write permission takes one validated JSON file).
5. **Merge eligibility.** A third job publishes the verdict as a `merge eligibility` check run on the PR head (below). It, too, takes only the
   judge's validated artifact and holds nothing but `checks: write`.

## The `merge eligibility` check

`scripts/ci/trust_shadow.py eligibility` (job `eligibility` of `trust-shadow.yml`) turns the verdict into the check run `merge eligibility` with `warden.eligibility.build_check_run`:
`ACCEPT` is `success`, `HOLD` and `ESCALATE` are `neutral`, `REJECT` is `failure`. The check's `external_id` binds **the repository, the PR number, the head commit, the merge base, the digest
of the verdict, the hash of the policy and the digest of the evidence**; its text is fixed phrases, nothing from the verdict's free text. The judge job writes the PR number and the merge base
(`git merge-base`) to `meta.json` beside the verdict; the job re-validates all three files, because they come from an artifact, whatever made it.

It then reads the check back the way a merge engine would (`warden.eligibility.verify_check`): only a completed check from the **expected App**, for the live head, whose payload agrees
with its conclusion and whose merge base is still the live one, counts. The job fails when it cannot read its own check back as that App's, which is how a wrong App id shows.

**Advisory.** No ruleset requires `merge eligibility`, and nothing merges or refuses on it. **Until the maintainer creates the judge GitHub App** (`tengoku-warden` `docs/RUNBOOK.md`, item 1: Checks
read and write only, installed on this repository), the check is made by the GitHub Actions identity, **app id 15368**, and `verify_check` is pinned to that id (`--app-id`). When the App exists, give
the job its token and pass its id; then a ruleset can require `merge eligibility` pinned to that `integration_id`, and no other identity with write access can forge it. Credit: the idea of an
admission that only one App can make, bound to the exact head and merge base, is Tau Ceti's bors-ng fork (PR 6, 2026-10-06); binding the evidence digest is ours.

## Backfill (run on the 38 most recent sandbox PRs, 2026-10-09)

Merged PRs: 19 accepted, 4 held (their head commit has no passing `pr-gate` run: cancelled, or merged without one), none rejected.
PRs whose `pr-gate` failed (#397, #399, #410): rejected. Running it over history found three bugs before they could reach a
live PR: a crashed script was recorded as a failure, `sorry` in tool files blocked tooling PRs, and a re-run check was
counted twice. For tooling PRs the verdict today mostly mirrors `pr-gate`; it gets sharper as the evidence below is added.

## Labelling

Run **trust-label** (Actions, by hand) with a commit and `accept` or `reject` when you know what a case deserved. Track records
and precedents are built only from these labels. Without labels the system stays at its cautious defaults.

## What it does not do yet

- The compile layer (axiom collection, which is what sees `sorry`), vacuity, fidelity and tree-wide checks are not exercised
  by the canaries: they need Lean. Run `python3 -m wounder run-canaries --layer axioms|vacuity|tree` on a runner that has built
  the tree to cover them.
- No proof-checker, rebuild or provenance evidence is produced for a PR yet, so "accepted" in shadow means *nothing required
  failed*. The queue's independent checks are the next evidence to connect.
- Records are not signed (the juridicator supports signatures; turn `require_signatures` on once producers have keys).
- The audit lottery (`wounder lottery`) is not running: it needs a secret salt held outside the repository.

## Changing the pins

The three tools are pinned to reviewed commits in `trust-shadow.yml` and `trust-label.yml`. `scripts/ci/trust_vendor/` holds
the evidence contract byte for byte with its hash; refresh it from the juridicator, never by hand.
