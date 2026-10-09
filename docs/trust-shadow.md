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
   writes through the contents API; the only job with write permission takes one validated JSON file).

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
