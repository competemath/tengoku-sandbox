# Threat model

The structural and technical threats to Tengoku, and what answers each. It is the basis for the checks in
[How Tengoku is tested](../testing.md) and is reviewed with the programme ([program.md](program.md)).

**Assets:** the Lean tree and the records (what people build on), the release and cache files (what they download), the
repository's secrets and workflow permissions, and the maintainer's accounts.
**Actors:** a contributor (honest, careless or hostile), a hostile upstream library, a compromised dependency or action,
someone with a leaked token, and an attacker who targets the maintainer's accounts.

| Threat | Answer in the repository |
|---|---|
| A pull request that runs hostile code in CI or changes the rules that judge it | the PR gate runs from `main` (`pull_request_target`): its code, not the PR's, judges the PR; the PR's own tests run with a read-only token and no secrets; workflow rules (`workflow_rules.py`) lint every workflow change; changes to tooling always wait for a maintainer |
| A record that is unsound or runs code when built | trusted only after the merge queue builds it; a record may not use `sorry` or an axiom beyond the standard ones; banked-content lint; the independent check re-verifies the exported tree with a second proof checker and an axiom scan |
| A tampered cache or release | every cache part and release has a build-provenance attestation; `scripts/cache.sh get` refuses an unattested part |
| A compromised action or package | actions pinned to full commits; Python packages pinned with hashes; Dependabot weekly; Scorecard weekly |
| A leaked secret | secret scanning (TruffleHog, detect-secrets) on every change; tokens only on the step that needs them; no secrets for fork or Dependabot runs; harden-runner records each job's network egress |
| A licence contamination | the allow-list of sources with their licences; copyleft refused ([licence-compliance.md](licence-compliance.md)) |
| A flaw in the gate itself | proved in tengoku-sandbox first; the gate scripts are unit-tested (coverage measured), fuzzed, and tested against a campaign of deliberately bad pull requests |
| Compromise of the maintainer's account | the ruleset needs a second approval and code-owner review, and nothing merges outside a pull request; beyond that it rests on the account's own security, and it is a single-person risk the documents do not hide |

**Not covered:** the correctness of an upstream library's mathematics beyond "it compiles and is axiom-clean" (a poor
formalisation is a normal issue, not a vulnerability), the hosted services, and anyone's local build.
