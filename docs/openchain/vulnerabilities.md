# Known vulnerabilities: finding, handling, communicating

The procedure for ISO/IEC 18974 (security assurance). Who does what is in [program.md](program.md); what threatens the
project in the first place is in [threat-model.md](threat-model.md).

## 1. What Tengoku uses (the component records)

| Component | Recorded in | Kept safe by |
|---|---|---|
| GitHub Actions used by the workflows | `uses:` lines in `.github/workflows/` | every action pinned to a full commit with its tag as a comment (`workflow_rules.py`, rule `pinned`); Dependabot updates them weekly |
| Python packages of the CI scripts | `scripts/ci/requirements/*.txt` | pinned with hashes, installed with `pip install --require-hashes`; Dependabot updates them weekly |
| Lean toolchain | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | one pinned toolchain; the tree has no Lake dependencies (seeded and generated, see `LICENSE-THIRD-PARTY.md`) |
| Third-party Lean libraries | `schemas/sources.json`: each source's licence and, for compiled libraries, repository and commit | the commit is fixed; a record is trusted only when the tree builds with it |
| Build tools (elan installer, lean4export, nanoda) | the workflows that run them | pinned to a commit |

The archive of what was used is the git history (every record names its source at a fixed commit), the attested
release files, and the Zenodo deposit of each release.

## 2. Finding known vulnerabilities

| Method | Runs | Looks at |
|---|---|---|
| Dependabot | weekly | Actions and Python dependencies |
| CodeQL | every pull request, every push, Mondays | the Python and the workflows |
| SonarQube Cloud | every pull request, `main` on code changes | the Python, shell and workflows: bugs, security hotspots, vulnerabilities |
| FOSSA | continuously | dependency vulnerabilities and licences |
| OpenSSF Scorecard | Mondays | the repository's practices (pinning, branch protection, signed releases, ...) |
| Secret scanning in the PR gate | every pull request | TruffleHog and detect-secrets over the change |
| Fuzzing | Tuesdays, and on a PR that changes a gate script | the gate scripts' parsers |

Newly published vulnerabilities after a release are found by the same services running on `main`; the independent check
also re-checks the newest commit of `main` nightly.

## 3. Following up

1. **Triage**: a finding is real, a false positive for this repository (a script only workflows call, with arguments the
   workflow supplies), or accepted risk. The decision and the reason are recorded where the finding is: the Sonar
   status and comment, the dismissal reason of a CodeQL or Dependabot alert, or the pull request that fixes it. "No
   action was needed" is recorded the same way.
2. **Fix** through a pull request. A change to a workflow, the gate or CI scripts is proved in
   [tengoku-sandbox](https://github.com/competemath/tengoku-sandbox) first; every Dependabot update is too.
3. **Aim**: a finding that is exploitable here is fixed within seven days; others by the next review.
4. **Before release**: the merge queue builds the exact merged tree, the independent check (axiom scan and a second
   proof checker) must pass for a release's commit, and required checks and the maintainer's approval gate every merge.

## 4. Communicating

A vulnerability in Tengoku's own releases is published as a GitHub security advisory on `competemath/tengoku`, naming the
affected versions and the fix, crediting the reporter unless they ask otherwise. A release fixing it says so in its notes.
Risk information that travels with a release: the manifest (toolchain, counts, the dataset's sha256) and the
Sigstore build-provenance files, which anyone can verify; a release also carries its bill of materials and the independent
check's axiom report (section 6).

## 5. Inquiries from third parties

Anyone can report a vulnerability or ask about one through GitHub's private vulnerability reporting (the repository's
Security tab); `SECURITY.md` says what is in scope. The maintainer:

1. aims to acknowledge within seven days;
2. reproduces it, in the sandbox where an attack must not touch the repository itself;
3. fixes it through a pull request, and publishes an advisory;
4. tells the reporter, and records the case in the review log of [program.md](program.md).

## 6. The bill of materials

Each release (`vMAJOR.MINOR.PATCH`, cut by `.github/workflows/release.yml`) carries a CycloneDX 1.5 bill of materials
(`scripts/sbom.py`): the Lean toolchain, every package the tree was seeded from and every library whose records the tree
holds (a package and a compiled library with its exact commit). The release, the bill and the axiom report of the independent check are attested, and
the bill is bound to the source archive ([docs/releases.md](../releases.md)). This is the archived record of what a
release used, beside the component table above.
