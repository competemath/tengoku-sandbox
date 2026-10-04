# The programme: policy, scope, people, metrics

This page is the programme's policy and its record of who does what. It serves both OpenChain specifications (ISO/IEC
18974 for security assurance, ISO/IEC 5230 for licence compliance). Review log at the end.

## Policy

Tengoku distributes a Lean 4 library, its dataset and the cache and release files that carry them, so a flaw in what it
accepts, builds or publishes, or a licence it breaks, reaches everyone who builds on it. The policy:

1. **Nothing enters the tree unchecked.** Every change, the maintainer's included, goes through a pull request, the PR
   gate and the merge queue ([How Tengoku is tested](../testing.md)); a record is trusted only once the tree builds with
   it and it uses no `sorry` and only the standard axioms.
2. **Every file keeps its upstream licence.** A record and the module generated from it stay under the licence of the
   library they came from, recorded in `schemas/sources.json`; copyleft libraries are not accepted
   ([LICENSE-THIRD-PARTY.md](../../LICENSE-THIRD-PARTY.md)).
3. **Known vulnerabilities in what Tengoku uses are found automatically and handled in the open or privately as
   [vulnerabilities.md](vulnerabilities.md) says**, and a report has a first-reply target of seven days (`SECURITY.md`).
4. **Releases are attested** (Sigstore build-provenance files, a manifest with the dataset's sha256) and are checked a
   second time, independently, before they are published.
5. **Changes to the gate itself are proved first** in [tengoku-sandbox](https://github.com/competemath/tengoku-sandbox).

This policy is communicated to every participant by being in the repository: it is linked from the README, and
`CONTRIBUTING.md` is the page a contributor reads before a first pull request.

## Scope and limits

**In scope ("Supplied Software"):** the contents of `competemath/tengoku` as released: the Lean tree (`Tengoku/`), the
records (`data/`), the scripts and workflows that build, check and publish them, and the release and cache files.
**Out of scope:** the upstream libraries' own code and security (Tengoku records which commit it took and checks it
compiles and is axiom-clean; it does not audit upstream proofs' authors or their repositories), the hosted services
(Leak I, II and IV) except where they serve this library, and anyone's local build.

## Roles and participants

**Participants are the people with write access or the right to approve a merge.** Contributors who open pull requests
are not participants; the gate and the maintainer's approval treat their work as untrusted until it has been checked.

| Role | What it covers | Held by |
|---|---|---|
| Programme manager and maintainer | owns this folder, merges, publishes releases, answers inquiries | Mikael Bashir (`@mikael-bashir`) |
| Second approver | approves what the maintainer's main account opens, since GitHub never lets an author approve their own pull request | the maintainer's second account (`@mikaelbashir14096545`) |

Both accounts belong to the same person. That is a limit of the programme (one pair of eyes), and the reason the checks
are automated: the gate, the queue and CodeRabbit are the independent reviewers that a second human would otherwise be.

### Competence

Self-assessed by the maintainer on 2026-10-02: familiar with the shapes of vulnerability that matter for this project
(supply-chain and CI-injection attacks on workflows, secret exposure, path traversal and command injection in scripts,
untrusted code reaching a build), and working with the tools that find them (CodeQL, Sonar, Scorecard, Dependabot,
fuzzing). Not a professional security specialist. Where a finding is beyond that, the route is the upstream project's
advisory, GitHub's advisory database and the project's reviewers, not guesswork.

### Awareness

The maintainer knows the objectives above (they are the maintainer's own), where this policy is (here), what is
expected of a participant (follow the PR flow and the procedures in this folder, do not bypass the gate, keep tokens out
of the repository), and what failing to do so means (a merge that skipped a check is reverted, the check is fixed and the
event is written into the review log). The repository's rules (ruleset, required checks, code owners) enforce the same
on every participant.

### Staffing and funding

There is no funding and no staff beyond the maintainer. The programme is scoped to be run by one person: detection,
testing and the second review are automated, free to run for a public repository, and written down so they do not
depend on memory. That is the sense in which it is "adequate", and it is a limit: availability, not tooling, is the
constraint, which is why a report has a first-reply target of seven days, not a faster one.

### Expertise

No adviser is retained. Legal questions about a licence are answered from the licence texts and the upstream
repository's statement; when a question is beyond that the record is withdrawn until it is settled (see
[licence-compliance.md](licence-compliance.md)). A security question beyond the maintainer's competence is taken to the
upstream project or GitHub's private vulnerability reporting channel.

## Metrics

Read from the live services, not typed in by hand:

| Metric | Where | Why |
|---|---|---|
| OpenSSF Scorecard score | [scorecard.dev](https://scorecard.dev/viewer/?uri=github.com/competemath/tengoku) | the repository's practices, scored weekly |
| Open vulnerabilities and code smells | [SonarQube Cloud](https://sonarcloud.io/project/overview?id=competemath_tengoku) | code quality trend |
| Test coverage | SonarQube Cloud and [Codecov](https://codecov.io/gh/competemath/tengoku) | how much of the scripts the unit tests reach |
| Open Dependabot pull requests and their age | the repository's pull requests labelled `dependencies` | how fast known-vulnerable dependencies are updated |
| Days from a report to the first reply | the Security tab and issues | the seven-day aim in `SECURITY.md` |
| Sources removed for licence reasons | `LICENSE-THIRD-PARTY.md` section 4 | compliance events |

## Review log

The programme, these documents and the metrics are reviewed at least every six months, and after any security report or
licence incident. Each review adds a row: the date, what changed, what was found.

| Date | Review | Outcome |
|---|---|---|
| 2026-10-02 | Initial adoption: documents written from what the repository does today | gaps listed in [README.md](README.md#known-gaps); next review due by 2027-04-02 |
