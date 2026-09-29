# Acknowledgements

What Tengoku is built with, and what shaped how it was designed. The mathematics itself comes from the libraries
it gathers: the seeded packages in [LICENSE-THIRD-PARTY.md](../LICENSE-THIRD-PARTY.md) and every registered library
in [schemas/sources.json](../schemas/sources.json). Each theorem credits its own authors.

## Language and core libraries

- [Lean 4](https://lean-lang.org) and Lake: the language, its kernel and its build tool.
- [Mathlib](https://leanprover-community.github.io) with Batteries, Aesop, Qq, ProofWidgets, Plausible,
  LeanSearchClient, import-graph and lean4-cli: the packages the tree was seeded from.

## Checking and Lean tooling

- [lean4export](https://github.com/leanprover/lean4export): exports a Lean environment; the translation pipeline's
  per-module exports.
- [nanoda](https://github.com/ammkrn/nanoda_lib): an independent Lean kernel, the second check of every declaration
  (in progress).
- [Loogle](https://github.com/nomeata/loogle): search by name and by type, the base of the Leak I search service.
- [Pantograph](https://github.com/lenianiva/Pantograph) and
  [PyPantograph](https://github.com/stanford-centaur/PyPantograph): a machine interface to Lean's proof states, the
  base of Leak II.
- [Model Context Protocol](https://modelcontextprotocol.io): how agents talk to the Leak services.

## Projects that informed the design

- Mathlib's review process and CI: what Tengoku keeps, and what it does by machine instead.
- [Archive of Formal Proofs](https://www.isa-afp.org): a long-lived, curated archive of formal proofs.
- [Metamath](https://us.metamath.org): one database in which every step is checked.
- [Equational Theories Project](https://teorth.github.io/equational_theories/): formalisation at scale by many
  people and AI tools together; the first library Tengoku translated.
- [Lean Pool](https://github.com/Vilin97/lean-pool): many Lean projects pooled in one place.
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures): open problems stated in Lean.

## Security and supply chain

- GitHub Security Lab, [Preventing pwn requests](https://securitylab.github.com/resources/github-actions-preventing-pwn-requests/):
  why every check runs from main and reads a pull request only as data.
- [SLSA](https://slsa.dev), [Sigstore](https://www.sigstore.dev) and
  [GitHub artifact attestations](https://docs.github.com/en/actions/security-for-github-actions/using-artifact-attestations):
  provenance for every build and release.
- [StepSecurity Harden-Runner](https://www.stepsecurity.io): audits what the gate's CI jobs reach over the network.
- [TruffleHog](https://github.com/trufflesecurity/trufflehog) and [detect-secrets](https://github.com/Yelp/detect-secrets):
  secret scanning.
- [Developer Certificate of Origin](https://developercertificate.org): the sign-off on every commit.
- Dependabot: keeps the pinned actions current.

## Review, CI and delivery

- [GitHub Actions](https://github.com/features/actions), rulesets and the
  [merge queue](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue).
- [CodeRabbit](https://www.coderabbit.ai) and [Greptile](https://www.greptile.com): AI review of every pull request.
- [pre-commit](https://pre-commit.com), [Ruff](https://docs.astral.sh/ruff/), [actionlint](https://github.com/rhysd/actionlint)
  and [ShellCheck](https://www.shellcheck.net).

## Infrastructure

- [Hugging Face Spaces](https://huggingface.co/spaces): hosts the Leak services.
- [Vercel](https://vercel.com), [Neon](https://neon.tech) and [Upstash](https://upstash.com): competemath.com, the
  search API and its index, rate limiting.
- GitHub Releases and [zstd](https://facebook.github.io/zstd/): the compiled library and its top-ups.
- [Zenodo](https://zenodo.org): a DOI for every release.

## AI

- [Claude](https://www.anthropic.com/claude) and [Claude Code](https://www.anthropic.com/claude-code) (Anthropic):
  Tengoku's tooling was largely written with Claude Code. Claude is the translation agent in the pipeline and the
  reviewer that writes the Suggestions in [GOALS.md](../GOALS.md).
- [Emissary-Archangel](https://github.com/competemath/emissary-archangel): the translation pipeline that turns
  registered libraries into Tengoku records.
