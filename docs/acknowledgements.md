# Acknowledgements

What Tengoku is built with, and what shaped how it was designed. The mathematics itself comes from the libraries
it gathers: the seeded packages in [LICENSE-THIRD-PARTY.md](../LICENSE-THIRD-PARTY.md) and every registered library
in [schemas/sources.json](../schemas/sources.json). Each theorem credits its own authors.

## Similar libraries, and what we took from them

- [Mathlib](https://github.com/leanprover-community/mathlib4): the seed. Tengoku keeps its layout by topic and
  its shared build cache, and does by machine much of what its reviewers do by hand.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti): its review looks for statements that prove nothing.
  Tengoku's vacuity check and AGENTS.md came from reading it.
- [Palomar](https://palomar-registry.org): checks every result with two independent kernels. One reason for
  Tengoku's second check with nanoda.
- [Lean Pool](https://github.com/Vilin97/lean-pool): many projects pooled in one repository. Its challenge board,
  paper and DOI showed how a library becomes citable.
- [merely-true](https://github.com/merely-true/merely-true): merges whatever compiles and deletes what breaks.
  Tengoku chose the opposite: nothing is deleted.
- [comparator](https://github.com/leanprover/comparator): checks a proof against its statement on one toolchain.
  Tengoku's translation check compares statements across toolchains, which comparator cannot.
- Also studied: [OpenGauss](https://github.com/math-inc/opengauss) and
  [lean4-skills](https://github.com/cameronfreer/lean4-skills), [Aristotle](https://aristotle.harmonic.fun),
  [zoogle](https://github.com/e-gubarev/zoogle), [Blossom](https://github.com/oe-parks/Blossom),
  [cat-rw](https://github.com/leomayer1/cat-rw), [LearnedBranching](https://github.com/xvade/LearnedBranching)
  and [LEANForExplainableAI](https://github.com/ssingh92-ops/LEANForExplainableAI).
- Where the libraries were found: the Lean community's
  [project list](https://leanprover-community.github.io/lean_projects.html),
  [awesome-lean4](https://github.com/tomhoule/awesome-lean4), [best-of-lean4](https://github.com/34j/best-of-lean4)
  and [Reservoir](https://reservoir.lean-lang.org).

## Lean and checking

- [Lean 4](https://lean-lang.org), Lake and [elan](https://github.com/leanprover/elan): the language, its kernel,
  its build tool and its toolchain installer. Leak IV and the translation check talk to Lean's own language server.
- Mathlib with Batteries, Aesop, Qq, ProofWidgets, Plausible, LeanSearchClient, import-graph and lean4-cli: the
  packages the tree was seeded from.
- [lean4export](https://github.com/leanprover/lean4export): writes out every declaration. It feeds the translation
  check and the independent check.
- [lean4checker](https://github.com/leanprover/lean4checker): its replay code is the core of the translation check.
- [nanoda](https://github.com/ammkrn/nanoda_lib): an independent Lean kernel that re-checks every declaration in the
  tree (being added).
- [Loogle](https://github.com/nomeata/loogle): search by name and by type, the base of Leak I. Morph Labs' Moogle
  gave Leak I its search by meaning, and its name.
- [Pantograph](https://github.com/lenianiva/Pantograph) and
  [PyPantograph](https://github.com/stanford-centaur/PyPantograph): a machine interface to Lean's proof states, the
  base of Leak II. [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) was its first version.
- [Keep the Proof State Live](https://arxiv.org/abs/2605.25556) (Shen and Shi): why Leak II keeps many proof states
  in one Lean process. The [Kimina Lean Server](https://arxiv.org/abs/2504.21230) is the model for more Leak IV
  workers.

## Security and supply chain

- [zizmor](https://github.com/zizmorcore/zizmor): we ran it and read its source. It found two gaps in our
  workflows, and Tengoku's own workflow checker grew from it.
- [actionlint](https://github.com/rhysd/actionlint) and [ShellCheck](https://www.shellcheck.net): check every
  workflow and its shell steps.
- GitHub Security Lab's [guide to pwn requests](https://securitylab.github.com/resources/github-actions-preventing-pwn-requests/)
  and the [tj-actions compromise](https://github.com/advisories/GHSA-mrrh-fwg8-r2c3): why every check runs main's
  code and every action is pinned to a commit.
- [GitHub artifact attestations](https://docs.github.com/en/actions/security-for-github-actions/using-artifact-attestations),
  signed with [Sigstore](https://www.sigstore.dev): every cache and release is signed, and checked before use.
- [CycloneDX](https://cyclonedx.org): the bill of materials in every release (being added).
- [StepSecurity Harden-Runner](https://github.com/step-security/harden-runner): watches and limits what CI jobs
  reach over the network.
- [TruffleHog](https://github.com/trufflesecurity/trufflehog) and [detect-secrets](https://github.com/Yelp/detect-secrets):
  secret scanning in the gate and before every commit.
- [Developer Certificate of Origin](https://developercertificate.org): the sign-off on every commit.
- Also studied: [gitleaks](https://github.com/gitleaks/gitleaks), [SonarQube](https://www.sonarsource.com/products/sonarqube/)
  and [Aikido](https://www.aikido.dev).

## Review, CI and delivery

- [GitHub](https://github.com/features/actions): pull requests, rulesets and the merge queue; Actions for every check,
  the nightly build and translation; Dependabot, code owners, private vulnerability reports, and Releases for the
  [zstd](https://facebook.github.io/zstd/)-compressed build caches.
- [CodeRabbit](https://www.coderabbit.ai): reviews every pull request, and its comments are resolved before
  anything merges. It replaced the blind re-proof test.
- [pre-commit](https://pre-commit.com) and [Ruff](https://docs.astral.sh/ruff/): the same lint on your machine
  and in CI.

## Services and infrastructure

- [Hugging Face](https://huggingface.co/spaces): Spaces host Leak I, II and IV. Its hub supplies the model that
  sentence-transformers and transformers.js use for search by meaning.
- [FastMCP](https://gofastmcp.com), on [Starlette](https://starlette.dev) and [uvicorn](https://uvicorn.dev): the
  servers behind Leak I, II and IV and the translation check.
- [ChromaDB](https://www.trychroma.com): Leak I's index for search by meaning.
- [uv](https://docs.astral.sh/uv/): builds the Leak service images.
- [Next.js](https://nextjs.org) on [Vercel](https://vercel.com): competemath.com/tengoku, its search API, and the
  Emissary-Archangel console.
- [Neon](https://neon.com) with [pgvector](https://github.com/pgvector/pgvector): the Postgres search index.
- [Zenodo](https://about.zenodo.org) and the [Citation File Format](https://citation-file-format.github.io): a DOI
  and a citation for every release.

## AI

- [Claude](https://www.anthropic.com/claude) and [Claude Code](https://www.anthropic.com/claude-code) (Anthropic):
  most of Tengoku's tooling was written with Claude Code. On GitHub Actions, Claude is the translation agent in
  [Emissary-Archangel](https://github.com/competemath/emissary-archangel) and the reviewer that writes the
  Suggestions in [GOALS.md](../GOALS.md).

## Visibility

- NiubiStar's support team: free advice to tell one story, a contributor's path from theorem to trusted record,
  and to explain the trust model to labs. The goals page, the pull request walkthrough, headline theorems and
  citable snapshots came from it.
