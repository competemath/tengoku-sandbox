<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>Formal mathematics from many Lean projects, translated onto one Lean version and machine-checked.</em></p>
<p align="center">
<a href="lean-toolchain"><img src="https://img.shields.io/badge/dynamic/regex?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Flean-toolchain&search=v%5B0-9.%5D%2B%28-rc%5B0-9%5D%2B%29%3F&label=Lean%204&color=blue" alt="Lean 4 toolchain"></a>
<a href="https://competemath.com/tengoku"><img src="https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fcompetemath.com%2Fapi%2Ftengoku%2Fstats&query=%24.trusted&label=trusted%20theorems&color=2e7d32" alt="Trusted theorems"></a>
</p>

## About

Formal mathematics is mathematics that a computer can check, step by step. It is scattered across many separate projects,
written for different versions of Lean 4. Tengoku (天国) gathers theorems from many formal mathematics projects into one
Lean 4 library on a single pinned toolchain. A theorem is _trusted_ only once the relevant library checks have passed: it
builds with no `sorry`, uses only the standard axioms, and its assumptions are checked not to contradict.
Every record links to its source at a fixed commit and carries its licence and credit.

Tengoku and [Leak](https://competemath.com/about/leak) are parts of one service: Tengoku is the library, and Leak is
the intended interface. Leak is tooling and a harness for agent-driven proving over MCP, providing search, proof-state
interaction and verification services. It is not the prover; any MCP-capable system can use it.

(Tengoku can be interpreted to mean sky kingdom, or heavenly abode. This represents our ambition for the useful knowledge in this repository to reach the skies.)

## Try it

- **Add the Leak MCP tools to your agent** (free, no sign-up): [Leak I](https://github.com/mikael-bashir/leak-i) searches
  (Loogle + Moogle + ChromaDB), [Leak II](https://github.com/mikael-bashir/leak-ii) steps through proofs (Pantograph service with efficient proof state switching),
  [Leak IV](https://github.com/mikael-bashir/leak-iv) verifies a script (Lean kernel daemon). All of these services use the Tengoku
  environment, and are provided like this to make it easy for the community to experiment - no SLA or uptime guarantee is provided.
  <details><summary>Connection URLs</summary>

  ```
  claude mcp add --transport sse tengoku-search https://barkingtree-leak-i.hf.space/sse
  claude mcp add --transport sse tengoku-proof  https://barkingtree-leak-ii.hf.space/sse
  claude mcp add --transport sse tengoku-verify https://barkingtree-leak-iv.hf.space/sse
  ```

  </details>

- **Search it on the web:** [competemath.com/tengoku](https://competemath.com/tengoku), in plain English or by name.
- **Run your own:** the [service code](https://github.com/mikael-bashir/leak-services).
- **HTTP API:** [docs/api.md](docs/api.md).
- **Download it:** clone this repository and run `scripts/cache.sh get` to download the compiled library.

## Contributors

Anyone can contribute, by hand or with AI. Because of the nature of this project, there are many indirect ways
to contribute and support. Interacting with and providing feedback for the main [site](https://competemath.com), as
well as using and improving the [Leak](https://github.com/mikael-bashir/leak-services) services, all support Tengoku indirectly.

We expect that realistic contributions directly to the project via pull requests will require AI assistance. This is because
parts of the repository change before a human can fully understand it. We understand that this creates a barrier to entry for
contributors due to factors beyond their control. We are not really in a position to solve this issue; if you
want to contribute directly, or want to learn about something that interests you, but can't because you don't
have access to AI tools, get in [touch](mailto:bashir.mikael@outlook.com?subject=Tengoku) - we will try to help if we have the availability.

For every other prospective contributor, you may work on whatever you wish, even if it initially doesn't
seem like it is related to Tengoku (if you have an odd idea or need particular permissions, get in touch with the link above).
However you contribute, it would be useful to make mention of what you are working on, or would like work to be directed
at, in the [goals](GOALS.md) file.

[How credit works](docs/credit.md) · [Contributing](CONTRIBUTING.md) · [How a theorem gets in](docs/how-a-pr-flows.md) · [Code of Conduct](https://github.com/competemath/.github/blob/main/CODE_OF_CONDUCT.md) · [Posting guidelines](https://github.com/competemath/.github/blob/main/POSTING.md) · [Found an issue, or have an idea?](https://github.com/competemath/tengoku/issues/new) · [Found a security problem?](SECURITY.md).

If you are unsure if an issue is a security problem, assume it is.

## Learn more

- [Why Tengoku does not trust the toolchain](docs/why-cynical.md): case studies of Lean 4 failures
- [How Tengoku stays reliable](docs/reliability.md)
- [Training on Tengoku](docs/for-labs.md): what labs must do, and what we ask
- [What Tengoku checks](docs/why-tengoku.md)
- [The full manual](https://competemath.com/about/tengoku)
- [Security and licence compliance](docs/openchain/README.md) (OpenChain ISO/IEC 18974 and 5230)
- [Acknowledgements](docs/acknowledgements.md): the projects and people Tengoku stands on
- Cite it: [10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400), or the _Cite this repository_ button

## Thanks

Tengoku makes extensive use of the Lean and Mathlib ecosystem - to the authors who make Tengoku possible, thank you.

<a href="https://snyk.io"><img src="https://cdn.simpleicons.org/snyk" height="18" alt="Snyk"></a>&nbsp;**Security, with [Snyk](https://snyk.io).** Tengoku is proud to be a member of Snyk's [Secure Developer Program](https://snyk.io/open-source/), which arms open-source maintainers with its advanced developer-security platform.

<a href="https://gitar.ai"><img src="docs/img/gitar.svg" height="18" alt="Gitar"></a>&nbsp;**Code review and CI repair, with [Gitar](https://gitar.ai).** Tengoku is proud to have been admitted to Gitar's open-source program, which gives open-source maintainers its AI code-review and CI-fixing agent.

## Funding and affiliation

Tengoku is one of the services of [CompeteMath](https://competemath.com/about). CompeteMath has no intention of generating income with any of its projects. CompeteMath is not affiliated with, nor does it support, any particular organization, corporate entity, or political group. Anyone considering donating or partnering with us should know that Tengoku will not allow any influence over the governance of this repository, nor its accessibility, the integrity of its contents, or [Tengoku's goals](GOALS.md).

## Badges

<p align="center">
<a href="https://doi.org/10.5281/zenodo.23050400"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.23050400.svg" alt="DOI"></a>
<a href="https://scorecard.dev/viewer/?uri=github.com/competemath/tengoku"><img src="https://api.scorecard.dev/projects/github.com/competemath/tengoku/badge" alt="OpenSSF Scorecard"></a>
<a href="https://www.bestpractices.dev/projects/15102"><img src="https://www.bestpractices.dev/projects/15102/badge" alt="OpenSSF Best Practices"></a>
<a href="LICENSE"><img src="https://img.shields.io/badge/licence-Apache--2.0-blue" alt="Licence: Apache-2.0"></a>
<a href="https://app.fossa.com/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku?ref=badge_small"><img src="https://app.fossa.com/api/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku.svg?type=small" alt="FOSSA Status"></a>
<a href="https://sonarcloud.io/summary/new_code?id=competemath_tengoku"><img src="https://sonarcloud.io/api/project_badges/measure?project=competemath_tengoku&amp;metric=alert_status" alt="SonarQube Cloud quality gate"></a>
<a href="https://codecov.io/gh/competemath/tengoku"><img src="https://codecov.io/gh/competemath/tengoku/graph/badge.svg" alt="Codecov"></a>
</p>
