<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>An AI-first formal mathematics library for Lean 4.</em></p>

## About
Significant formal math projects are fragmented across hundreds of different sources. We pull them
into one unified, verified tree, under the same toolchain. Tengoku aims to provide continuously improving,
reliable context for automated theorem provers.

## Developers
Tengoku hosts **Leak I**, a free MCP service that lets an LLM or agent query
formal theorems by meaning or by type, here: https://barkingtree-leak-i.hf.space/sse (no auth configurations required).

Search the whole library right now [here](https://competemath.com/tengoku).

Prefer HTTP? Endpoint, input and output shapes: [API](docs/api.md).

Want to host your own infrastructure? The code for those who want to self-serve is
[here](https://github.com/mikael-bashir/leak-services).

## Contributors
Anyone can contribute, by hand or with AI. Before you submit:

- **Verification is automatic.** Leak checks every submission: if it compiles
  cleanly and isn't just a longer route to something the tree already reaches,
  it's in.
- **Credit is permanent, and shared.** Put a docstring above your theorem naming
  the human author, any AI used, and a link to you (GitHub, LinkedIn, ORCID, or
  your [CompeteMath ID](https://competemath.com/whoami)). It stays in the tree.

  ```lean
  /-- The sum of the first `n` odd numbers is `n ^ 2`.

  Author: Ada Lovelace (https://github.com/ada), with Claude Fable 5.1. -/
  theorem sum_range_odd (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
    ...
  ```

  One sentence on what it says, then one line starting with `Author:`. That word
  is what the checks key on: no pull request can remove or edit the line once it
  is in.
- **Submitting a whole project?** Point the
  [bulk attribution tool](tools/attribute/README.md) at the directory with your
  credit string once; it writes the docstrings for you.
- **Tiers.** Submissions start in `tentative` or `staging` and are promoted to
  `trusted` only once Leak's own toolchain has compiled them from scratch.

## Full documentation
This is the quick start. The full manual — merge queue, tiers, toolchain, every
seeded library — is at [competemath.com/about/tengoku](https://competemath.com/about/tengoku).

## Tech

[Lean 4](https://lean-lang.org) · [Mathlib](https://github.com/leanprover-community/mathlib4) · [GitHub](https://github.com/features/actions) · [Claude Code](https://www.anthropic.com/claude-code) · [CodeRabbit](https://www.coderabbit.ai) · [Hugging Face](https://huggingface.co/spaces) · [FastMCP](https://gofastmcp.com) · [Loogle](https://github.com/nomeata/loogle) · [Pantograph](https://github.com/lenianiva/Pantograph) · [lean4export](https://github.com/leanprover/lean4export) · [lean4checker](https://github.com/leanprover/lean4checker) · [nanoda](https://github.com/ammkrn/nanoda_lib) · [Next.js](https://nextjs.org) · [Vercel](https://vercel.com) · [Neon](https://neon.com) · [zizmor](https://github.com/zizmorcore/zizmor) · [Harden-Runner](https://github.com/step-security/harden-runner) · [TruffleHog](https://github.com/trufflesecurity/trufflehog) · [detect-secrets](https://github.com/Yelp/detect-secrets)

Tengoku stands on these projects, and on the authors of every library in it: thank you. How each one shaped
Tengoku, and the full list of the technology, tools and writing behind it (security, infrastructure, design, AI,
review and CI), is in [docs/acknowledgements.md](docs/acknowledgements.md). The mathematics comes from the
libraries listed in [schemas/sources.json](schemas/sources.json) and [LICENSE-THIRD-PARTY.md](LICENSE-THIRD-PARTY.md).
