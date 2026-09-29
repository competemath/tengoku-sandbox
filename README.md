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

<table>
<tr><th></th><th>How it shaped Tengoku</th></tr>
<tr><td nowrap><img src="https://lean-lang.org/static/apple-touch-icon.png" height="20" alt="">&nbsp;<a href="https://lean-lang.org">Lean 4</a></td><td>The language and its kernel. Every trusted theorem is checked by it, on one pinned toolchain.</td></tr>
<tr><td nowrap><img src="https://github.com/leanprover-community.png?size=40" height="20" alt="">&nbsp;<a href="https://leanprover-community.github.io">Mathlib</a></td><td>The seed: Tengoku starts from Mathlib and its dependencies, and follows its conventions.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/github/181717/ffffff" height="20" alt="">&nbsp;<a href="https://github.com/features/actions">GitHub</a></td><td>Pull requests, the merge queue and Actions run every check, the translation pipeline and the releases; artifact attestations sign the builds.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/claude" height="20" alt="">&nbsp;<a href="https://www.anthropic.com/claude-code">Claude</a></td><td>Most of Tengoku's tooling was written with Claude Code; Claude is also the translation agent and the goals reviewer.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/coderabbit" height="20" alt="">&nbsp;<a href="https://www.coderabbit.ai">CodeRabbit</a></td><td>Reviews every pull request; its comments are answered before anything merges.</td></tr>
<tr><td nowrap><img src="https://github.com/greptileai.png?size=40" height="20" alt="">&nbsp;<a href="https://www.greptile.com">Greptile</a></td><td>A second AI reviewer on every pull request.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/huggingface" height="20" alt="">&nbsp;<a href="https://huggingface.co/spaces">Hugging Face</a></td><td>Spaces host the Leak services: search, proof states and verification.</td></tr>
<tr><td nowrap><img src="https://github.com/nomeata.png?size=40" height="20" alt="">&nbsp;<a href="https://github.com/nomeata/loogle">Loogle</a></td><td>Search by name and by type: the base of Leak I.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/vercel/000000/ffffff" height="20" alt="">&nbsp;<a href="https://vercel.com">Vercel</a></td><td>Hosts competemath.com and its search API.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/neon" height="20" alt="">&nbsp;<a href="https://neon.tech">Neon</a></td><td>The Postgres database behind competemath.com.</td></tr>
<tr><td nowrap><img src="https://github.com/sigstore.png?size=40" height="20" alt="">&nbsp;<a href="https://www.sigstore.dev">Sigstore</a></td><td>Signs the provenance attached to every build and release.</td></tr>
<tr><td nowrap><img src="https://github.com/step-security.png?size=40" height="20" alt="">&nbsp;<a href="https://www.stepsecurity.io">StepSecurity</a></td><td>Audits what the gate's CI jobs reach over the network.</td></tr>
<tr><td nowrap><img src="https://github.com/trufflesecurity.png?size=40" height="20" alt="">&nbsp;<a href="https://github.com/trufflesecurity/trufflehog">TruffleHog</a></td><td>Scans every pull request for secrets.</td></tr>
<tr><td nowrap><img src="https://github.com/zenodo.png?size=40" height="20" alt="">&nbsp;<a href="https://zenodo.org">Zenodo</a></td><td>A permanent DOI for every release.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/python" height="20" alt="">&nbsp;<a href="https://www.python.org">Python</a></td><td>The gate and the library's generator.</td></tr>
<tr><td nowrap><img src="https://cdn.simpleicons.org/nodedotjs" height="20" alt="">&nbsp;<a href="https://nodejs.org">Node.js</a></td><td>Emissary-Archangel, the translation pipeline.</td></tr>
</table>

Tengoku stands on these projects, and on the authors of every library in it: thank you. The full list of the
technology, tools and writing that shaped it, from security and infrastructure to design, AI, review and CI, is in
[docs/acknowledgements.md](docs/acknowledgements.md). The mathematics comes from the libraries listed in
[schemas/sources.json](schemas/sources.json) and [LICENSE-THIRD-PARTY.md](LICENSE-THIRD-PARTY.md).
