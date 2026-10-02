<p align="center"><img src="logo.png" alt="Tengoku" width="150"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><b>Formal mathematics from many Lean projects, translated onto one Lean version and checked by machine.</b><br>
For AI provers and the people who work with them: search it, import it, or hand it to an agent.<br>
Every theorem keeps its source, licence and credit.</p>
<p align="center">
[Lean toolchain badge] [trusted theorems badge]
</p>

[Lean](https://lean-lang.org) is a language for writing mathematics a computer can check, and [Mathlib](https://github.com/leanprover-community/mathlib4) is its main library. Beyond Mathlib, formal mathematics lives in many separate Lean projects, each tied to its own Lean version, so they cannot be used together and a prover cannot see what already exists. Tengoku translates them onto one **toolchain** (a single Lean version) so that they import together. Mathlib is in, and one research project (Equational Theories) is built in; translating the rest is under way ([where it stands](coverage-draft.md)).

## Try it

```bash
# browse: competemath.com/tengoku (try "sum of two squares")

# search from code
curl 'https://competemath.com/api/tengoku/search?q=Nat.add_comm'

# give an AI agent the search tool (Claude Code; no sign-up)
claude mcp add --transport sse tengoku-search \
  https://barkingtree-leak-i.hf.space/sse

# the trusted records with source, licence and credit (18 MB, one JSON object per line)
curl -LO https://github.com/competemath/tengoku/releases/download/v1.0.0/tengoku-dataset.jsonl.gz

# import it into Lean: about two minutes (needs git, zstd and elan, Lean's version manager)
git clone --filter=blob:none https://github.com/competemath/tengoku
cd tengoku && scripts/cache.sh get
```

In one Lean file, a natural-number structure from Mathlib and a theorem translated from the Equational Theories project:

```lean
import Tengoku.All
open EquationalTheories

instance : Magma ℕ := ⟨fun a b => a + b⟩
example (h : Equation1723 ℕ) : Equation2 ℕ := Equation1723_implies_Equation2 ℕ h
```

## What "trusted" means

Every record (a theorem or definition, with its proof, source, licence and credit) is in one of three tiers:

| Tier | Meaning |
|---|---|
| **tentative** | a real proof from a real source, indexed and searchable; not yet translated or checked here |
| **staging** | translated onto the library's toolchain and accepted by the translation checks; not yet built into the library |
| **trusted** | built into the library, with no `sorry` (Lean's placeholder for an unproved step), only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and hypotheses searched for a contradiction (a search that can miss some) |

A second, independent kernel ([nanoda](https://github.com/ammkrn/nanoda_lib)) re-checks every declaration of the library nightly. The stages are in [TRUST.md](trust-draft.md).

Trusted does **not** mean the Lean statement says what its source says, that a translation is equivalent to its original, or that a person reviewed it. [Benchmarks have the same gap](https://arxiv.org/abs/2606.29493).

## For the authors of the projects Tengoku draws on

The originals stay canonical: to cite a result, cite its project. Each record links to its source at a fixed commit and names the project, its authors and its licence, and a translation is labelled as one. Copyleft sources are not accepted. Corrections and removals: open an issue ([how](CONTRIBUTING.md)). Tengoku's Mathlib content is a copy of Mathlib at a pinned commit, under `Tengoku.*` names; it is independent of Mathlib's maintainers and not endorsed by them. Mathlib's line-by-line review is the standard Tengoku builds on, not one it replaces.

## More

[Where each project stands](coverage-draft.md) · [what has been measured, and what has not](evidence-draft.md) · [how Tengoku relates to Mathlib, Reservoir, LeanDojo and others](comparison-draft.md) · [where it is going](vision-draft.md)

## Contribute · Cite

Anyone can contribute, by hand or with AI: a theorem, a whole project, or a goal ([CONTRIBUTING.md](CONTRIBUTING.md), [GOALS.md](GOALS.md); no Lean needed to suggest one). Credit is permanent. Cite: [DOI 10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400). Apache-2.0, with each record under its upstream licence.

Built by one independent developer, with AI assistance named where it was used, alongside [CompeteMath](https://competemath.com) and the Leak provers. The checks, not the author, decide what is trusted.

## Dedication · Badges
[as in tengoku #246]
