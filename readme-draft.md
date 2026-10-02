<p align="center"><img src="logo.png" alt="Tengoku" width="150"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><b>Formal mathematics from many Lean projects, translated onto one Lean version and machine-checked.</b><br>
Today: Mathlib and one research project, with more on the way. Search it, import it, or hand it to an agent.<br>
Every theorem keeps its source and licence, and its authors' credit.</p>
<p align="center">
[Lean toolchain badge] [trusted theorems badge]
</p>

[Lean](https://lean-lang.org) writes mathematics a computer can check; [Mathlib](https://github.com/leanprover-community/mathlib4) is its main library. Other formal mathematics lives in separate Lean projects, each pinned to its own Lean version, so they cannot be combined and a prover cannot see what exists. Tengoku translates them onto one **toolchain** (a single Lean version) so they import together, and a second, independent kernel ([nanoda](https://github.com/ammkrn/nanoda_lib)) re-checks the whole library every night. Mathlib and one research project (Equational Theories) are in; the rest is under way ([status](coverage-draft.md)).

## Try it

Start with the first line, a web page. The rest is for programmers.

```bash
# browse: competemath.com/tengoku (try "continuous image of compact")

# search from code
curl 'https://competemath.com/api/tengoku/search?q=IsCompact.image'
# -> trusted · mathlib · IsCompact.image
#    IsCompact s → Continuous f → IsCompact (f '' s)   (statement only; the proof is in the source file)

# give an AI agent the search tool (Claude Code; no sign-up)
claude mcp add --transport sse tengoku-search \
  https://barkingtree-leak-i.hf.space/sse

# the trusted theorems: statements, sources, licences (18 MB; see the data card)
curl -LO https://github.com/competemath/tengoku/releases/download/v1.0.0/tengoku-dataset.jsonl.gz

# import it into Lean: a few minutes, mostly one download (needs git, zstd and elan, Lean's version manager)
git clone --filter=blob:none https://github.com/competemath/tengoku
cd tengoku && scripts/cache.sh get
```

One Lean file, using a natural-number structure from Mathlib and a theorem translated from the Equational Theories project:

```lean
import Tengoku.All
open EquationalTheories

instance : Magma ℕ := ⟨fun a b => a + b⟩
example (h : Equation1723 ℕ) : Equation2 ℕ := Equation1723_implies_Equation2 ℕ h
```

## What "trusted" means

| Tier | Meaning |
|---|---|
| **tentative** | a real proof from a real source, searchable; not yet translated or checked here |
| **staging** | translated and accepted by the translation checks; not yet built into the library |
| **trusted** | built into the library; no `sorry` (Lean's placeholder for an unproved step); only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); hypotheses searched for a contradiction (a search that can miss some) |

Trusted does **not** mean the Lean statement says what its source says, that a translation equals its original, or that a person reviewed it. [Benchmarks share this gap](https://arxiv.org/abs/2606.29493). The stages are in [TRUST.md](trust-draft.md).

**Known gaps** (2026-10-02): the nightly check matches 136,444 of the 161,646 distinct trusted names to declarations in the library, all resting only on the standard axioms; the rest are Mathlib search-index entries it does not match by name. 262 CompeteMath problems carry the trusted label but were verified separately and are not built into the library ([details](trust-draft.md#known-gaps)).

## For the authors of the projects Tengoku draws on

The originals stay canonical: cite the project, not Tengoku. Each record links to its source at a fixed commit and names the project and its licence; seeded files keep their authors' headers, and a contributed theorem carries a permanent `Author:` line. Translations are labelled, and copyleft sources are refused. For corrections or removal, open an issue ([how](CONTRIBUTING.md)). The Mathlib content is a pinned copy under `Tengoku.*` names, independent of Mathlib's maintainers and not endorsed by them; their line-by-line review is a standard Tengoku does not claim to meet.

## More

[Data card](data-draft.md) · [coverage](coverage-draft.md) · [evidence](evidence-draft.md) · [comparison](comparison-draft.md) · [vision](vision-draft.md)

## Contribute · Cite

Anyone can contribute, by hand or with AI: a theorem, a project, or a goal ([CONTRIBUTING.md](CONTRIBUTING.md), [GOALS.md](GOALS.md)). Cite [DOI 10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400). Apache-2.0; each record keeps its upstream licence.

One independent developer, AI assistance named where used, alongside [CompeteMath](https://competemath.com) and the Leak provers. The checks, not the author, decide what is trusted.

## Dedication · Badges
[as in tengoku #246]
