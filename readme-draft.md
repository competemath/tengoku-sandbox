<p align="center"><img src="logo.png" alt="Tengoku" width="150"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><b>Mathlib and the projects around it, on one Lean version, checked by machine.</b><br>
A library for AI provers and the people who work with them: search it, import it, or give it to an agent.<br>
Every theorem keeps its source, licence and credit.</p>
<p align="center">
[Lean toolchain badge] [trusted theorems badge]
</p>

[Lean](https://lean-lang.org) is a language for writing mathematics that a computer can check, and [Mathlib](https://github.com/leanprover-community/mathlib4) is its main library. Beyond Mathlib, formal mathematics lives in many separate Lean projects, and each works only with its own version of Lean, which changes often. They cannot be used together, and a program that tries to prove theorems cannot even see what already exists. Tengoku translates those projects onto **one toolchain**, so they import together, and trusts a theorem only after it passes checks that anyone can read.

## Try it

```bash
# browse: competemath.com/tengoku (type "sum of two squares")

# search from code
curl 'https://competemath.com/api/tengoku/search?q=Nat.add_comm'

# give an AI agent the search tool (Claude Code; no sign-up)
claude mcp add --transport sse tengoku-search https://barkingtree-leak-i.hf.space/sse

# the 198,172 trusted theorems, with source, licence and credit (18 MB, one file per line)
curl -LO https://github.com/competemath/tengoku/releases/download/v1.0.0/tengoku-dataset.jsonl.gz

# import it into Lean (about two minutes: a download, then Lean)
git clone --filter=blob:none https://github.com/competemath/tengoku && cd tengoku && scripts/cache.sh get
```

One file, two projects that were never built together (Mathlib's `ℕ` and a theorem of the Equational Theories project):

```lean
import Tengoku.All
open EquationalTheories

instance : Magma ℕ := ⟨fun a b => a + b⟩
example (h : Equation1723 ℕ) : Equation2 ℕ := Equation1723_implies_Equation2 ℕ h
```

## What "trusted" means

A theorem is **trusted** when the library builds with it, it uses no `sorry` (Lean's placeholder for an unproved step) and only the three standard axioms, and its hypotheses are checked for contradiction. Every declaration of the library is re-checked nightly by a second, independent type checker ([nanoda](https://github.com/ammkrn/nanoda_lib)). The stages are in [TRUST.md](trust-draft.md).

It does **not** mean the Lean statement says what its source says, that a translation is equivalent to its original, or that a person reviewed it. [Benchmarks have the same gap](https://arxiv.org/abs/2606.29493). Mathlib's line-by-line review is the standard Tengoku builds on, not one it replaces; Tengoku does not fork Mathlib, and what belongs in Mathlib belongs upstream. Originals stay canonical: each theorem links to its source at a fixed commit, with its licence and its authors, copyleft sources are not accepted, and an author can ask for a correction or removal.

## Where it stands

- **Trusted:** Mathlib and its dependencies, CompeteMath's problems and Equational Theories, the one research library promoted so far.
- **Translated, awaiting promotion:** 60 more libraries, including Carleson, the IMO Shortlist and PrimeNumberTheoremAnd.
- **Indexed, not yet translated:** about 100 libraries (searchable, each with a source link).

Counts per library: [COVERAGE.md](coverage-draft.md). What has been measured about the services, and what has not: [EVIDENCE.md](evidence-draft.md). How it relates to Mathlib, Reservoir, LeanDojo and others: [COMPARISON.md](comparison-draft.md). Where it is going: [VISION.md](vision-draft.md).

## Contribute · Cite

Anyone can contribute, by hand or with AI: a theorem, a whole library, or a goal ([CONTRIBUTING.md](CONTRIBUTING.md), [GOALS.md](GOALS.md); no Lean needed to suggest one). Credit is permanent. Cite: [DOI 10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400). Apache-2.0, with each record under its upstream licence.

Built by one independent developer, with AI assistance named where it was used; the checks, not the author, decide what is trusted.

## Dedication · Badges
[as in tengoku #246]
