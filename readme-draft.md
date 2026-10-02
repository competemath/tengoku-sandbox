<p align="center"><img src="logo.png" alt="Tengoku" width="150"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><b>Formal mathematics from many projects, unified on one Lean toolchain and checked by machine.</b><br>
Built so AI provers, and the people who work with them, can find and trust what has already been proved.</p>
<p align="center">
[Lean toolchain badge] [trusted theorems badge]
</p>

## Try it

| | |
|---|---|
| **Search** | [competemath.com/tengoku](https://competemath.com/tengoku): try `sum of two squares`, or a Lean type |
| **Give it to an agent** | `claude mcp add --transport sse leak-i https://barkingtree-leak-i.hf.space/sse` (no sign-up) |
| **From code** | `curl 'https://competemath.com/api/tengoku/search?q=Nat.add_comm'` |
| **Import it** | `git clone https://github.com/competemath/tengoku && cd tengoku && scripts/cache.sh get`, then `import Tengoku.All` |

## Why

Formal mathematics now spans hundreds of Lean projects, but each one pins its own version of Lean, so they cannot be used together. An AI prover cannot see what exists beyond Mathlib, and even the benchmarks are not always sound: an [audit of five widely used Lean benchmarks](https://arxiv.org/abs/2606.29493) found vacuous theorems, counterexamples and unsound axioms among 4,833 findings.

Tengoku's answer is one library: libraries are **translated onto a single toolchain**, every theorem is **checked by machine**, and every theorem keeps its **source, licence and credit**.

## What "trusted" means

A theorem is **trusted** when the library builds with it, it uses no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and its assumptions are checked not to contradict each other (so it is not vacuous). A second kernel re-checks every declaration nightly.

```mermaid
flowchart LR
  A["theorem<br/>+ credit line"] --> B["gate<br/>shape, credit, safe Lean"] --> C["queue<br/>built with the library"] --> D["tentative / staging"] --> E["promotion<br/>fresh build, axioms,<br/>vacuity"] --> F(["trusted"])
```

Not claimed: that a statement says what its informal source says (faithfulness), or that a human reviewed it. Mathlib's line-by-line review is the standard Tengoku builds on, not one it replaces.

## Evidence

The services above help an agent prove. On [FATE-X](https://github.com/frenzymath/FATE-X) (graduate algebra), the same model and budget proved **38 of 98** problems with Tengoku's compiler gate and library search, and **1 of 42** with no tools (that run was stopped early). Measured before Tengoku's growth; measured again after it. [Report: TODO link]

## Where it fits

| | |
|---|---|
| **Mathlib** | the base. Curated and human-reviewed; Tengoku adds what it does not hold, checked by machine. |
| **Research projects** (Carleson, PFR, FLT, …) | translated onto one toolchain, each theorem linked to its original. |
| **Lake / Reservoir** | finds and versions packages; does not unify their Lean versions. |
| **Datasets** (LeanDojo, Lean Workbook, …) | fixed releases; Tengoku is a living library with provenance. |
| **Search** (Loogle, Moogle, LeanSearch) | Tengoku's search builds on Loogle and Moogle, over the whole library, with trust shown. |
| **Formal Conjectures** | one of Tengoku's sources. |

## Status

| | |
|---|---|
| **Today** | Mathlib and its dependencies; translated research libraries; search, verifier and proof-state services; nightly builds and independent check; monthly dataset releases with a DOI |
| **Next** | translating the remaining registered libraries; a second measurement after growth |
| **Later** | following every new Lean release; fresh, uncontaminated problems; a public record of what the library does for provers |

More in [VISION.md](vision-draft.md).

## Contribute · Cite

Anyone can contribute, by hand or with AI: a theorem, a whole library, or a goal ([CONTRIBUTING.md](CONTRIBUTING.md), [GOALS.md](GOALS.md)). Credit is permanent. Cite: [DOI 10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400).

## Dedication · Badges
[as in tengoku #246]
