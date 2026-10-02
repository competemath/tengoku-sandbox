# Tengoku: the wording every page should share (draft)

One source for what Tengoku is, why it exists and what it is not, so the README, the site, the repositories and the citation say the same thing. Anything that describes Tengoku should be this, shortened, never reworded.

## The three questions

| | Canonical answer |
|---|---|
| **What is it?** | One verified Lean 4 library of formal mathematics, assembled from many projects on a single toolchain, with every theorem's source, licence and credit attached. |
| **Why does it exist?** | Formal mathematics is fragmented: hundreds of projects, each on its own Lean version, so nobody (and no AI prover) can use them together or even find what exists. |
| **What is it for?** | Giving automated theorem provers, and the people working with them, continuously improving, reliable context: one library to search, one toolchain, one definition of "trusted". |

## The pitch at three lengths

- **Repository description (under 120 characters):** One verified Lean 4 library of formal mathematics, with every theorem's source and credit, for AI provers and people.
- **Tagline:** Formal mathematics from many projects, in one verified Lean 4 library.
- **Paragraph:** Tengoku (天国, "heaven") gathers theorems from many formal mathematics projects into one Lean 4 library on a single pinned toolchain. A theorem is *trusted* only once the library builds with it, it uses no `sorry` and only the standard axioms, and its assumptions are checked not to contradict. Every record links to its source at a fixed commit and carries its licence and credit. It is built so that AI provers, and the people who work with them, can search everything already proven and rely on it.

## Words

| Say | Not | Why |
|---|---|---|
| **library** | "tree", "knowledge tree", "dataset" in prose | One noun for the thing you import. "Tree" is fine for the directory in technical docs. |
| **dataset** | | Only for the monthly snapshot release (the file with its DOI). |
| **trusted** / **tentative** / **staging** | "verified" alone | "Verified" is the library's job description; a record has a tier. Tentative: a real proof at its source, not yet checked here. Staging: translated, awaiting promotion. Trusted: built into the library and checked. |
| **registered sources** | "libraries" for both the sources and the library | Tengoku is *the* library; what it draws from are *sources*. |
| **Leak** | | The verification and search services (Leak I search over MCP, Leak IV verifier). One sentence on first use. |
| **Emissary-Archangel** | | The pipeline that translates sources onto Tengoku's toolchain. A separate repository. |

## Facts that must come from one place

| Fact | Single source |
|---|---|
| number of trusted / tentative / staging theorems | the badge and `data/stats.json`, never typed into prose |
| number of registered sources | one definition: entries of `schemas/sources.json`, published in `stats.json` |
| the pinned toolchain | `lean-toolchain` |
| search endpoints | `docs/api.md` |

## Claims with numbers

A benchmark figure is quoted with what it measured: the model, the benchmark, the denominator of each arm, the toolchain, the date, and a link to the report. Two arms with different denominators say so in the same sentence. A service's benefit is claimed only where a completed run isolates it (the measured case covers the compiler gate and the library search, not the proof-state service).

## What Tengoku is not

- Not a replacement for Mathlib: it builds on Mathlib and adds what Mathlib does not hold, checked by machine instead of by line-by-line review.
- Not a proof assistant: it is a library for one.
- Not CompeteMath: CompeteMath is the competition site, one user of Tengoku (it checks its problems and answers against the library). Tengoku does not need CompeteMath to be used.

## Where each surface says it

| Surface | Uses |
|---|---|
| `competemath/tengoku` GitHub description and README | description, tagline, then the problem table |
| `competemath/tengoku-sandbox` description | "A public testing sandbox for Tengoku's checks, not the library. Use at your own risk. Official repository: competemath/tengoku." |
| `competemath/emissary-archangel` README first line | "Translates verified Lean theorems onto the Tengoku library's toolchain (Emissary) and checks each translation twice (Archangel)." |
| competemath.com `/tengoku` (search page) | tagline, the three-point list from this page, the live numbers |
| competemath.com `/about/tengoku` | the paragraph, then the full breakdown |
| competemath.com `/about`, `/faq` | one sentence: Tengoku is the open Lean 4 library CompeteMath checks its problems against; link to `/about/tengoku` |
| `CITATION.cff`, `zenodo.json` | the paragraph, as a dataset description |
