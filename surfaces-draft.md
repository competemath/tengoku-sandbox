# Proposed wording for every surface (draft)

One idea in the same words everywhere. The README ([readme-draft.md](readme-draft.md)) is the reference; each surface below is it, shortened. Nothing here is applied yet.

**The sentence:** *Formal mathematics from many Lean projects, translated onto one Lean version and checked by machine.*

| Surface | Today | Proposed |
|---|---|---|
| GitHub description, `competemath/tengoku` | "Mathlib plus research libraries in one verified Lean 4 tree, every theorem with its source and credit." | "Many Lean projects translated onto one Lean version, checked by machine, every theorem with its source and credit." |
| GitHub description, `competemath/tengoku-sandbox` | "Sandbox for the Tengoku security rework — not the library, no releases, nothing depends on it" | "A public testing sandbox for Tengoku's checks, not the library: use at your own risk. Official repository: competemath/tengoku." |
| GitHub description, `competemath/emissary-archangel` | "Translates verified Lean theorems into the Tengoku tree: Leak IV compile gate + Archangel kernel-checked entailment gate, banked as staging, trusted once the module builds" | "Translates Lean theorems from other projects onto Tengoku's Lean version (Emissary) and checks each translation twice (Archangel) before it is banked." |
| `emissary-archangel` README, first paragraph | "Translates verified Lean theorems from a source corpus on one Lean toolchain into the Tengoku tree on its toolchain, and vouches for each translation twice before it is banked." | "Lean projects each work with their own Lean version. Emissary-Archangel translates their theorems onto the one version [Tengoku](https://github.com/competemath/tengoku) runs on, and vouches for each translation twice before it is banked." |
| `CITATION.cff` abstract, Zenodo description | "…into one Lean 4 tree on a single pinned toolchain…" | "…into one Lean 4 library on a single pinned toolchain…" (the rest unchanged) |
| competemath.com `/tengoku`, intro | "Tengoku (天国 — "heaven") is an open-source Lean 4 formal knowledge tree, with a few key features: …" | "Tengoku (天国) is an open Lean 4 library of formal mathematics: many projects translated onto one Lean version, every theorem checked by machine, each with its source, licence and credit. Search it below, or give it to an AI agent." Then three points: **One Lean version** (projects translated so they import together); **Checked by machine** (what the labels mean, below); **Open** (anyone can contribute, by hand or with AI). |
| competemath.com `/tengoku`, labels | "Leak-trusted" and "tentative", unexplained | "trusted" and "tentative", with a one-line legend: *trusted: built into the library and checked. tentative: a real proof from its source, not yet checked here.* |
| competemath.com `/tengoku`, page description (metadata) | "…an open-source Lean 4 formal knowledge tree: many libraries unified on one toolchain, open to contributions, growing autonomously with Leak." | "Search an open Lean 4 library of formal mathematics: many projects on one Lean version, every theorem checked by machine, with its source, licence and credit." |
| competemath.com `/about/tengoku`, opening | "one self-contained Lean 4 library… Its purpose is continuously improving, reliable context for automated theorem provers" | the README's opening paragraph, then the existing breakdown |
| competemath.com `/about/tengoku`, metadata | "How Tengoku, CompeteMath's AI-first Lean 4 library, is built, verified, grown and served." | "How Tengoku, an open Lean 4 library of formal mathematics, is built, checked, grown and served." |
| competemath.com `/about`, "Verified by Lean 4" | "…against Tengoku, our own Lean 4 library, seeded from Mathlib and other open libraries." | "…against [Tengoku](/about/tengoku), the open Lean 4 library CompeteMath's developer maintains. It is a separate project that CompeteMath is one user of." |
| competemath.com `/faq` | "…against Tengoku, our own Lean 4 library, guaranteeing the mathematics is airtight." | "…against Tengoku, an open Lean 4 library. The kernel checks the proof; whether the statement says what the problem says is checked separately." |
| competemath.com `/about/leak`, first mention | "Lemma search over Tengoku." | "Lemma search over [Tengoku](/about/tengoku), the open Lean 4 library the services run on." |

Two edits that go beyond wording, because the wording depends on them:

1. The FAQ's "guaranteeing the mathematics is airtight" cannot stand next to a README that says trusted does not mean faithful. The proposed sentence is the honest one.
2. `/tengoku` shows a total of theorems that includes tentative records. A reader will take it as "checked". Show trusted first, or label the total.
