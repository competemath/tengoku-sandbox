# Where Tengoku fits (draft)

What already exists, and how Tengoku relates to it. Figures are the neighbours' own, at the time of writing, with their source. Most of these are what Tengoku stands on.

| Project | What it is | How Tengoku relates |
|---|---|---|
| **[Mathlib](https://github.com/leanprover-community/mathlib4)** | The curated Lean 4 mathematics library, reviewed line by line by its community and shaped for people writing proofs: names and interfaces are refactored as better statements are found. | The base. Tengoku carries a pinned copy of it in `Tengoku.*` modules, keeping Mathlib's declaration names. Where Mathlib's interfaces move, provers break; Tengoku keeps what was proved, and a retracted theorem leaves a note saying how to prove the same idea (the equivalent theorem, or the steps to take). What belongs in Mathlib belongs upstream; Tengoku adds the projects around it, checked by machine instead of by review. |
| **Individual research projects** (Carleson, PFR, FLT, Equational Theories, …) | Each a Lean project pinned to its own Lean and Mathlib version, maintained by its authors. | Registered as sources. Tengoku translates their theorems to its toolchain and links every theorem to the original at a fixed commit and licence. The originals stay canonical and keep evolving; the translations are copies that carry their provenance. |
| **[Reservoir](https://reservoir.lean-lang.org)** | The official registry that indexes Lean packages and their versions. | Finds and versions packages; it does not make them importable together. Tengoku works on the part Reservoir leaves to each project: one toolchain for all. |
| **[LeanDojo](https://arxiv.org/abs/2306.15626)** | A toolkit and benchmark that traces Lean projects (102,514 theorems in LeanDojo Benchmark 4) for retrieval-augmented provers. | LeanDojo extracts a dataset from Mathlib at one point in time. Tengoku is a library that keeps growing, with a tier and a source on every theorem. |
| **[Lean Workbook](https://arxiv.org/abs/2406.03847), [DeepSeek-Prover data](https://arxiv.org/abs/2405.14333)** | Large sets of problems autoformalised from natural language (57,000 problems, 5,000 with proofs; 8 million synthetic statements). | Different material: formalised problem statements, mostly synthetic. Tengoku holds theorems with real proofs from real sources. The two meet where a benchmark's statements are checked against the library. |
| **[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)** (Google DeepMind) | Statements of open conjectures formalised in Lean (2,615 statements, 1,029 open conjectures at last count). | One of Tengoku's registered sources. |
| **[Loogle](https://loogle.lean-lang.org), [Moogle](https://arxiv.org/abs/2403.13310), [LeanSearch](https://arxiv.org/abs/2605.13137), [LeanExplore](https://arxiv.org/abs/2506.11085)** | Search engines over Mathlib: by type pattern (Loogle) or by meaning. | Tengoku's search service is built on Loogle and Moogle and runs over the whole library, with the tier of every result. |
| **[Pantograph](https://arxiv.org/abs/2410.16429), [Kimina Lean Server](https://neurips.cc/virtual/2025/131063), the Lean REPL, [AXLE](https://arxiv.org/abs/2606.26442)** | Ways to run Lean programmatically: proof states for tree search (Pantograph), large-scale batch verification (Kimina, AXLE). | The same kind of service. Tengoku's proof-state service (Leak II) builds on Pantograph, and its verifier (Leak IV) compiles scripts like these servers do; what differs is that they run against Tengoku, so a script can use every project in it. |
| **[Archive of Formal Proofs](https://www.isa-afp.org)** (Isabelle, 993 entries at last count) | The curated archive of Isabelle proof developments. | A different proof assistant; the closest model of a community archive. Tengoku is Lean only, for now. |

## What is unusual about Tengoku

Not any one piece, which exist elsewhere, but the combination, all in the open: translation of whole libraries onto one toolchain; a machine-checked definition of trust that includes a check for vacuous theorems; provenance, licence and credit on every record; services an agent can call while it proves; and a measurement of what those services do for provers, to be repeated as the library grows.

## What Tengoku does not claim

- To be a better library than Mathlib. It is a different thing.
- That translation is lossless. It is checked, not guaranteed equivalent ([how](trust-draft.md)).
- That a larger library makes provers better. That is a hypothesis being measured ([evidence](evidence-draft.md)).
