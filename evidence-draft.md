# Evidence (draft)

What has been measured about the services Tengoku runs on, what that does and does not show, and what is planned.

## The measurement

[FATE-X](https://github.com/frenzymath/FATE-X/releases/tag/v4.28.0) is a benchmark of 100 graduate-level problems in abstract and commutative algebra, in Lean 4. 98 problems were scorable. The same model (Claude Sonnet 5), the same 60-minute budget per problem, no web search:

| Arm | Given | Proved |
|---|---|---|
| **Control II** | the Leak IV compiler gate and the Leak I library search | **38 of 98** (38.8%) |
| **Ultra Fleeting** | decomposition into lemmas, and more tools | 28 of 98 (28.6%) |
| **Control III** | no tools: told only whether each whole attempt compiled | **1 of 42** (stopped after 42 problems) |

Date of the runs: summer 2026. Toolchain: Lean v4.29.1 with Mathlib, before Tengoku existed. [Full report: link when public.]

## What it shows, and what it does not

- It shows that, for this model and benchmark, the tool-equipped flat agent beat both the no-tool agent and the decomposition pipeline. The report's headline is the second part: the project's own more elaborate design lost.
- It does **not** show that Tengoku, the larger library, improves provers: the library did not exist yet. The search ran over Mathlib.
- The Control III row is not a matched comparison: it was stopped at 42 problems, so it counts a different number of problems from the other rows. The report itself uses it only to say that the base agent without tools makes almost no headway.
- It does not isolate Leak II (the proof-state service). A run designed to (Control IV) was not completed.

## What is planned

The same benchmark, with the same model, problems and budget, after Tengoku has grown: the services now run over Tengoku (a script importing `Tengoku.All` and using a theorem from a research library compiles on the live verifier today). The result, whichever way it goes, will be published here. For it to be a fair before and after, the benchmark's statements must compile on Tengoku's newer toolchain, and the arms must be matched in the number of problems.
