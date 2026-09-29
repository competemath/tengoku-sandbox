# Goals

What Tengoku should have next. A goal can be anything the library's users want in it: a theorem proved, a
library translated, a tool. The first goal is translation: getting the bulk of the registered libraries into
the tree.

Click a goal to open it, and each of its parts to open that. Every goal has two parts. The first is written by
people. Below it, **Suggestions** are written by an AI reviewer that reads the goals and the library and points
out what they miss: a subtlety in a goal, a resource nobody listed, a goal worth adding. The AI may change only
Suggestions; a check on every pull request enforces that. People may edit anything, Suggestions included.

Goals are never deleted: a finished one moves to **Completed**, one given up moves to **Retired** with the reason.
To add or change a goal, see [docs/goals.md](docs/goals.md).

## Open

<!-- goal: translate-the-registered-libraries -->
<details>
<summary><b>Translate the bulk of the registered libraries</b> · partly done</summary>

<!-- people -->
<details><summary>The statement</summary>

Most theorems of the libraries registered in [schemas/sources.json](schemas/sources.json) are in Tengoku:
translated onto the pinned toolchain by Emissary-Archangel and trusted, and the ones that cannot be translated
are recorded with the reason.

</details>
<details><summary>Why it matters</summary>

One tree with every library in it is the point of Tengoku. Until the libraries are in, a prover working in
Tengoku sees little more than Mathlib.

</details>
<details><summary>Why it looks doable</summary>

The translation pipeline already runs unattended on GitHub Actions, banks what it translates as staging pull
requests, and the merge queue promotes them to trusted. What remains is throughput, and the theorems whose
translation needs the agent rather than the mechanical pass.

</details>
<details><summary>What it builds on</summary>

- [schemas/sources.json](schemas/sources.json): the registered libraries, their pinned commits and licences
- [Emissary-Archangel](https://github.com/competemath/emissary-archangel): the translation pipeline and its two checks
- [How a theorem gets into Tengoku](docs/how-a-pr-flows.md): staging, the merge queue and promotion

</details>
<details><summary>Built on the work of</summary>

- The authors of every registered library ([schemas/sources.json](schemas/sources.json)): the theorems themselves
- The Lean community ([Mathlib](https://github.com/leanprover-community/mathlib4)): the base the libraries build on

</details>
<details><summary>Size</summary>

large

</details>
<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
<!-- /suggestions -->

</details>
</details>
<!-- /goal -->

## Completed

None yet.

## Retired

None yet.

<details>
<summary><b>Goals worth adding</b> (suggested by the AI reviewer)</summary>

<!-- suggestions -->
<!-- /suggestions -->

</details>
