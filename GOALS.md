# Goals

What Tengoku should have next. A goal can be anything the library's users want in it: a theorem proved, a
library translated, a tool. The first goal is translation: getting the bulk of the source libraries into
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
<summary><b>Translate the bulk of the source libraries</b> · in progress (early-stage)</summary>

<!-- people -->
<details><summary>The statement</summary>

Most theorems of the source libraries (those registered in [schemas/sources.json](schemas/sources.json)) are in Tengoku:
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

- [schemas/sources.json](schemas/sources.json): the source libraries, their pinned commits and licences
- [Emissary-Archangel](https://github.com/competemath/emissary-archangel): the translation pipeline and its two checks
- [How a theorem gets into Tengoku](docs/how-a-pr-flows.md): staging, the merge queue and promotion

</details>
<details><summary>Built on the work of</summary>

- The authors of every source library ([schemas/sources.json](schemas/sources.json)): the theorems themselves
- The Lean community ([Mathlib](https://github.com/leanprover-community/mathlib4)): the base the libraries build on

</details>
<details><summary>Size</summary>

large

</details>
<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
- **Make "the bulk" a number.** The statement says "most theorems" without saying of what. Each source library already has a status file that counts what each pass did; add up, per library, the records that are trusted, refused with a reason, or still waiting, and let "most" mean a stated share of the waiting-or-trusted records of every library (say 80%), with the rest all explained. Without a number this goal cannot be called done, and "in progress (early-stage)" cannot become anything else.
<!-- /suggestions -->

</details>
</details>
<!-- /goal -->

<!-- goal: simplest-script-for-a-mathlib-version -->
<details>
<summary><b>Extract the simplest viable script for a chosen Mathlib version</b> · open</summary>

<!-- people -->
<details><summary>The statement</summary>

Given a theorem of Tengoku and a target Mathlib (a Mathlib commit with its Lean toolchain), one command returns the
simplest script that compiles on that Mathlib alone, with no Tengoku module imported, and whose nominated theorem
proves the same thing as the Tengoku theorem.

- **Same thing** is not "looks alike": Emissary-Archangel's second gate (the kernel-level entailment check) accepts
  the target-side statement and the Tengoku statement as equivalent, and the first gate (Leak IV, configured for the
  target Mathlib) compiles the whole script with no `sorry` and no new axiom.
- **Simplest** is measured, in this order: the fewest declarations in the script (only the part of the theorem's
  dependency closure that the target Mathlib does not already have), the fewest imports, then the fewest lines. A
  lemma the target Mathlib already has is used, not copied.
- The answer says what it did: which Tengoku declarations were inlined, which were replaced by a target-Mathlib
  lemma (and under what name), which tactics or names had to change, and the Mathlib commit and toolchain it was
  checked against. When no script exists (the theorem needs a definition the target Mathlib cannot express), it
  says why, and nothing unchecked is returned.

</details>
<details><summary>Why it matters</summary>

People accustomed to the more popular Mathlib library can more readily and easily use Tengoku for AI-heavy tasks, this tool thus acting like a seamless bridge. It also means that proofs can be checked on [live-lean](https://live.lean-lang.org/), on the more mature Mathlib.

</details>
<details><summary>Why it looks doable</summary>

Emissary-Archangel already moves verified theorems from other libraries into Tengoku with two gates, and the same two
gates work in the other direction with a different target. The dependency closure of a declaration is already
computed for the exports, Leak IV compiles a script against a pinned environment, and the agent that repairs
translations already handles the renames and tactic changes between versions. What is missing is the reverse
direction as one command, a measure of "simplest", and a way to run Leak IV against a Mathlib that is not the tree's.

</details>
<details><summary>What it builds on</summary>

- [Emissary-Archangel](https://github.com/competemath/emissary-archangel): the two gates, the dependency closures and the translation agent
- [How a theorem gets into Tengoku](docs/how-a-pr-flows.md): what Tengoku keeps for each theorem (statement, proof, tier, source)
- [Mathlib](https://github.com/leanprover-community/mathlib4): the targets, one commit at a time
- [lean4export](https://github.com/leanprover/lean4export): the kernel-level export that the entailment check reads

</details>
<details><summary>Built on the work of</summary>

- The Lean community ([Mathlib](https://github.com/leanprover-community/mathlib4)): the targets, and the deprecation record that says what was renamed
- The authors of lean4export ([leanprover/lean4export](https://github.com/leanprover/lean4export)): the export format the statement-equivalence gate reads

</details>
<details><summary>Size</summary>

large

</details>
<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
- **Start from what live-lean can run.** Find out which Mathlib versions [live-lean](https://live.lean-lang.org/) offers and how much time and memory it gives a run, and make those the first targets and the first meaning of "simple enough". A script that cannot run there does not deliver the second half of the value this goal states.
- **A theorem about a definition only Tengoku has.** The script must carry that definition along, so "the same statement" is then about a copy of the definition, not the original. Say how the entailment gate treats this, and begin with theorems whose statements use only definitions that both Mathlibs have; the other kind is the harder second step.
<!-- /suggestions -->

</details>
</details>
<!-- /goal -->

<!-- goal: deterministic-self-healing-translation -->
<details>
<summary><b>Make translation and intake deterministic, self-healing and easy to run</b> · open</summary>

<!-- people -->
<details><summary>The statement</summary>

Bringing a source library into Tengoku at scale needs no conversation with an AI and no person watching it:

- **One entry point.** Registering a library and starting one workflow is all a person does. The workflow decides
  how to run (one job, or a build first and then the exports split across runners) and carries on until the library
  is translated or every theorem that is not translated has a recorded reason.
- **Deterministic.** The same pinned inputs (library commit, toolchain, tool versions, runner image) give the same
  records. Every tool, toolchain and runner image is pinned, and the pins are written next to the output, so a result
  can be reproduced and a difference explained.
- **The agent is a bounded step, not the driver.** The mechanical pass does everything it can without a model. The
  model is used only for the theorems the mechanical pass cannot do, with a budget per theorem, its answer recorded
  and reused, and its result accepted only after the same two gates as any other record.
- **Self-healing.** Each known failure has a detector and a remedy that run without a person: an out-of-memory kill
  (retry with a smaller batch), a full or capped temporary disk, an expired artifact (rebuild it), a registry drift
  of a runner image, a patch of a tool that no longer fits (recorded as the reason, with the evidence). A failure with
  no remedy ends as a recorded reason and one issue with the log lines that explain it, never as a silent loop.
- **Visible.** One page says, per library, how many theorems are translated, queued, waiting for the agent, or
  refused and why, and how long since anything changed.

Done looks like: seven source libraries registered one after another all finish, or end with every untranslated theorem
explained, with nobody touching them; and running the same library twice gives byte-identical records.

</details>
<details><summary>Why it matters</summary>

Translation is the point of Tengoku, and today it needs babysitting. In October 2026 a library with 30,662 modules
went through three rounds of the sharded setup and exported none, because the build step ignored the build it was
handed and nothing noticed that no round made progress. A library failed on a patch for one version of lean4export.
The merge queue threw out a pull request twice when the default runner image changed and the cache download no
longer fit in the temporary directory. Each of these was found and fixed by a person reading logs. At the scale of
hundreds of source libraries that does not work, and a result that depends on who was awake is not a result a
reader can trust.

</details>
<details><summary>Why it looks doable</summary>

The pieces are there: a mechanical mode that uses no model, a per-library status file and ledger of what each pass
did, a single `setup-auto` entry point that chooses the route by size, rounds that carry on from the last one, and a
build status that tells a complete build from an incomplete one. Most failures seen so far were one of a small set
of causes with a known remedy, which is what makes detectors and remedies worth writing. What remains is turning
those remedies from things a person did into things the pipeline does, pinning what is not pinned, and a check
that fails when a round makes no progress.

</details>
<details><summary>What it builds on</summary>

- [Emissary-Archangel](https://github.com/competemath/emissary-archangel): `setup-auto`, `setup-sharded`, the translation workflows, the per-library status and ledger files
- [schemas/sources.json](schemas/sources.json): the source libraries and the pins that make a run repeatable
- [How a theorem gets into Tengoku](docs/how-a-pr-flows.md): what a translated record has to pass

</details>
<details><summary>Already tried</summary>

An unattended loop that dispatches a mechanical pass for every set-up library, and an agent pass behind a switch,
exists and is switched off by hand. Setting up the largest library failed in three rounds without progress and
without an alarm (the cause was found by reading the logs). Nothing yet detects "this round did nothing".

</details>
<details><summary>Built on the work of</summary>

- The maintainers of [lean4export](https://github.com/leanprover/lean4export): the exports every translation reads
- The Lean community ([Mathlib](https://github.com/leanprover-community/mathlib4)): the build cache the setups start from

</details>
<details><summary>Size</summary>

large

</details>
<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
- **Detect "this round did nothing" from numbers that already exist.** `setup-source.mjs --phase build-status` writes how many modules have an `.olean`. If a build round adds none, stop the run with that evidence instead of starting another round. The three rounds that exported nothing for the largest library would have been one.
- **Pin the runner image and record it.** `ubuntu-latest` moved to Ubuntu 26.04, where `/tmp` is a small tmpfs, and the merge queue broke. Name the image in the workflows and write the image and tool versions into the setup record next to the pins it already holds, so a difference between two runs has an explanation on file.
<!-- /suggestions -->

</details>
</details>
<!-- /goal -->

<!-- goal: prove-the-value-of-tengoku -->
<details>
<summary><b>Prove that Tengoku is worth having</b> · open</summary>

<!-- people -->
<details><summary>The statement</summary>

Show, with evidence a sceptic can check, that a library of many sources proves more than Mathlib alone. Either of
these closes the goal:

1. **An open problem, proved with many sources.** An open problem is proved in Lean, accepted by Leak IV, and the
   proof's dependencies reach into at least seven different source libraries besides Mathlib. The count is read from
   the tree (each dependency's source), not claimed, and the proof says which results from which source it uses.
2. **A controlled comparison.** Two proving setups that differ in exactly one thing: the library behind the search
   and the compiler. One is backed by Mathlib alone, the other by Tengoku. Same prover, same model, same prompts and
   tools, same time and cost budget per problem, same problems, several runs each. The problems are chosen and
   written down before the runs (and include some that earlier Mathlib-only runs did not solve). The report gives
   solved counts for both sides, the difference with its uncertainty, and the problems only one side solved. The runs
   and logs are published.

A result that shows no difference is also a result, and is written up.

</details>
<details><summary>Why it matters</summary>

Everything else on this page assumes that a bigger, many-source library helps provers and mathematicians. Nobody has
shown it. If it does, that is the argument for every library added; if it does not, we should know which kind of
library does not help and stop adding it.

</details>
<details><summary>Why it looks doable</summary>

The proving harness (Leak I for search, Leak IV for the compiler) already takes the library as a setting, so a
Mathlib-only backing is a tree with only Mathlib in it. Recorded benchmark runs already exist, including problems
no run solved, so there are baselines and hard problems to start from. For the open problem, the tree can already
answer which sources a proof depends on, and problems that sit between fields (algebraic geometry, number fields,
commutative algebra) are where many sources should matter.

</details>
<details><summary>What it builds on</summary>

- [competemath/LRR](https://github.com/competemath/LRR): recorded proving runs and their results, the baselines for a comparison
- [Emissary-Archangel](https://github.com/competemath/emissary-archangel): how the sources get into the tree
- [schemas/sources.json](schemas/sources.json): the source libraries a proof can draw on
- [Mathlib](https://github.com/leanprover-community/mathlib4): the control

</details>
<details><summary>Already tried</summary>

Individual recorded runs of provers with and without extra tools exist, and several benchmark problems were not
solved by any run. No comparison has been run in which the library is the only difference.

</details>
<details><summary>Built on the work of</summary>

- The Lean community ([Mathlib](https://github.com/leanprover-community/mathlib4)): the control library and most of the sources' foundation
- The authors of every source library ([schemas/sources.json](schemas/sources.json)): the libraries a proof would draw on

</details>
<details><summary>Size</summary>

large

</details>
<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
- **Take the open problem from a list somebody else keeps.** [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) is a registered source library and states open problems in Lean. Choosing from it, and writing the choice down before any run, stops the target from moving to fit the result.
- **Keep the answer out of both sides.** Some source libraries (for example [compfiles](https://github.com/dwrensha/compfiles)) contain solved versions of competition-style problems. For the comparison, remove from both trees whatever contains the benchmark's own solutions; otherwise the Tengoku side is partly answering from memory and the difference means less than it seems to.
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
### Make the harvester emit only records the gate accepts

The statement: `tools/harvest.py` produces only records that pass `validate_records.py` and `lint_banked.py`, or reports in its output exactly which it left out and why, so nobody finds out in CI.

Why: harvesting eight source libraries gave 45,935 records and the gate refused 89 of them: three "declarations" that were words read out of comments (`supplies`, `in`, `it`), one name that is already trusted, 84 repeated names (private lemmas of different sections) and one `set_option` that is not on the allowlist. Each round of that was found by reading a failed check, and the validator lists only the first 25 problems per run, so the first round looked smaller than it was. Running the same two checks inside the harvester is a small change with a clear test: harvest, then run the gate's scripts on the result, and expect no refusals.
<!-- /suggestions -->

</details>
