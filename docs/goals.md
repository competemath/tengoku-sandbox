# Writing goals

[GOALS.md](../GOALS.md) lists results people would like Tengoku to reach. Each goal opens into the same
fields, so a reader always knows where to look.

## The fields

| Field | What goes in it |
|---|---|
| **The statement** | The exact Lean statement, in a ```` ```lean ```` block, if it can be written down; otherwise one sentence saying what is missing before it can be. With a Lean statement, the check notices when a trusted theorem proves exactly it. |
| **Why it matters** | What it unlocks or settles, and for whom. |
| **Why it looks doable** | Why now: the pieces that exist, a known proof on paper, a recent result. |
| **What it builds on** | Theorems already in Tengoku (written `tengoku:Name`) and outside sources (links). |
| **Built on the work of** | The people whose results this goal rests on or who posed it, one line each: who, a link, what they did. Whoever closes the goal is credited by the `Author:` line on their proof; this field is for everyone else. |
| **Already tried** *(optional)* | Past attempts and where they got stuck, so nobody repeats a dead end. |
| **Size** *(optional)* | small, medium or large: a rough effort. |
| **Proved by** *(required once done)* | The theorem that closes it: `tengoku:Name`. |

The status in the title line is one of `open`, `partly done` or `done`.

## A new goal

Copy this to the end of GOALS.md and fill it in. Keep the marker comments exactly as they are: the check
reads them. The id is lowercase letters, digits and dashes, and never changes once the goal is in.

````markdown
<!-- goal: your-goal-id -->
<details>
<summary><b>The goal in a few words</b> · open</summary>

<!-- people -->
<details><summary>The statement</summary>

```lean
theorem name (binders) : claim
```

</details>
<details><summary>Why it matters</summary>

…

</details>
<details><summary>Why it looks doable</summary>

…

</details>
<details><summary>What it builds on</summary>

- `tengoku:Some.Theorem` — why it helps
- [An outside source](https://example.org) — why it helps

</details>
<details><summary>Built on the work of</summary>

- Name ([link](https://example.org)) — what they did

</details>
<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
<!-- /suggestions -->

</details>
</details>
<!-- /goal -->
````

## What the check enforces

`scripts/ci/goals_check.py` runs on every pull request that changes GOALS.md:

- every goal has a unique id, a title, a status, the fields above and no others, and one Suggestions part
  after the part people write;
- every `tengoku:Name` names a record or declaration that exists (the AI reviewer's references included), and
  every link is `http(s)`;
- a pull request from the AI reviewer (its branch starts with `goals-suggest/`) changes nothing but the text
  inside Suggestions, and no other file.

When a trusted theorem proves a goal's statement exactly, the check says so on the pull request; a person then
marks the goal done.
