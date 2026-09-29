"""goals_check.py: the shape of GOALS.md, real references, and the AI reviewer writing only Suggestions."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import GOOD, Repo  # noqa: E402

PAGE = "# Goals\n\nIntro.\n\n"


def goal(gid="sum-odd", status="open", statement="theorem sum_odd (n : Nat) : n = n", suggestion="", extra="", why="Because."):
    return f"""<!-- goal: {gid} -->
<details>
<summary><b>A goal</b> · {status}</summary>

<!-- people -->
<details><summary>The statement</summary>

```lean
{statement}
```

</details>
<details><summary>Why it matters</summary>

{why}

</details>
<details><summary>Why it looks doable</summary>

It is small.

</details>
<details><summary>What it builds on</summary>

- `tengoku:Lib.old`
- [a paper](https://example.org/p)

</details>
<details><summary>Built on the work of</summary>

- Ada ([link](https://github.com/ada)) — posed it

</details>
{extra}<!-- /people -->

<details><summary>Suggestions (AI)</summary>

<!-- suggestions -->
{suggestion}
<!-- /suggestions -->

</details>
</details>
<!-- /goal -->
"""


class Goals(unittest.TestCase):
    def repo_with(self, base_page: str | None = None) -> Repo:
        r = Repo()
        if base_page is not None:
            r.git("checkout", "-q", "main")
            r.write("GOALS.md", base_page)
            r.commit("goals")
            r.git("checkout", "-q", "-B", "pr")
        return r

    def run_check(self, r: Repo, ai=False):
        return r.gate("goals_check.py", env={"GOALS_AI": "1"} if ai else None)

    def test_a_well_formed_page_passes(self):
        r = self.repo_with()
        r.write("GOALS.md", PAGE + goal())
        r.commit("add a goal")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("goals OK (1 goals)", out)

    def test_an_unchanged_page_is_not_checked(self):
        rc, out = self.run_check(self.repo_with())
        self.assertEqual(rc, 0, out)
        self.assertIn("unchanged", out)

    def test_missing_field_bad_status_and_duplicate_id_fail(self):
        r = self.repo_with()
        broken = goal().replace("<details><summary>Why it looks doable</summary>", "<details><summary>Whatever</summary>")
        r.write("GOALS.md", PAGE + broken + goal(status="finished"))
        r.commit("bad")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("missing the field `Why it looks doable`", out)
        self.assertIn("unknown field `Whatever`", out)
        self.assertIn("status 'finished'", out)
        self.assertIn("id used twice", out)

    def test_a_reference_to_nothing_fails(self):
        r = self.repo_with()
        r.write("GOALS.md", PAGE + goal(suggestion="- `tengoku:Invented.lemma_that_does_not_exist` helps"))
        r.commit("hallucinated")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("tengoku:Invented.lemma_that_does_not_exist", out)

    def test_a_declaration_in_the_tree_is_a_real_reference(self):
        r = self.repo_with()
        r.write("GOALS.md", PAGE + goal(suggestion="- `tengoku:seeded` is the base case"))
        r.commit("seeded ref")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)

    def test_a_non_http_link_fails(self):
        r = self.repo_with()
        r.write("GOALS.md", PAGE + goal(why="See [this](javascript:alert(1))."))
        r.commit("bad link")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("not http(s)", out)

    def test_a_done_goal_names_what_proved_it(self):
        r = self.repo_with()
        r.write("GOALS.md", PAGE + goal(status="done"))
        r.commit("done without proof")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("Proved by", out)
        r.write("GOALS.md", PAGE + goal(status="done", extra="<details><summary>Proved by</summary>\n\n`tengoku:Lib.old`\n\n</details>\n"))
        r.commit("done with proof")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)

    def test_the_ai_reviewer_may_change_suggestions_only(self):
        r = self.repo_with(PAGE + goal())
        r.write("GOALS.md", PAGE + goal(suggestion="- A subtlety: `tengoku:Lib.old` needs `n > 0`."))
        r.commit("suggest")
        rc, out = self.run_check(r, ai=True)
        self.assertEqual(rc, 0, out)
        r.write("GOALS.md", PAGE + goal(suggestion="- A subtlety.", why="Rewritten by the AI."))
        r.commit("rewrite")
        rc, out = self.run_check(r, ai=True)
        self.assertNotEqual(rc, 0)
        self.assertIn("may change only the text inside Suggestions", out)

    def test_the_ai_reviewer_may_not_touch_other_files(self):
        r = self.repo_with(PAGE + goal())
        r.write("GOALS.md", PAGE + goal(suggestion="- More."))
        r.write("README.md", "# changed\n")
        r.commit("two files")
        rc, out = self.run_check(r, ai=True)
        self.assertNotEqual(rc, 0)
        self.assertIn("may change only GOALS.md", out)

    def test_a_page_level_suggestions_part_after_the_goals(self):
        tail = "<details>\n<summary><b>Goals worth adding</b></summary>\n\n<!-- suggestions -->\n{s}\n<!-- /suggestions -->\n\n</details>\n"
        r = self.repo_with(PAGE + goal() + tail.format(s=""))
        r.write("GOALS.md", PAGE + goal() + tail.format(s="- A goal nobody wrote: the converse, via `tengoku:Lib.old`."))
        r.commit("ai adds a goal idea")
        rc, out = self.run_check(r, ai=True)
        self.assertEqual(rc, 0, out)
        r.write("GOALS.md", PAGE + tail.format(s="") + goal())
        r.commit("before the goals")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("goes after the last goal", out)

    def test_a_qualified_reference_needs_a_real_namespace(self):
        r = self.repo_with()
        # `seeded` exists at the root, but there is no namespace `Other`
        r.write("GOALS.md", PAGE + goal(suggestion="- `tengoku:Other.seeded`"))
        r.commit("wrong namespace")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("tengoku:Other.seeded", out)

    def test_a_namespaced_declaration_is_found_by_its_full_name(self):
        r = self.repo_with()
        r.git("checkout", "-q", "main")
        r.write("Tengoku/Nat/Extra.lean", "namespace Nat\n\ntheorem two_eq : 2 = 2 := rfl\n\nend Nat\n")
        r.commit("seed a namespaced theorem")
        r.git("checkout", "-q", "-B", "pr")
        r.write("GOALS.md", PAGE + goal(suggestion="- `tengoku:Nat.two_eq`"))
        r.commit("ref")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)

    def test_an_additive_name_the_attribute_generates_is_found(self):
        r = self.repo_with()
        r.git("checkout", "-q", "main")
        r.write("Tengoku/Finset/Prod.lean", "namespace Finset\n\n@[to_additive]\ntheorem prod_range_succ : True := trivial\n\nend Finset\n")
        r.commit("seed")
        r.git("checkout", "-q", "-B", "pr")
        r.write("GOALS.md", PAGE + goal(suggestion="- `tengoku:Finset.sum_range_succ`"))
        r.commit("ref")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)

    def test_a_record_added_by_the_same_pr_can_be_referenced(self):
        r = self.repo_with()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.fresh", "statement": "theorem Lib.fresh : 1 + 1 = 2"}) + "\n")
        r.write("GOALS.md", PAGE + goal(suggestion="- `tengoku:Lib.fresh` closes it"))
        r.commit("record and goal")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)

    def test_an_ai_pr_that_leaves_goals_alone_still_may_not_touch_other_files(self):
        r = self.repo_with(PAGE + goal())
        r.write("README.md", "# changed by the AI\n")
        r.commit("only readme")
        rc, out = self.run_check(r, ai=True)
        self.assertNotEqual(rc, 0)
        self.assertIn("may change only GOALS.md", out)

    def test_deleting_the_page_fails(self):
        r = self.repo_with(PAGE + goal())
        (r.dir / "GOALS.md").unlink()
        r.commit("delete")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("GOALS.md is deleted", out)

    def test_an_unclosed_field_fails(self):
        r = self.repo_with()
        broken = goal().replace("It is small.\n\n</details>", "It is small.\n\n", 1)
        r.write("GOALS.md", PAGE + broken)
        r.commit("unclosed")
        rc, out = self.run_check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("not closed", out)

    def test_two_goals_with_one_statement_are_both_reported(self):
        r = self.repo_with()
        rec = {
            **GOOD,
            "name": "Lib.twice",
            "statement": "theorem Lib.twice (n : Nat) : n = n",
            "status": "trusted",
            "promoted_at": "2026-01-01T00:00:00Z",
        }
        r.git("checkout", "-q", "main")
        r.append("data/trusted/lib.jsonl", json.dumps(rec) + "\n")
        r.commit("proved")
        r.git("checkout", "-q", "-B", "pr")
        r.write("GOALS.md", PAGE + goal(gid="one") + goal(gid="two"))
        r.commit("goals")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("goal one looks proved", out)
        self.assertIn("goal two looks proved", out)

    def test_people_may_change_anything(self):
        r = self.repo_with(PAGE + goal(suggestion="- Old suggestion."))
        r.write("GOALS.md", PAGE + goal(suggestion="", why="Clearer now."))
        r.commit("human edit")
        rc, out = self.run_check(r)
        self.assertEqual(rc, 0, out)

    def test_a_goal_a_trusted_record_proves_is_reported(self):
        r = self.repo_with()
        rec = {
            **GOOD,
            "name": "Lib.sumOdd",
            "statement": "theorem Lib.sumOdd (n : Nat) : n = n",
            "status": "trusted",
            "promoted_at": "2026-01-01T00:00:00Z",
        }
        r.git("checkout", "-q", "main")
        r.append("data/trusted/lib.jsonl", json.dumps(rec) + "\n")
        r.commit("proved")
        r.git("checkout", "-q", "-B", "pr")
        r.write("GOALS.md", PAGE + goal())
        r.commit("goal")
        subprocess.run(["git", "checkout", "-q", "main"], cwd=r.dir, check=True)  # the gate runs on main's tree
        rc, out = r.gate("goals_check.py", "main", "pr")
        self.assertEqual(rc, 0, out)
        self.assertIn("looks proved by the trusted record Lib.sumOdd", out)


if __name__ == "__main__":
    unittest.main()
