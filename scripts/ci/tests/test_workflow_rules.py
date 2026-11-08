"""workflow_rules.py: every rule has cases that must fail and cases that must pass.

Each failing case is the clean workflow below with one change, and asserts which rule fired; the clean
workflow itself must produce no finding, so a failing case cannot pass for an unrelated reason.
"""

from __future__ import annotations

import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

CI = Path(__file__).resolve().parents[1]
TREE = CI.parents[1]
sys.path.insert(0, str(CI))
import workflow_rules as wr  # noqa: E402

CO = "actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4"
CLEAN = f"""name: t
on:
  pull_request:
    types: [opened]
permissions: {{}}
env:
  BASE: ${{{{ github.event.pull_request.base.sha || github.event.merge_group.base_sha }}}}
  HEAD: ${{{{ github.event.pull_request.head.sha || github.event.merge_group.head_sha }}}}
jobs:
  a:
    runs-on: ubuntu-latest
    permissions: {{ contents: read }}
    steps:
      - uses: {CO}
        with: {{ ref: "${{{{ env.BASE }}}}", persist-credentials: false }}
      - name: work
        env: {{ TITLE: "${{{{ github.event.pull_request.title }}}}" }}
        run: |
          printf '%s' "$TITLE" > t.txt
          echo "${{{{ github.event.pull_request.number }}}} ${{{{ github.sha }}}}"
          python3 x.py ${{{{ github.event_name == 'merge_group' && '--queue' || '' }}}}
"""


def rules(text: str, path: str = ".github/workflows/t.yml") -> list[str]:
    return [f[2] for f in wr.Checker(path, text).run().findings]


def swap(old: str, new: str, text: str = CLEAN) -> str:
    assert text.count(old) == 1, old
    return text.replace(old, new)


TARGET = swap("  pull_request:\n", "  pull_request_target:\n")


class Clean(unittest.TestCase):
    def test_clean_workflow_passes(self):
        self.assertEqual(rules(CLEAN), [])
        self.assertEqual(rules(TARGET), [])

    def test_repository_workflows_pass(self):
        for p in sorted((TREE / ".github/workflows").glob("*.yml")):
            with self.subTest(p.name):
                self.assertEqual(wr.Checker(str(p), p.read_text()).run().findings, [])


CANCELLING = swap("permissions: {}\n", "permissions: {}\nconcurrency:\n  group: g\n  cancel-in-progress: true\n")


class Cancelable(unittest.TestCase):
    """Found 2026-10-05: CodeRabbit rewrites a PR's description after its review, an `edited` event, which cancelled the running pr-gate; the cancelled run's `pr-gate` job (`if: always()`)
    still ran, failed, and stayed on the commit as the latest `pr-gate` after the newer run had passed, so every PR was blocked until someone re-ran the right run."""

    def test_always_in_a_cancelling_workflow_fails(self):
        self.assertIn(
            "cancelable", rules(swap("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    if: always()\n", CANCELLING))
        )
        self.assertIn(
            "cancelable",
            rules(
                swap(
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    if: ${{ always() && github.event_name == 'pull_request' }}\n",
                    CANCELLING,
                )
            ),
        )
        self.assertIn(
            "cancelable",
            rules(
                swap(
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    if: always() && needs.x.result != 'skipped'\n",
                    CANCELLING,
                )
            ),
        )

    def test_an_expression_for_cancel_in_progress_counts_as_cancelling(self):
        text = swap("cancel-in-progress: true", "cancel-in-progress: ${{ github.event_name == 'pull_request' }}", CANCELLING)
        self.assertIn("cancelable", rules(swap("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    if: always()\n", text)))

    def test_a_job_level_concurrency_counts_too(self):
        text = swap(
            "    runs-on: ubuntu-latest\n",
            "    runs-on: ubuntu-latest\n    if: always()\n    concurrency: { group: g, cancel-in-progress: true }\n",
        )
        self.assertIn("cancelable", rules(text))

    def test_not_cancelled_passes(self):
        self.assertEqual(
            rules(swap("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    if: ${{ !cancelled() }}\n", CANCELLING)), []
        )
        self.assertEqual(
            rules(
                swap(
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    if: ${{ !cancelled() && github.event_name == 'pull_request' }}\n",
                    CANCELLING,
                )
            ),
            [],
        )

    def job_if(self, cond):
        wrapped = cond if cond.startswith("${{") else "${{ " + cond + " }}"  # a bare `!` at the start of a YAML scalar is a tag
        return rules(swap("    runs-on: ubuntu-latest\n", f"    runs-on: ubuntu-latest\n    if: {wrapped}\n", CANCELLING))

    def test_always_with_a_guard_that_holds_on_every_cancelled_run_passes(self):
        for cond in [
            "${{ always() && !cancelled() }}",
            "${{ !cancelled() && always() }}",
            "always() && ! cancelled ( ) && needs.x.result != 'skipped'",
            "always() && !(!(!cancelled()))",
            "!(cancelled() || github.event_name == 'x') && always()",
            "always() && !cancelled() || false",
            "!cancelled() && (always() || github.event_name == 'x')",
            "github.event_name == 'x' && !cancelled() && always()",  # an unknown left operand: the right one must be read once
            "(github.event_name == 'x' || false) && !cancelled() && always()",  # the same inside parentheses, with `||`
            "always() && !cancelled() && contains((github.event.x), 'a')",  # a call argument with parentheses of its own
            "always() && !cancelled() && github.event[format('{0}', github.x)]",  # an index that is an expression
            "always() && !cancelled() && github.event.pull_request.labels.*.name && github.event['ref'] == 'x'",
        ]:
            self.assertEqual(self.job_if(cond), [], cond)

    def test_a_condition_that_can_be_true_on_a_cancelled_run_is_reported(self):
        for cond in [
            "${{ always() || !cancelled() }}",
            "${{ always() && !cancelled() || github.event_name == 'pull_request' }}",
            "${{ always() && foo || !cancelled() }}",
            "always() && !(!cancelled())",  # CodeRabbit: a second negation brings the cancellation back
            "always() && (!cancelled() || github.event_name == 'x')",
            "always() && !contains(github.event.label.name, 'a||b')",
            "failure() || always()",
            "github.event_name == 'x' || !cancelled() && always() && false",  # the left of `||` alone can make it true, whatever the right says
            "always() && !cancelled() == false",  # `!cancelled() == false` is true after a cancellation
            "always() && contains(github.event.label.name, 'x')",
            "always() && github.event.pull_request.labels.*.name",
        ]:
            self.assertIn("cancelable", self.job_if(cond), cond)

    def test_status_functions_on_a_cancelled_run(self):
        self.assertFalse(wr.runs_when_cancelled("success()"))
        self.assertFalse(wr.runs_when_cancelled("failure()"))
        self.assertTrue(wr.runs_when_cancelled("cancelled()"))
        self.assertTrue(wr.runs_when_cancelled("always()"))
        self.assertFalse(wr.runs_when_cancelled("always() && failure()"))

    def test_text_that_cannot_be_parsed_counts_as_able_to_run(self):
        for cond in [
            "always() &&",
            "always() && (!cancelled()",
            "always() $ !cancelled()",
            "always() !cancelled()",
            "!cancelled() always()",
        ]:
            self.assertTrue(wr.runs_when_cancelled(cond), cond)
            self.assertIn("cancelable", self.job_if(cond), cond)

    def test_always_in_a_workflow_that_nobody_cancels_passes(self):
        self.assertEqual(rules(swap("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    if: always()\n")), [])
        no_cancel = swap("permissions: {}\n", "permissions: {}\nconcurrency:\n  group: g\n  cancel-in-progress: false\n")
        self.assertEqual(rules(swap("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    if: always()\n", no_cancel)), [])

    def test_a_step_that_always_runs_is_not_the_rule(self):
        # a step of a cancelled run does not outlive it as a check; the rule is about jobs
        self.assertEqual(rules(swap("      - name: work\n", "      - name: work\n        if: always()\n", CANCELLING)), [])


class Pinned(unittest.TestCase):
    def test_tag_branch_and_missing_comment_fail(self):
        for uses in [
            "actions/checkout@v4",
            "actions/checkout@main",
            '"actions/checkout@v4"',
            "actions/checkout@11d5960a326750d5838078e36cf38b85af677262",
        ]:
            with self.subTest(uses):
                self.assertEqual(rules(swap(CO, uses)), ["pinned"])

    def test_short_or_uppercase_sha_fails(self):
        self.assertEqual(rules(swap(CO, "actions/checkout@11d5960 # v4")), ["pinned"])
        self.assertEqual(rules(swap(CO, "actions/checkout@11D5960A326750D5838078E36CF38B85AF677262 # v4")), ["pinned"])

    def test_local_and_digest_pass_image_tag_fails(self):
        step = "      - uses: {}\n"
        base = CLEAN + step.format("./.github/actions/x")
        self.assertEqual(rules(base), [])
        self.assertEqual(rules(CLEAN + step.format("docker://alpine@sha256:" + "a" * 64)), [])
        self.assertEqual(rules(CLEAN + step.format("docker://alpine:3.20")), ["pinned"])

    def test_self_repository_reference(self):
        step = "      - uses: {}\n"
        self.assertEqual(rules(CLEAN + step.format("$/.github/actions/build")), [])
        self.assertEqual(rules(CLEAN + step.format("$/")), ["pinned"])
        self.assertEqual(rules(CLEAN + step.format("$/.github/actions/build@main")), ["pinned"])

    def test_reusable_workflow_job(self):
        job = "  b:\n    uses: org/repo/.github/workflows/w.yml@{}\n"
        self.assertEqual(rules(CLEAN + job.format("main")), ["pinned"])
        self.assertEqual(rules(CLEAN + job.format("a" * 40 + " # v1")), [])

    def test_composite_action(self):
        action = "name: x\nruns:\n  using: composite\n  steps:\n    - uses: actions/setup-python@v5\n"
        self.assertEqual(rules(action, ".github/actions/x/action.yml"), ["pinned"])


class Token(unittest.TestCase):
    def test_missing_or_true_fails(self):
        self.assertEqual(rules(swap(", persist-credentials: false }", " }")), ["token"])
        self.assertEqual(rules(swap("persist-credentials: false", "persist-credentials: true")), ["token"])

    def test_string_false_and_anchor_pass(self):
        self.assertEqual(rules(swap("persist-credentials: false", 'persist-credentials: "false"')), [])
        anchored = swap(
            f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.BASE }}}}", persist-credentials: false }}\n',
            f"      - uses: {CO}\n        with: &co {{ persist-credentials: false }}\n      - uses: {CO}\n        with: {{ <<: *co, fetch-depth: 0 }}\n",
        )
        self.assertEqual(rules(anchored), [])


class Permissions(unittest.TestCase):
    def test_top_level_must_be_empty(self):
        self.assertEqual(rules(swap("permissions: {}\n", "")), ["permissions"])
        self.assertEqual(rules(swap("permissions: {}\n", "permissions: read-all\n")), ["permissions"])
        self.assertEqual(rules(swap("permissions: {}\n", "permissions: { contents: read }\n")), ["permissions"])

    def test_job_write_all_fails(self):
        self.assertEqual(rules(swap("permissions: { contents: read }", "permissions: write-all")), ["permissions"])


class Expressions(unittest.TestCase):
    def test_text_contexts_fail(self):
        for expr in [
            "github.event.pull_request.title",
            "github.head_ref",
            "steps.c.outputs.class",
            "needs.a.outputs.x",
            "inputs.name",
            "env.TITLE",
            "github.event.pull_request.number || github.event.merge_group.head_ref",
            "format('{0}', github.event.pull_request.body)",
            "toJSON(github.event.issue)",
            "contains(github.event.pull_request.title, '(') && github.event.pull_request.title || ''",
        ]:
            with self.subTest(expr):
                self.assertEqual(rules(swap("printf '%s' \"$TITLE\"", "echo ${{ " + expr + " }}")), ["expressions"])

    def test_fixed_compared_and_literal_pass(self):
        for expr in [
            "github.run_id",
            "github.event.merge_group.base_sha",
            "needs.classify.outputs.class == 'promotion' && '--promotion' || ''",
            "contains(github.event.pull_request.title, 'x') && 'y' || 'z'",
            "!github.event.pull_request.draft && 'a' || 'b'",
            "'github.event.pull_request.title'",
            "hashFiles('lean-toolchain')",
        ]:
            with self.subTest(expr):
                self.assertEqual(rules(swap("printf '%s' \"$TITLE\"", "echo ${{ " + expr + " }}")), [])

    def test_github_script_sink(self):
        step = (
            "      - uses: actions/github-script@"
            + "b" * 40
            + " # v7\n        with:\n          script: console.log('${{ github.event.issue.title }}')\n"
        )
        self.assertEqual(rules(CLEAN + step), ["expressions"])


class PrCode(unittest.TestCase):
    def run_step(self, cmd: str, text: str = TARGET) -> list[str]:
        return rules(text + f"      - run: {cmd}\n")

    def test_checkout_of_the_pr_fails(self):
        for ref in ["${{ github.event.pull_request.head.sha }}", "${{ env.HEAD }}", "${{ github.head_ref }}", "refs/pull/1/merge"]:
            with self.subTest(ref):
                self.assertEqual(rules(swap('ref: "${{ env.BASE }}"', f'ref: "{ref}"', TARGET)), ["pr-code"])
        self.assertEqual(
            rules(swap('ref: "${{ env.BASE }}"', 'repository: "${{ github.event.pull_request.head.repo.full_name }}"', TARGET)), ["pr-code"]
        )

    def test_case_variants(self):
        self.assertEqual(
            rules(swap(CO, CO.replace("actions/checkout", "Actions/Checkout"), TARGET).replace(", persist-credentials: false", "")),
            ["token"],
        )
        self.assertEqual(rules(swap('ref: "${{ env.BASE }}"', 'REF: "${{ github.event.pull_request.head.sha }}"', TARGET)), ["pr-code"])
        self.assertEqual(rules(swap("persist-credentials: false", "Persist-Credentials: false", TARGET)), [])
        step = (
            "      - uses: Actions/GitHub-Script@"
            + "b" * 40
            + " # v7\n        with:\n          Script: console.log('${{ github.event.issue.title }}')\n"
        )
        self.assertEqual(rules(CLEAN + step), ["expressions"])

    def test_workflow_run_head_fails(self):
        wr_ = swap("  pull_request_target:\n    types: [opened]\n", "  workflow_run:\n    workflows: [x]\n", TARGET)
        self.assertEqual(rules(swap('ref: "${{ env.BASE }}"', 'ref: "${{ github.event.workflow_run.head_sha }}"', wr_)), ["pr-code"])

    def test_base_checkout_passes(self):
        self.assertEqual(rules(swap('ref: "${{ env.BASE }}"', 'ref: "${{ github.event.pull_request.base.sha }}"', TARGET)), [])
        self.assertEqual(rules(swap(", persist-credentials", ', repository: "${{ github.repository }}", persist-credentials', TARGET)), [])

    def test_workflow_commit_and_default_branch_pass(self):
        for ref in ["${{ github.workflow_sha }}", "${{ github.event.repository.default_branch }}"]:
            with self.subTest(ref):
                self.assertEqual(rules(swap('ref: "${{ env.BASE }}"', f'ref: "{ref}"', TARGET)), [])

    def test_git_commands(self):
        self.assertEqual(self.run_step('git checkout -q "$HEAD" -- data'), [])
        self.assertEqual(self.run_step('git checkout -q "$HEAD" -- data/staging/x.jsonl'), [])
        self.assertEqual(self.run_step('git show "$HEAD:data/x.jsonl" > x.jsonl'), [])
        self.assertEqual(self.run_step('git fetch -q origin "+$PR_REF:refs/remotes/origin/pr-head"'), [])
        self.assertEqual(self.run_step('git checkout "$(git merge-base main "$HEAD")"'), [])
        for cmd in [
            'git checkout "$HEAD"',
            'git checkout -q "$HEAD" -- scripts',
            'git checkout -q "$HEAD" -- data ../scripts',
            'git checkout -q "$HEAD" -- data && git checkout "$HEAD" -- scripts',
            'git diff "$BASE...$HEAD" | git apply',
            'git -C repo switch --detach "$HEAD"',
            'git archive "$HEAD" | tar -x',
            "git reset --hard FETCH_HEAD",
            'git show "$HEAD:x.sh" | bash',
            'python3 <(git show "$HEAD:x.py")',
        ]:
            with self.subTest(cmd):
                self.assertEqual(self.run_step(cmd), ["pr-code"])

    def test_gh_pr_checkout_and_diff(self):
        self.assertEqual(self.run_step('gh pr checkout "$PR"'), ["pr-code"])
        self.assertEqual(self.run_step('gh pr diff "$PR" | git apply'), ["pr-code"])
        self.assertEqual(self.run_step('gh pr diff "$PR" > pr.diff'), [])

    def test_any_patch_application(self):
        for cmd in [
            'gh pr diff "$PR" | patch -p1',
            "patch -p1 < pr.diff",
            "git apply pr.diff",
            "git am < mail",
            "sudo patch -p0 -i x",
            "if [ -f saved.patch ]; then git apply saved.patch; fi",
            "if [ -f s.diff ]; then patch -p1 < s.diff; fi",
            'for p in *.diff; do patch -p1 < "$p"; done',
            "true && { patch -p1 < x.diff; }",  # a bare `{` would start a YAML mapping, not a script
            "ls *.diff | xargs patch",
            "out=$(patch -p1 < x.diff)",
        ]:
            with self.subTest(cmd):
                self.assertEqual(self.run_step(cmd), ["pr-code"])
        for cmd in [
            "gh api -X PATCH repos/o/r/issues/1 -f state=closed",
            "echo patch",
            "git log --patch -1",
            "cp a.patch b.patch",
            "mkdir patch-dir",
        ]:
            with self.subTest(cmd):
                self.assertEqual(self.run_step(cmd), [])
        self.assertEqual(self.run_step("patch -p1 < pr.diff", CLEAN), [])

    def test_local_action_in_a_privileged_workflow(self):
        self.assertEqual(rules(TARGET + "      - uses: ./.github/actions/x\n"), ["pr-code"])
        self.assertEqual(rules(TARGET + "      - uses: $/.github/actions/x\n"), [])
        self.assertEqual(rules(CLEAN + "      - uses: ./.github/actions/x\n"), [])

    def test_same_commands_in_an_unprivileged_workflow_pass(self):
        self.assertEqual(self.run_step('git checkout "$HEAD"', CLEAN), [])
        self.assertEqual(self.run_step('gh pr checkout "$PR"', CLEAN), [])


ELAN_COMMIT = "https://raw.githubusercontent.com/leanprover/elan/0e36a07b9bbcc5381fa6250df109f9a4f94d7bac/elan-init.sh"
ELAN_MASTER = "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
DIGEST_LINE = 'echo "a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53  elan-init.sh" | sha256sum -c -'


def with_run(*cmds: str) -> str:
    """CLEAN with the given shell lines added to its `run:` block."""
    anchor = "          printf '%s' \"$TITLE\" > t.txt\n"
    return swap(anchor, anchor + "".join("          " + line + "\n" for c in cmds for line in c.split("\n")))


class Installer(unittest.TestCase):
    """Tau Ceti, 2026-08-18 (issue 3725): `elan-init` was fetched unpinned in five workflows, one of them the job that held the cache key."""

    def test_a_download_piped_into_a_shell_fails(self):
        for cmd in (
            "curl -sSfL https://example.com/install.sh | sh",
            f"curl -sSfL {ELAN_MASTER} | sh -s -- -y",
            "wget -qO- https://get.example.com | sudo bash",
            "wget -qO- https://get.example.com | sudo -E bash -",
            "curl -fsSL https://get.example.com | env FOO=1 bash",
            "curl -sSf https://x.io/i.py | python3 -",
            "curl -s https://x.io/a | tee /tmp/a | sh",
        ):
            with self.subTest(cmd):
                self.assertEqual(rules(with_run(cmd)), ["installer"])

    def test_a_stream_is_refused_even_at_a_pinned_commit(self):
        found = wr.Checker(".github/workflows/t.yml", with_run(f"curl -sSfL {ELAN_COMMIT} | sh -s -- -y")).run().findings
        self.assertEqual([f[2] for f in found], ["installer"])
        self.assertIn("cannot be checked against a digest before it runs", found[0][3])

    def test_a_download_handed_to_a_shell_by_substitution_fails(self):
        for cmd in (
            'sh -c "$(curl -fsSL https://example.com/i.sh)"',
            'bash -c "$(wget -qO- https://example.com/i.sh)"',
            "bash -ec '$(curl -s https://example.com/i.sh)'",
            "bash <(curl -s https://example.com/i.sh)",
            "source <(curl -s https://example.com/env.sh)",
            'eval "$(curl -s https://example.com/env)"',
            "sh <(wget -qO- https://example.com/i.sh)",
        ):
            with self.subTest(cmd):
                self.assertEqual(rules(with_run(cmd)), ["installer"])

    def test_a_continued_line_is_one_command(self):
        self.assertEqual(rules(with_run("curl -sSfL \\\n  https://example.com/i.sh \\\n  | sh")), ["installer"])

    def test_a_downloaded_script_must_come_from_a_commit_and_be_checked_first(self):
        passing = f"curl --proto '=https' -sSfL -o elan-init.sh {ELAN_COMMIT}\n{DIGEST_LINE}\nsh elan-init.sh -y"
        self.assertEqual(rules(with_run(passing)), [])
        for name, cmd, fragment in (
            ("a branch", f"curl -sSfL -o elan-init.sh {ELAN_MASTER}\n{DIGEST_LINE}\nsh elan-init.sh -y", "no full 40-hex commit"),
            (
                "a tag",
                "curl -sSfL -o i.sh https://github.com/o/r/raw/v1.2.3/i.sh\nsha256sum -c sums.txt\nbash i.sh",
                "no full 40-hex commit",
            ),
            ("no digest", f"curl -sSfL -o elan-init.sh {ELAN_COMMIT}\nsh elan-init.sh -y", "without a `sha256sum -c`"),
            (
                "a digest after the run",
                f"curl -sSfL -o elan-init.sh {ELAN_COMMIT}\nsh elan-init.sh -y\n{DIGEST_LINE}",
                "without a `sha256sum -c`",
            ),
            (
                "a digest of another file",
                f'curl -sSfL -o elan-init.sh {ELAN_COMMIT}\necho "{"a" * 64}  other.sh" | sha256sum -c -\nsh elan-init.sh',
                "without a `sha256sum -c`",
            ),
            (
                "a digest that is printed, not checked",
                f"curl -sSfL -o elan-init.sh {ELAN_COMMIT}\nsha256sum elan-init.sh\nsh elan-init.sh",
                "without a `sha256sum -c`",
            ),
            ("an output redirect", f"curl -sSfL {ELAN_COMMIT} > elan-init.sh\nbash elan-init.sh", "without a `sha256sum -c`"),
            ("wget", f"wget -q -O elan-init.sh {ELAN_COMMIT}\n./elan-init.sh", "without a `sha256sum -c`"),
            ("source", f"curl -sSfL -o env.sh {ELAN_COMMIT}\nsource env.sh", "without a `sha256sum -c`"),
        ):
            with self.subTest(name):
                found = wr.Checker(".github/workflows/t.yml", with_run(cmd)).run().findings
                self.assertEqual([f[2] for f in found], ["installer"], found)
                self.assertIn(fragment, found[0][3])

    def test_the_digest_may_be_checked_with_shasum_or_a_checksum_file_that_names_the_download(self):
        for check in (
            'echo "a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53  elan-init.sh" | shasum -a 256 -c -',
            "sha256sum --check elan-init.sh.sha256 # lists elan-init.sh",
            "shasum -c SHA256SUMS --ignore-missing elan-init.sh",
        ):
            with self.subTest(check):
                self.assertEqual(rules(with_run(f"curl -sSfL -o elan-init.sh {ELAN_COMMIT}\n{check}\nsh elan-init.sh")), [])

    def test_what_is_not_run_is_not_an_installer(self):
        for cmd in (
            "curl -sSfL -o data.json https://example.com/x.json\njq . data.json",
            "curl -fsS https://example.com/x | sha256sum",
            "curl -fsS https://example.com/x | jq .name",
            "curl -sS -m 30 -X POST https://example.com/refresh 2>&1 | head -c 300",
            'curl -sSfL -o elan.tar.gz https://example.com/elan.tar.gz\necho "abc  elan.tar.gz" | sha256sum -c -\ntar xzf elan.tar.gz',
            "echo 'never run: curl https://example.com/i.sh | sh'",
            "# curl https://example.com/i.sh | sh",
            "curl -sSfL -o i.sh https://example.com/i.sh\ncat i.sh",
        ):
            with self.subTest(cmd):
                self.assertEqual(rules(with_run(cmd)), [])

    def test_a_script_that_runs_in_two_places_is_judged_per_run(self):
        both = f"curl -sSfL -o a.sh {ELAN_COMMIT}\n{DIGEST_LINE.replace('elan-init.sh', 'a.sh')}\nsh a.sh\ncurl -sSfL -o b.sh {ELAN_COMMIT}\nsh b.sh"
        found = wr.Checker(".github/workflows/t.yml", with_run(both)).run().findings
        self.assertEqual([f[2] for f in found], ["installer"])
        self.assertIn("`b.sh`", found[0][3])

    def test_the_finding_points_at_the_line(self):
        text = with_run("curl -sSfL https://example.com/install.sh | sh")
        (found,) = wr.Checker(".github/workflows/t.yml", text).run().findings
        self.assertTrue(text.splitlines()[found[1] - 1].strip().startswith("curl"))

    def test_elan_is_installed_from_a_digest_in_every_workflow_of_the_repository(self):
        for p in sorted((TREE / ".github/workflows").glob("*.yml")):
            text = p.read_text()
            if "leanprover/elan" in text:
                with self.subTest(p.name):
                    self.assertNotIn("/latest/", text)
                    self.assertNotIn("elan-init.sh", text)  # the script of that repository downloads whatever release is latest
                    self.assertIn("sha256sum -c", text)


TOKEN_SHA = "5f3d7a0e6f1b2c4d8e9a0b1c2d3e4f5a6b7c8d9e"  # pragma: allowlist secret (a commit id)


def with_token(uses: str, perms: str = "          permission-contents: write\n") -> str:
    step = f"      - uses: {uses}\n        with:\n          app-id: ${{{{ vars.APP_ID }}}}\n          private-key: ${{{{ secrets.APP_KEY }}}}\n{perms}"
    return swap("      - name: work\n", step + "      - name: work\n")


class AppToken(unittest.TestCase):
    """Tau Ceti, 2026-09-17 (PR 7206): create-github-app-token v1 silently ignored `permission-*` and minted the App's full installation permissions."""

    def test_v2_or_later_with_a_permission_passes(self):
        for tag in ("v2", "v2.2.1", "v3.0.0", "v10"):
            with self.subTest(tag):
                self.assertEqual(rules(with_token(f"actions/create-github-app-token@{TOKEN_SHA} # {tag}")), [])

    def test_v1_fails_however_it_is_pinned(self):
        for tag in ("v1", "v1.12.0"):
            with self.subTest(tag):
                found = (
                    wr.Checker(".github/workflows/t.yml", with_token(f"actions/create-github-app-token@{TOKEN_SHA} # {tag}")).run().findings
                )
                self.assertEqual([f[2] for f in found], ["app-token"])
                self.assertIn("silently ignored", found[0][3])
        self.assertEqual(
            sorted(rules(with_token("actions/create-github-app-token@v1"))), ["app-token", "pinned"]
        )  # a moving tag: two findings

    def test_a_token_with_no_permission_input_fails(self):
        found = (
            wr.Checker(".github/workflows/t.yml", with_token(f"actions/create-github-app-token@{TOKEN_SHA} # v2.2.1", perms=""))
            .run()
            .findings
        )
        self.assertEqual([f[2] for f in found], ["app-token"])
        self.assertIn("every permission", found[0][3])

    def test_a_permission_input_of_any_kind_counts_and_other_inputs_do_not(self):
        self.assertEqual(
            rules(with_token(f"actions/create-github-app-token@{TOKEN_SHA} # v2", perms="          permission-pull-requests: read\n")), []
        )
        self.assertEqual(
            rules(with_token(f"actions/create-github-app-token@{TOKEN_SHA} # v2", perms="          owner: o\n          repositories: r\n")),
            ["app-token"],
        )

    def test_a_commit_with_no_version_comment_cannot_be_judged(self):
        self.assertIn("app-token", rules(with_token(f"actions/create-github-app-token@{TOKEN_SHA}")))

    def test_the_action_name_is_matched_without_regard_to_case_and_other_actions_are_left_alone(self):
        self.assertEqual(rules(with_token(f"Actions/Create-GitHub-App-Token@{TOKEN_SHA} # v1")), ["app-token"])
        self.assertEqual(rules(with_token(f"actions/create-something-else@{TOKEN_SHA} # v1", perms="")), [])


class Online(unittest.TestCase):
    def test_compare_status_decides(self):
        with tempfile.TemporaryDirectory() as d:
            gh = Path(d) / "gh"
            # fake gh (`gh api repos/<repo>/compare/<tag>...<sha> --jq .status`): the impostor commit (all c's) has
            # diverged from its tag, every other commit is identical to it
            gh.write_text('#!/bin/sh\ncase "$2" in *cccccccc*) echo diverged ;; *) echo identical ;; esac\n')
            gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
            pins = [("f", 1, "actions/checkout", "a" * 40, "v4"), ("f", 2, "actions/checkout", "c" * 40, "v4")]
            with mock.patch.dict(os.environ, {"PATH": f"{d}:{os.environ['PATH']}"}):
                found = wr.verify_pins(pins)
            self.assertEqual([(f[1], f[2]) for f in found], [(2, "pinned")])
            self.assertIn("impostor", found[0][3])


class Changed(unittest.TestCase):
    def test_reads_the_changed_files_from_head(self):
        with tempfile.TemporaryDirectory() as d:
            run = lambda *a: subprocess.run(["git", *a], cwd=d, check=True, capture_output=True, text=True).stdout.strip()  # noqa: E731
            run("init", "-q", "-b", "main")
            run("config", "user.email", "t@t")
            run("config", "user.name", "t")
            w = Path(d) / ".github/workflows"
            w.mkdir(parents=True)
            (w / "t.yml").write_text(CLEAN)
            (Path(d) / "README.md").write_text("x\n")
            run("add", "-A")
            run("commit", "-q", "-m", "base")
            base = run("rev-parse", "HEAD")
            (Path(d) / "README.md").write_text("y\n")
            run("commit", "-qam", "docs only")
            docs = run("rev-parse", "HEAD")
            (w / "t.yml").write_text(swap(CO, "actions/checkout@v4"))
            run("commit", "-qam", "unpinned")
            bad = run("rev-parse", "HEAD")
            run("checkout", "-q", base)  # the working tree holds the clean file: the checker must read HEAD's
            script = str(CI / "workflow_rules.py")
            r = subprocess.run([sys.executable, script, "--changed", base, docs], cwd=d, capture_output=True, text=True)
            self.assertEqual((r.returncode, r.stdout.strip()), (0, "no workflow or action file changed"))
            r = subprocess.run([sys.executable, script, "--changed", base, bad], cwd=d, capture_output=True, text=True)
            self.assertEqual(r.returncode, 1)
            self.assertIn("[pinned] `actions/checkout@v4`", r.stdout)
            gone = Path(d) / "scripts/ci/workflow_rules.py"  # the checker in the tree, then a PR that deletes it
            run("checkout", "-q", "main")
            gone.parent.mkdir(parents=True)
            gone.write_text("# checker\n")
            run("add", "-A")
            run("commit", "-qm", "add checker")
            with_checker = run("rev-parse", "HEAD")
            gone.unlink()
            run("commit", "-qam", "delete checker")
            r = subprocess.run(
                [sys.executable, script, "--changed", with_checker, run("rev-parse", "HEAD")], cwd=d, capture_output=True, text=True
            )
            self.assertEqual(r.returncode, 1)
            self.assertIn("[removed]", r.stdout)


if __name__ == "__main__":
    unittest.main()


class WriteAndPr(unittest.TestCase):
    """A job that holds a write permission never fetches the PR's or the queue entry's commits."""

    FETCH = 'git fetch -q --no-tags origin "+$PR_REF:refs/remotes/origin/pr-head"'

    def wf(self, perms: str, run: str, on: str = "pull_request_target") -> str:
        return f"""name: t
on:
  {on}:
permissions: {{}}
jobs:
  a:
    runs-on: ubuntu-latest
    permissions: {perms}
    steps:
      - uses: {CO}
        with: {{ persist-credentials: false }}
      - run: {run}
"""

    def test_a_write_job_that_fetches_the_pr_is_refused(self):
        self.assertIn("write-and-pr", rules(self.wf("{ contents: read, pull-requests: write }", f"'{self.FETCH}'")))
        self.assertIn("write-and-pr", rules(self.wf("{ actions: write }", f"'{self.FETCH}'", on="merge_group")))
        self.assertIn("write-and-pr", rules(self.wf("{ pull-requests: write }", "'git fetch origin refs/pull/1/head'", on="workflow_run")))

    def test_a_read_only_job_may_fetch_it(self):
        self.assertNotIn("write-and-pr", rules(self.wf("{ contents: read }", f"'{self.FETCH}'")))

    def test_a_write_job_that_does_not_fetch_it_passes(self):
        self.assertNotIn("write-and-pr", rules(self.wf("{ pull-requests: write }", "'gh pr edit 1 --add-label x'")))
        self.assertNotIn("write-and-pr", rules(self.wf("{ pull-requests: write }", "'git fetch origin main'")))

    def test_an_unprivileged_trigger_is_not_this_rules_business(self):
        self.assertNotIn("write-and-pr", rules(self.wf("{ pull-requests: write }", f"'{self.FETCH}'", on="pull_request")))

    def test_odd_shapes_do_not_crash(self):
        for perms in ("write-all", "5", "{}"):
            rules(self.wf(perms, f"'{self.FETCH}'"))

    # The next cases are the findings of the review of this rule: each asserts the rule list is exactly ["write-and-pr"], so another
    # rule firing cannot hide that this one missed.
    def custom(self, on: str, env: str, steps: str, perms: str = "{ pull-requests: write }") -> str:
        return f"""name: t
on:
  {on}:
permissions: {{}}
env:
{env}
jobs:
  a:
    runs-on: ubuntu-latest
    permissions: {perms}
    steps:
{steps}
"""

    ALIASES = "  HEAD: ${{ github.event.pull_request.head.sha || github.event.merge_group.head_sha }}\n  BASE: ${{ github.event.pull_request.base.sha || github.event.merge_group.base_sha }}"

    def test_the_head_alias_is_recognised(self):
        steps = '      - run: git fetch -q origin "$HEAD"'
        self.assertEqual(rules(self.custom("pull_request_target", self.ALIASES, steps)), ["write-and-pr"])
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, steps)), ["write-and-pr"])

    def test_any_env_name_built_from_the_prs_commit_is_recognised(self):
        env = "  ENTRY: ${{ github.event.merge_group.head_sha }}"
        for run in ('git fetch origin "$ENTRY"', "git fetch origin ${ENTRY}", 'git -C . checkout "$ENTRY"'):
            self.assertEqual(rules(self.custom("merge_group", env, f"      - run: {run}")), ["write-and-pr"], run)

    def test_a_job_or_step_env_alias_is_recognised_too(self):
        steps = '      - env: { C: "${{ github.event.pull_request.head.sha }}" }\n        run: git fetch origin "$C"'
        self.assertEqual(rules(self.custom("pull_request_target", "  X: 1", steps)), ["write-and-pr"])

    def test_the_base_side_may_be_fetched_by_a_write_job(self):
        steps = '      - run: git fetch -q origin "$BASE"'
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, steps)), [])

    def test_a_default_checkout_in_a_merge_group_write_job_is_the_queue_entry(self):
        steps = f"      - uses: {CO}\n        with: {{ persist-credentials: false }}\n      - run: python3 scripts/anything.py"
        self.assertEqual(rules(self.custom("merge_group", "  X: 1", steps)), ["write-and-pr"])

    def test_a_merge_group_checkout_of_the_entry_by_name_is_refused_and_of_the_base_is_not(self):
        entry = f'      - uses: {CO}\n        with: {{ ref: "${{{{ github.event.merge_group.head_sha }}}}", persist-credentials: false }}'
        alias = f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.HEAD }}}}", persist-credentials: false }}'
        base = f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.BASE }}}}", persist-credentials: false }}'
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, entry)), ["write-and-pr"])
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, alias)), ["write-and-pr"])
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, base)), [])

    def test_a_default_checkout_in_a_pull_request_target_write_job_is_the_base(self):
        steps = f"      - uses: {CO}\n        with: {{ persist-credentials: false }}"
        self.assertEqual(rules(self.custom("pull_request_target", "  X: 1", steps)), [])

    def test_a_read_only_job_may_do_all_of_it(self):
        steps = f'      - uses: {CO}\n        with: {{ persist-credentials: false }}\n      - run: git fetch origin "$HEAD"'
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, steps, perms="{ contents: read }")), [])

    # The second review round: github.sha / github.ref are the queue entry in a merge_group workflow, an empty ref is the default ref,
    # `gh pr checkout` and a patch load the PR just as a fetch does, and `repository:` can name a fork.
    def test_sha_and_ref_are_the_queue_entry_under_merge_group_and_the_base_otherwise(self):
        for ref in ("github.sha", "github.ref", "github.workflow_sha"):
            steps = f'      - uses: {CO}\n        with: {{ ref: "${{{{ {ref} }}}}", persist-credentials: false }}'
            self.assertEqual(rules(self.custom("merge_group", "  X: 1", steps)), ["write-and-pr"], ref)
            self.assertEqual(rules(self.custom("pull_request_target", "  X: 1", steps)), [], ref)  # the base branch's commit there

    def test_the_default_environment_variables_are_the_queue_entry_under_merge_group(self):
        for var in ("$GITHUB_SHA", "${GITHUB_REF}", "$GITHUB_WORKFLOW_SHA"):
            self.assertEqual(rules(self.custom("merge_group", "  X: 1", f'      - run: git fetch origin "{var}"')), ["write-and-pr"], var)
        self.assertEqual(
            rules(self.custom("pull_request_target", "  X: 1", '      - run: git fetch origin "$GITHUB_HEAD_REF"')), ["write-and-pr"]
        )
        self.assertEqual(rules(self.custom("pull_request_target", "  X: 1", '      - run: git fetch origin "$GITHUB_SHA"')), [])

    def test_an_empty_ref_is_the_default_ref(self):
        for ref in ('""', '" "', '"${{ env.EMPTY }}"'):
            steps = f"      - uses: {CO}\n        with: {{ ref: {ref}, persist-credentials: false }}"
            self.assertEqual(rules(self.custom("merge_group", "  EMPTY: ''", steps)), ["write-and-pr"], ref)

    def test_gh_pr_checkout_and_patches_load_the_pr_after_an_explicit_base_checkout(self):
        base = f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.BASE }}}}", persist-credentials: false }}\n'
        for run in ("gh pr checkout 123", "git apply x.patch", "git am < x.mbox", "patch -p1 < x.diff"):
            self.assertEqual(rules(self.custom("merge_group", self.ALIASES, base + f"      - run: {run}")), ["write-and-pr"], run)

    def test_reading_the_base_is_still_fine_and_a_log_of_the_prs_commits_is_not(self):
        base = f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.BASE }}}}", persist-credentials: false }}\n'
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, base + '      - run: git show "$BASE:README.md"')), [])
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, base + '      - run: git log "$BASE..$HEAD"')), ["write-and-pr"])

    def test_a_checkout_of_another_repository_is_refused(self):
        steps = f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.BASE }}}}", repository: "${{{{ github.event.pull_request.head.repo.full_name }}}}", persist-credentials: false }}'
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, steps)), ["write-and-pr"])
        ok = f'      - uses: {CO}\n        with: {{ ref: "${{{{ env.BASE }}}}", repository: "${{{{ github.repository }}}}", persist-credentials: false }}'
        self.assertEqual(rules(self.custom("merge_group", self.ALIASES, ok)), [])
