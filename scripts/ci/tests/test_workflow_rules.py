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
