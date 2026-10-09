"""agent_guard.py against synthetic repositories (docs/agent-security.md): every rule has a hostile case that must be found and one that must pass.

No network, no Lean. The policies under test are the repository's own (scripts/ci/agent-paths.json, .github/agent-paths.json, .github/CODEOWNERS)."""

from __future__ import annotations

import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
TREE = CI.parents[1]
sys.path.insert(0, str(CI))

import agent_guard as ag  # noqa: E402
from warden import scope  # noqa: E402

# a token-shaped value, assembled here so that no scanner reads this file as a leak
FAKE_TOKEN = "gh" + "p_" + "A1b2C3d4E5f6G7h8I9j0K1l2M3n4O5p6Q7r8"  # pragma: allowlist secret


class Repo:
    """A repository with the shape of the real one, a base commit on `main`, and helpers to build a PR on branch `pr`."""

    def __init__(self, codeowners=None):
        self.dir = Path(tempfile.mkdtemp())
        self.git("init", "-q", "-b", "main")
        for rel in (".github/agent-paths.json", "scripts/ci/agent-paths.json"):
            self.write(rel, (TREE / rel).read_text(encoding="utf-8"))
        self.write(
            ".github/CODEOWNERS", codeowners if codeowners is not None else (TREE / ".github/CODEOWNERS").read_text(encoding="utf-8")
        )
        self.write("data/staging/lib.jsonl", '{"name": "Lib.a"}\n')
        self.write("data/trusted/lib.jsonl", '{"name": "Lib.old"}\n')
        self.write("Tengoku/Lib/Basic.lean", "theorem Lib.old : 1 + 1 = 2 := rfl\n")
        self.write("scripts/x.py", "print(1)\n")
        self.write(".github/workflows/ci.yml", "name: ci\n")
        self.write("scripts/ci/requirements/yaml.txt", "pyyaml==6.0\n")
        self.write("README.md", "# t\n")
        shutil.copytree(TREE / "schemas", self.dir / "schemas")  # classify.py reads them
        self.commit("base")
        self.base = self.rev()
        self.git("checkout", "-q", "-b", "pr")

    def git(self, *a, **kw):
        env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
        return subprocess.run(["git", *a], cwd=self.dir, capture_output=True, text=True, check=True, env=env, **kw).stdout

    def write(self, rel, text):
        p = self.dir / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def commit(self, msg):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg)
        return self.rev()

    def rev(self, ref="HEAD"):
        return self.git("rev-parse", ref).strip()

    def guard(self, **kw):
        cls = kw.pop("cls", "tooling")
        defaults = {
            "repo": str(self.dir),
            "base": self.base,
            "head": self.rev(),
            "scope_policy": str(self.dir / "scripts/ci/agent-paths.json"),
        }
        return ag.check(ag.Inputs(**{**defaults, **kw}), cls=cls)

    def codes(self, doc, check=None):
        return sorted(f["code"] for f in doc["findings"] if check is None or f["check"] == check)


def found(doc, check, code):
    return any(f["check"] == check and f["code"] == code for f in doc["findings"])


class WhoIsAnAgent(unittest.TestCase):
    def test_accounts_branches_and_titles(self):
        cases = [
            (("dependabot[bot]", "Bot", "dependabot/pip/x", "build(deps): bump", "tengoku-bot", "tooling"), "dependabot"),
            (("tengoku-bot", "User", "x", "x", "tengoku-bot", "promotion"), "factory"),
            (("renovate[bot]", "Bot", "x", "x", "tengoku-bot", "tooling"), "bot"),
            (("someone", "Bot", "x", "x", "tengoku-bot", "tooling"), "bot"),
            (("someone", "User", "intake/apap-37164062081", "x", "tengoku-bot", "tooling"), "factory"),
            (("someone", "User", "x", "intake: apap (56 verified theorems)", "tengoku-bot", "tooling"), "factory"),
            (("someone", "User", "promote/cloud-20261009T000000Z", "x", "tengoku-bot", "tooling"), "factory"),
            (("someone", "User", "scopefix-vcvio", "x", "tengoku-bot", "tooling"), "factory"),
        ]
        for args, want in cases:
            self.assertEqual(ag.scope_class(*args)[0], want, args)

    def test_the_repository_variable_names_a_factory_only_for_the_factorys_classes(self):
        # the sandbox's TENGOKU_BOT is a person: their tooling PRs are not the factory's, their promotions are
        self.assertEqual(ag.scope_class("mikael-bashir", "User", "x", "sonar: fix", "mikael-bashir", "tooling")[0], None)
        self.assertEqual(ag.scope_class("mikael-bashir", "User", "x", "sonar: fix", "mikael-bashir", "docs")[0], None)
        self.assertEqual(ag.scope_class("mikael-bashir", "User", "x", "Promote: 3 records", "mikael-bashir", "promotion")[0], "factory")
        self.assertEqual(ag.scope_class("a-human", "User", "feature", "Add a lemma", "tengoku-bot", "content")[0], None)

    def test_ai_trailers(self):
        self.assertEqual(
            ag.agent_commits(
                [
                    "fix\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>",
                    "plain",
                    "x\n\n🤖 Generated with [Claude Code](https://x)",
                ]
            ),
            2,
        )
        self.assertEqual(ag.agent_commits(["Co-authored-by: Ada Lovelace <ada@example.org>"]), 0)


class Modes(unittest.TestCase):
    def test_a_symlink_under_data_or_tengoku_is_found_in_any_pr(self):
        r = Repo()
        os.symlink("/etc/passwd", r.dir / "data/staging/lib2.jsonl")
        os.symlink("../../scripts/x.py", r.dir / "Tengoku/Lib/Link.lean")
        r.commit("links")
        doc = r.guard(actor="a-human")
        self.assertEqual(r.codes(doc, "modes"), ["symlink_added", "symlink_added"])
        self.assertEqual(doc["conclusion"], "failure")

    def test_an_executable_under_data_is_found_and_one_under_scripts_is_not(self):
        r = Repo()
        r.write("data/staging/run.sh", "echo hi\n")
        os.chmod(r.dir / "data/staging/run.sh", os.stat(r.dir / "data/staging/run.sh").st_mode | stat.S_IXUSR)
        r.write("scripts/tool.sh", "echo hi\n")
        os.chmod(r.dir / "scripts/tool.sh", os.stat(r.dir / "scripts/tool.sh").st_mode | stat.S_IXUSR)
        r.commit("exec")
        doc = r.guard(actor="a-human")
        self.assertEqual([f["path"] for f in doc["findings"] if f["check"] == "modes"], ["data/staging/run.sh"])

    def test_a_submodule_is_found(self):
        r = Repo()
        r.git("update-index", "--add", "--cacheinfo", "160000", "a" * 40, "Tengoku/Sub")
        r.git("commit", "-q", "-m", "submodule")
        self.assertIn("submodule_added", r.codes(r.guard(actor="a-human"), "modes"))

    def test_ordinary_files_pass(self):
        r = Repo()
        r.write("data/staging/lib2.jsonl", '{"name": "Lib.b"}\n')
        r.commit("records")
        self.assertEqual(r.guard(actor="a-human")["conclusion"], "success")


class ScopeOfAgentPRs(unittest.TestCase):
    def test_a_bot_pr_that_touches_the_tooling_is_refused(self):
        r = Repo()
        r.write("scripts/x.py", "print(2)\n")
        r.write(".github/workflows/ci.yml", "name: ci\non: push\n")
        r.commit("bot edits the gate")
        doc = r.guard(actor="tengoku-bot", head_ref="intake/lib-1")
        self.assertEqual(doc["scope_class"], "factory")
        paths = {f["path"] for f in doc["findings"] if f["code"] in ("path_not_allowed", "protected_path")}
        self.assertEqual(paths, {"scripts/x.py", ".github/workflows/ci.yml"})
        self.assertEqual(doc["conclusion"], "failure")

    def test_a_symlink_in_a_bot_pr_is_refused_by_mode_and_by_scope(self):
        r = Repo()
        os.symlink("/etc/passwd", r.dir / "data/intake.json")
        r.commit("link")
        doc = r.guard(actor="tengoku-bot")
        self.assertTrue(found(doc, "scope", "mode_not_allowed"))
        self.assertTrue(found(doc, "modes", "symlink_added"))

    def test_the_factorys_own_work_passes(self):
        r = Repo()
        r.write("data/intake/lib/manifest.jsonl", '{"name": "Lib.x"}\n')
        r.write("Tengoku/Lib2/A.lean", "theorem Lib2.a : True := trivial\n")
        r.write("Tengoku/Lib2.lean", "import Tengoku.Lib2.A\n")
        with open(r.dir / "data/staging/lib.jsonl", "a", encoding="utf-8") as fh:
            fh.write('{"name": "Lib.b"}\n')
        r.commit("intake: lib (1 verified theorem)")
        doc = r.guard(actor="tengoku-bot", head_ref="intake/lib-1", title="intake: lib (1 verified theorem in 1 module)")
        self.assertEqual(doc["findings"], [])
        self.assertEqual(doc["conclusion"], "success")

    def test_dependabot_may_touch_workflows_and_requirements_only(self):
        r = Repo()
        r.write(".github/workflows/ci.yml", "name: ci\n# bumped\n")
        r.write("scripts/ci/requirements/yaml.txt", "pyyaml==6.0.3\n")
        r.commit("bump")
        self.assertEqual(r.guard(actor="dependabot[bot]", actor_type="Bot")["findings"], [])
        r.write("scripts/x.py", "import os\n")
        r.commit("and a script")
        doc = r.guard(actor="dependabot[bot]", actor_type="Bot")
        self.assertEqual([f["path"] for f in doc["findings"]], ["scripts/x.py"])

    def test_an_unknown_bot_may_touch_nothing(self):
        r = Repo()
        r.write("README.md", "# changed\n")
        r.commit("docs")
        doc = r.guard(actor="renovate[bot]", actor_type="Bot")
        self.assertEqual(doc["scope_class"], "bot")
        self.assertEqual(r.codes(doc, "scope"), ["path_not_allowed"])

    def test_a_person_is_not_held_to_the_agent_policy(self):
        r = Repo()
        r.write("scripts/x.py", "print(3)\n")
        r.commit("tooling")
        doc = r.guard(actor="mikael-bashir", tengoku_bot="mikael-bashir")
        self.assertEqual(doc["scope_class"], "")
        self.assertEqual(doc["findings"], [])

    def test_size_caps_and_binary_files(self):
        r = Repo()
        (r.dir / "Tengoku/Lib/Blob.lean").write_bytes(b"\x00\x01\x02" * 100)
        r.commit("binary")
        self.assertTrue(found(r.guard(actor="tengoku-bot"), "scope", "binary_forbidden"))
        r.git("reset", "-q", "--hard", "HEAD~1")
        r.write("Tengoku/Lib/Long.lean", "-- x\n" * 20001)
        r.commit("long")
        self.assertTrue(found(r.guard(actor="tengoku-bot"), "scope", "new_file_too_long"))

    def test_a_restructure_is_judged_by_its_own_check_not_by_path(self):
        r = Repo()
        r.write("Tengoku.lean", "import Tengoku.Seed\n")
        r.commit("move")
        doc = r.guard(actor="tengoku-bot", cls="restructure")
        self.assertEqual(r.codes(doc, "scope"), [])
        self.assertIn("restructure_check", doc["scope_reason"])


class Secrets(unittest.TestCase):
    def test_a_secret_in_a_commit_message_is_found_whatever_pragma_it_carries(self):
        r = Repo()
        r.write("README.md", "# t2\n")
        r.git("add", "-A")
        r.git("commit", "-q", "-m", f"debug with token {FAKE_TOKEN}  # pragma: allowlist secret")
        doc = r.guard(actor="a-human")
        self.assertEqual([f["path"] for f in doc["findings"] if f["check"] == "secrets"][0][:7], "commit ")
        self.assertEqual(r.codes(doc, "secrets"), ["github_token"])
        self.assertNotIn(FAKE_TOKEN, json.dumps(doc))
        self.assertNotIn(FAKE_TOKEN[:8], ag.summary(doc))

    def test_a_secret_in_the_title_or_body_is_found(self):
        r = Repo()
        r.write("README.md", "# t2\n")
        r.commit("plain")
        doc = r.guard(actor="a-human", title="fix " + FAKE_TOKEN, body="see\n" + FAKE_TOKEN + "\n")
        self.assertEqual(sorted(f["path"] for f in doc["findings"] if f["check"] == "secrets"), ["PR body", "PR title"])

    def test_a_secret_in_an_added_line_is_found_and_a_pragma_is_counted(self):
        r = Repo()
        r.write("scripts/leak.py", f'TOKEN = "{FAKE_TOKEN}"\n')
        r.write("scripts/ok.py", f'TOKEN = "{FAKE_TOKEN}"  # pragma: allowlist secret\n')
        r.commit("add")
        doc = r.guard(actor="a-human")
        self.assertEqual([f["path"] for f in doc["findings"] if f["check"] == "secrets"], ["scripts/leak.py"])
        self.assertTrue(any("allowlist pragma" in n for n in doc["notices"]))

    def test_clean_metadata_passes(self):
        r = Repo()
        r.write("README.md", "# t2\n")
        r.commit("a plain message about 40 hex ids like " + "a" * 40)
        self.assertEqual(r.codes(r.guard(actor="a-human", title="a title", body="a body"), "secrets"), [])


class DroppedHumanWork(unittest.TestCase):
    def humans_pr(self):
        r = Repo()
        r.write(".github/workflows/ci.yml", "name: ci\njobs: {lint: {}, test: {}}\n")
        r.write("data/staging/lib2.jsonl", '{"name": "Lib.b"}\n')
        before = r.commit("a person adds the lint and test jobs and a record")
        return r, before

    def test_an_agent_that_reverts_the_humans_ci_to_get_green_is_found(self):
        r, before = self.humans_pr()
        r.write(".github/workflows/ci.yml", "name: ci\n")  # back to the base: base..head shows no change to this path at all
        r.commit("make it green\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>")
        self.assertNotIn(".github/workflows/ci.yml", [c.path for c in scope.changed(str(r.dir), r.base, r.rev())])
        doc = r.guard(actor="a-human", sender="a-human", before=before)
        self.assertEqual(
            [(f["code"], f["path"]) for f in doc["findings"] if f["check"] == "dropped"],
            [("human_work_modified", ".github/workflows/ci.yml")],
        )
        self.assertEqual(doc["agent_commits"], 1)

    def test_an_agent_that_deletes_a_human_owned_file_is_found(self):
        r, before = self.humans_pr()
        r.git("rm", "-q", "scripts/x.py")
        r.git("commit", "-q", "-m", "drop it")
        # sent by a bot account: no trailer needed
        r2 = r.guard(actor="a-human", sender="some-agent[bot]", before=before)
        self.assertEqual(
            [(f["code"], f["path"]) for f in r2["findings"] if f["check"] == "dropped"], [("human_work_deleted", "scripts/x.py")]
        )

    def test_a_push_by_a_person_is_not_judged(self):
        r, before = self.humans_pr()
        r.write(".github/workflows/ci.yml", "name: ci\n")
        r.commit("the person simplifies their own change")
        self.assertEqual(r.codes(r.guard(actor="a-human", sender="a-human", before=before), "dropped"), [])

    def test_an_agent_that_only_changes_what_humans_do_not_own_passes(self):
        r, before = self.humans_pr()
        r.write("data/staging/lib2.jsonl", '{"name": "Lib.b"}\n{"name": "Lib.c"}\n')
        r.commit("one more record\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>")
        self.assertEqual(r.codes(r.guard(actor="a-human", sender="a-human", before=before), "dropped"), [])

    def test_a_persons_pr_in_a_factorys_shape_is_judged_when_an_agent_pushes_to_it(self):
        r, before = self.humans_pr()
        r.write(".github/workflows/ci.yml", "name: ci\n")
        r.commit("make it green\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>")
        doc = r.guard(actor="a-human", sender="a-human", before=before, head_ref="intake/lib-1")
        self.assertEqual(doc["scope_class"], "factory")
        self.assertEqual(r.codes(doc, "dropped"), ["human_work_modified"])

    def test_a_bot_updating_its_own_pr_is_not_judged(self):
        r = Repo()
        r.write("Tengoku/Lib2/A.lean", "theorem a : True := trivial\n")
        before = r.commit("intake: lib2")
        r.write("Tengoku/Lib2/A.lean", "theorem a : True := by trivial\n")
        r.commit("intake: lib2 again")
        doc = r.guard(actor="tengoku-bot", sender="tengoku-bot", before=before, head_ref="intake/lib2-1")
        self.assertEqual(r.codes(doc, "dropped"), [])

    def test_a_previous_head_that_is_gone_is_a_notice_not_a_pass_or_a_failure(self):
        r, _before = self.humans_pr()
        doc = r.guard(actor="a-human", sender="x[bot]", before="b" * 40)
        self.assertEqual(doc["conclusion"], "neutral")
        self.assertEqual(
            [(f["code"], f["severity"]) for f in doc["findings"] if f["check"] == "dropped"], [("previous_head_gone", "notice")]
        )


class Ownership(unittest.TestCase):
    def test_the_repositorys_own_files_are_in_step(self):
        texts = [
            (TREE / p).read_text(encoding="utf-8")
            for p in (".github/CODEOWNERS", ".github/agent-paths.json", "scripts/ci/agent-paths.json")
        ]
        self.assertEqual([(f.code, f.path, f.detail) for f in ag.ownership_findings(*texts)], [])

    def test_a_human_path_that_lost_its_owner_is_drift(self):
        text = (
            (TREE / ".github/CODEOWNERS")
            .read_text(encoding="utf-8")
            .replace("/scripts/                @mikael-bashir @mikaelbashir14096545\n", "")
        )
        own = (TREE / ".github/agent-paths.json").read_text(encoding="utf-8")
        found_ = ag.ownership_findings(text, own, None)
        self.assertTrue(found_ and all(f.code == "diverged" for f in found_))
        self.assertTrue(any("scripts" in f.detail for f in found_))

    def test_one_owner_where_the_policy_wants_both_is_drift(self):
        text = re.sub(
            r"^/\.github/\s+@\S+ @\S+", "/.github/ @mikael-bashir", (TREE / ".github/CODEOWNERS").read_text(encoding="utf-8"), flags=re.M
        )
        self.assertIn("/.github/ @mikael-bashir\n", text)
        own = (TREE / ".github/agent-paths.json").read_text(encoding="utf-8")
        self.assertTrue(ag.ownership_findings(text, own, None))

    def test_an_agent_path_that_gained_an_owner_is_drift(self):
        text = (TREE / ".github/CODEOWNERS").read_text(encoding="utf-8") + "/data/staging/ @mikael-bashir @mikaelbashir14096545\n"
        own = (TREE / ".github/agent-paths.json").read_text(encoding="utf-8")
        self.assertTrue(ag.ownership_findings(text, own, None))

    def test_the_scope_policy_may_not_let_an_agent_write_what_it_protects(self):
        own = json.loads((TREE / ".github/agent-paths.json").read_text(encoding="utf-8"))
        doc = json.loads((TREE / "scripts/ci/agent-paths.json").read_text(encoding="utf-8"))
        self.assertEqual(ag.scope_policy_problems(doc, own), [])
        doc["classes"]["factory"]["allow"].append("/scripts/ci/")
        self.assertTrue(any("may write" in p for p in ag.scope_policy_problems(doc, own)))
        doc["protected"].append("/docs/")
        self.assertTrue(any("not human-owned" in p for p in ag.scope_policy_problems(doc, own)))

    def test_a_pr_that_breaks_the_policy_file_is_found_at_its_head(self):
        r = Repo()
        r.write(".github/agent-paths.json", '{"human": ["/scripts/"], "agent": [], "review": ["/nowhere/"]}')
        r.commit("break the policy")
        self.assertTrue(found(r.guard(actor="a-human"), "ownership", "policy_invalid"))

    def test_the_synthetic_repository_passes_when_untouched(self):
        r = Repo()
        r.write("README.md", "# t2\n")
        r.commit("docs")
        self.assertEqual(r.codes(r.guard(actor="a-human"), "ownership"), [])

    def test_owner_helpers(self):
        text = "/a/ @x @y\n/b/ @y @x  # both\n/c/ @x\n# comment\n"
        self.assertEqual(ag.human_owners_of(text), ("@x", "@y"))
        self.assertEqual(ag.normalise_owners(text, ("@x", "@y")).splitlines()[:3], ["/a/ @human", "/b/ @human", "/c/ @x"])


class ResultFile(unittest.TestCase):
    def doc(self):
        r = Repo()
        r.write("scripts/x.py", "print(9)\n")
        r.commit("x")
        return ag.validate_result(r.guard(actor="tengoku-bot"))

    def test_a_result_round_trips_and_makes_a_check_run(self):
        doc = self.doc()
        body = ag.check_run_body(ag.validate_result(json.loads(json.dumps(doc))))
        self.assertEqual(
            (body["name"], body["status"], body["conclusion"], body["head_sha"]), ("scope", "completed", "failure", doc["head_sha"])
        )
        self.assertIn("Advisory", body["output"]["summary"])

    def test_the_write_half_refuses_anything_that_is_not_exactly_a_result(self):
        doc = self.doc()
        for mutate in (
            lambda d: d.update(extra=1),
            lambda d: d.update(conclusion="approved"),
            lambda d: d.update(head_sha="main"),
            lambda d: d.update(scope_class="admin"),
            lambda d: d["findings"].append(
                {"check": "scope", "code": "x", "path": "<script>alert(1)</script>", "detail": "", "severity": "violation"}
            ),
            lambda d: d["findings"].append({"check": "nothing", "code": "x", "path": "", "detail": "", "severity": "violation"}),
            lambda d: d.update(notices=["`@someone` look"]),
            lambda d: d["counts"].update(extra=1),
        ):
            bad = json.loads(json.dumps(doc))
            mutate(bad)
            with self.assertRaises(ValueError):
                ag.validate_result(bad)

    def test_text_from_a_pr_is_plain_in_the_result(self):
        r = Repo()
        r.write("scripts/`evil`<b>@everyone.py", "x\n")
        r.commit("x")
        doc = ag.validate_result(r.guard(actor="tengoku-bot"))
        shown = ag.summary(doc)
        self.assertNotIn("<b>", shown)
        self.assertNotIn("`evil`", shown)

    def test_publish_posts_the_validated_result_as_a_check_run(self):
        doc = self.doc()
        d = Path(tempfile.mkdtemp())
        (d / "result.json").write_text(json.dumps(doc), encoding="utf-8")
        bin_ = Path(tempfile.mkdtemp())
        shim = bin_ / "gh"
        shim.write_text(f'#!/bin/sh\necho "$@" > "{d}/args"\ncat > "{d}/stdin"\n', encoding="utf-8")
        shim.chmod(0o755)
        env = {**os.environ, "PATH": f"{bin_}{os.pathsep}{os.environ['PATH']}"}
        done = subprocess.run(
            [sys.executable, str(CI / "agent_guard.py"), "publish", "--dir", str(d), "--repo", "o/r"],
            env=env,
            capture_output=True,
            text=True,
        )
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("repos/o/r/check-runs", (d / "args").read_text())
        self.assertEqual(json.loads((d / "stdin").read_text())["name"], "scope")
        (d / "result.json").write_text(json.dumps({**doc, "conclusion": "approved"}), encoding="utf-8")
        done = subprocess.run(
            [sys.executable, str(CI / "agent_guard.py"), "publish", "--dir", str(d), "--repo", "o/r"],
            env=env,
            capture_output=True,
            text=True,
        )
        self.assertEqual(done.returncode, 2)

    def test_cli_check_writes_the_result_for_a_real_classification(self):
        r = Repo()
        r.write("data/staging/lib2.jsonl", '{"name": "Lib.b"}\n')
        r.commit("records")
        out = Path(tempfile.mkdtemp())
        env = {**os.environ, "PR_ACTOR": "a-human", "PR_TITLE": "records", "PR_BODY": "", "TENGOKU_CI_ROOT": str(r.dir)}
        done = subprocess.run(
            [
                sys.executable,
                str(CI / "agent_guard.py"),
                "check",
                "--repo",
                str(r.dir),
                "--base",
                r.base,
                "--head",
                r.rev(),
                "--out",
                str(out),
            ],
            env=env,
            cwd=r.dir,
            capture_output=True,
            text=True,
        )
        self.assertEqual(done.returncode, 0, done.stderr)
        doc = json.loads((out / "result.json").read_text())
        self.assertEqual(doc["class"], "content")
        self.assertEqual(doc["conclusion"], "success")


if __name__ == "__main__":
    unittest.main()
