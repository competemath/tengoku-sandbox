"""The autotag: a lane PR gets its isnad tags from the bot, as one commit on its own branch (scripts/ci/autotag.py, autotag_push.py; docs/isnad.md, "Born tagged").
The trusted half is tested against a fake GitHub: what must hold before anything is written, and that nothing is when one thing does not."""

from __future__ import annotations

import base64
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
TREE = HERE.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(TREE / "scripts"))
import autotag_push as ap  # noqa: E402
import test_studied_class as sct  # noqa: E402
from test_born_tagged import NOVEL, SEED, tagged_lean  # noqa: E402
from test_gates import Repo  # noqa: E402

REPO = "competemath/tengoku"
HEAD = "a" * 40
BOT = {"TENGOKU_BOT": "tengoku-bot"}
P1 = f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean"
P2 = f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(2)[:12]}.lean"


class Fake:
    """Just enough GitHub: a pull request, its files, the files' contents at the head, and a record of every write."""

    def __init__(self, files: dict[str, str] | None = None, **pr):
        self.contents = files if files is not None else {P1: sct.lean(1), P2: sct.lean(2)}
        self.pr = {
            "state": "open",
            "head": {"sha": HEAD, "ref": "supervisor/erdos-396", "repo": {"full_name": REPO}},
            "user": {"login": "tengoku-supervisor[bot]"},
            **pr,
        }
        self.status = {p: "added" for p in self.contents}
        self.writes: list[tuple[str, str, object]] = []
        self.blobs: dict[str, str] = {}

    def __call__(self, method: str, path: str, body: dict | None = None, raw: bool = False):
        if method == "GET" and path == f"repos/{REPO}/pulls/7":
            return self.pr
        if method == "GET" and path.startswith(f"repos/{REPO}/pulls/7/files"):
            return [{"filename": p, "status": s} for p, s in self.status.items()] if "page=1" in path else []
        if method == "GET" and path.startswith(f"repos/{REPO}/contents/"):
            p = path.split("/contents/")[1].split("?")[0]
            return self.contents[p].encode() if raw else {}
        if method == "GET" and path == f"repos/{REPO}/git/commits/{HEAD}":
            return {"tree": {"sha": "t" * 40}}
        self.writes.append((method, path, body))
        if path.endswith("/git/blobs"):
            sha = f"{len(self.blobs):040x}"
            self.blobs[sha] = base64.b64decode(body["content"]).decode()  # type: ignore[index]
            return {"sha": sha}
        if path.endswith("/git/trees"):
            return {"sha": "e" * 40}
        if path.endswith("/git/commits"):
            return {"sha": "c" * 40}
        return {}


def created(n: int) -> str:
    """what the tagger writes for a theorem that has no docstring: a docstring that holds only the tag"""
    return sct.lean(n).replace(f"theorem lemma_{n}", f"/--\n{NOVEL}\n-/\ntheorem lemma_{n}")


def tagged_pair() -> dict[str, str]:
    return {P1: created(1), P2: created(2)}


class Push(unittest.TestCase):
    def go(self, gh: Fake, files: dict[str, str] | None = None, **kw):
        return ap.push(gh, REPO, 7, HEAD, files if files is not None else tagged_pair(), {**BOT, **kw.pop("env", {})}, **kw)

    def refused(self, gh: Fake, why: str, files: dict[str, str] | None = None, **kw):
        with self.assertRaises(ap.Refused) as cm:
            self.go(gh, files, **kw)
        self.assertIn(why, str(cm.exception))
        self.assertEqual(gh.writes, [], "nothing is written when a check fails")

    def test_the_tags_become_one_commit_on_the_prs_branch(self):
        gh = Fake()
        out = self.go(gh)
        self.assertIn("tagged 2 module(s)", out)
        methods = [(m, p.split("/", 3)[-1]) for m, p, _ in gh.writes]
        self.assertEqual(
            methods,
            [
                ("POST", "git/blobs"),
                ("POST", "git/blobs"),
                ("POST", "git/trees"),
                ("POST", "git/commits"),
                ("PATCH", "git/refs/heads/supervisor/erdos-396"),
            ],
        )
        tree = next(b for m, p, b in gh.writes if p.endswith("/git/trees"))
        self.assertEqual(tree["base_tree"], "t" * 40)  # type: ignore[index]
        self.assertEqual(sorted(e["path"] for e in tree["tree"]), [P1, P2])  # type: ignore[index]
        self.assertEqual(sorted(gh.blobs.values()), sorted(tagged_pair().values()))
        commit = next(b for m, p, b in gh.writes if p.endswith("/git/commits"))
        self.assertEqual(commit["parents"], [HEAD])  # type: ignore[index]
        self.assertIn("Signed-off-by: tengoku-bot <tengoku-bot@users.noreply.github.com>", commit["message"])  # type: ignore[index]
        self.assertEqual(commit["author"], commit["committer"])  # type: ignore[index]
        ref = next(b for m, p, b in gh.writes if m == "PATCH")
        self.assertEqual(ref, {"sha": "c" * 40, "force": False})

    def test_a_dry_run_writes_nothing(self):
        gh = Fake()
        self.assertIn("dry run: 2 module(s)", self.go(gh, dry_run=True))
        self.assertEqual(gh.writes, [])

    def test_the_head_must_be_the_commit_that_was_tagged(self):
        self.refused(Fake(head={"sha": "b" * 40, "ref": "x", "repo": {"full_name": REPO}}), "moved on")

    def test_only_a_branch_of_this_repository(self):
        self.refused(Fake(head={"sha": HEAD, "ref": "x", "repo": {"full_name": "someone/tengoku"}}), "not in this repository")

    def test_only_the_lanes_apps(self):
        self.refused(Fake(user={"login": "mallory"}), "not one of the lane's Apps")
        gh = Fake(user={"login": "renamed[bot]"})
        self.assertIn("tagged", self.go(gh, env={"AUTOTAG_ACTORS": "renamed[bot]"}))

    def test_an_open_pr_and_a_branch_that_is_not_main(self):
        self.refused(Fake(state="closed"), "not open")
        self.refused(Fake(head={"sha": HEAD, "ref": "main", "repo": {"full_name": REPO}}), "not one the autotag writes to")
        self.refused(Fake(head={"sha": HEAD, "ref": "--force", "repo": {"full_name": REPO}}), "not one the autotag writes to")

    def test_only_modules_the_pr_adds(self):
        gh = Fake()
        gh.status[P1] = "modified"
        self.refused(gh, "not a module this PR adds")
        gh = Fake()
        self.refused(gh, "not a module this PR adds", {**tagged_pair(), "Tengoku/Seed/Other.lean": "x"})

    def test_what_changed_must_be_tags_and_nothing_else(self):
        sneaky = tagged_pair()
        sneaky[P1] = sneaky[P1].replace("omega", "simp [Nat.add_comm]")
        self.refused(Fake(), "changes more than tags", sneaky)
        sneaky = tagged_pair()
        sneaky[P2] = sneaky[P2] + "\n-- a comment\n"
        self.refused(Fake(), "changes more than tags", sneaky)

    def test_an_untouched_module_is_not_a_tagged_one(self):
        self.refused(Fake(), "nothing was tagged", {P1: sct.lean(1), P2: tagged_lean(2)})

    def test_a_module_that_declares_no_theorem_comes_out_as_it_went_in_and_is_not_written(self):
        """azurite part 1: ExactDiv.lean has only definitions, the tagger leaves it alone, and the artifact carries it unchanged"""
        defs = sct.lean(2, "def two : Nat := 2\n")
        gh = Fake({P1: sct.lean(1), P2: defs})
        out = self.go(gh, {P1: created(1), P2: defs})
        self.assertIn("tagged 1 module(s)", out)
        tree = next(b for m, p, b in gh.writes if p.endswith("/git/trees"))
        self.assertEqual([e["path"] for e in tree["tree"]], [P1])  # type: ignore[index]

    def test_a_pr_whose_modules_all_need_no_tag_writes_nothing(self):
        defs = {P1: sct.lean(1, "def one : Nat := 1\n"), P2: sct.lean(2, "def two : Nat := 2\n")}
        gh = Fake(defs)
        self.assertIn("nothing to tag", self.go(gh, dict(defs)))
        self.assertEqual(gh.writes, [])

    def test_a_docstring_with_words_is_not_something_the_tagger_adds(self):
        # the tag is right, but the docstring the artifact carries has words the PR did not have: that is a change a compiler's documentation reads
        self.refused(Fake(), "changes more than tags", {P1: tagged_lean(1), P2: created(2)})

    def test_the_tags_must_be_well_formed_and_from_the_modules_place(self):
        files = {P1: sct.lean(1).replace("theorem", f"/--\n{NOVEL.replace('from=novel', 'from=seed')}\n-/\ntheorem")}
        self.refused(Fake({P1: sct.lean(1)}), "from=seed but the module is novel content", files)
        self.assertNotEqual(SEED, NOVEL)

    def test_a_module_that_declares_theorems_must_come_out_tagged(self):
        # an artifact that only reformats a comment away from the PR's text is no tagging
        plain = sct.lean(1, "-- a note\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n")
        self.refused(Fake({P1: plain}), "changes more than tags", {P1: plain.replace("-- a note", "-- another note")})

    def test_only_the_api_calls_the_script_makes(self):
        for method, path in (
            ("DELETE", "repos/a/b/pulls/1"),
            ("GET", "user"),
            ("GET", "repos/a/b/../../c"),
            ("GET", "orgs/x"),
            ("POST", "repos/a/b/git/blobs\nx"),
        ):
            with self.assertRaises(ap.Refused, msg=f"{method} {path}"):
                ap.gh_api(method, path)

    def test_paths_the_autotag_does_not_write(self):
        d = Path(tempfile.mkdtemp())
        for bad in (
            "../x.lean",
            "Tengoku/All.lean",
            "Tengoku/Studied.lean",
            "Tengoku/FxLib.lean",
            "scripts/x.lean",
            "/etc/x.lean",
            "Tengoku/a\\b.lean",
        ):
            self.assertFalse(ap.safe_path(bad), bad)
        self.assertTrue(ap.safe_path(P1))
        self.assertTrue(ap.safe_path("Tengoku/Tao/«1102.4662»/A.lean"))
        (d / "Tengoku" / "Studied").mkdir(parents=True)
        (d / "Tengoku" / "Studied" / "S.lean").write_text("x")
        (d / "notes.lean").write_text("x")
        with self.assertRaises(ap.Refused):
            ap.artifact_files(d)

    def test_a_symlink_in_the_artifact_is_refused(self):
        d = Path(tempfile.mkdtemp())
        outside = Path(tempfile.mkdtemp()) / "secret.lean"
        outside.write_text("secret")
        (d / "Tengoku").mkdir()
        (d / "Tengoku" / "A.lean").symlink_to(outside)
        with self.assertRaises(ap.Refused):
            ap.artifact_files(d)

    def test_too_many_modules(self):
        files = {f"Tengoku/Studied/X/S{i:012x}.lean": "x" for i in range(ap.MAX_MODULES + 1)}
        self.refused(Fake(), "cap", files)

    def test_an_artifact_that_holds_nothing(self):
        self.refused(Fake(), "no module", {})

    def test_the_artifact_is_read_from_a_directory(self):
        d = Path(tempfile.mkdtemp())
        for p, t in tagged_pair().items():
            (d / p).parent.mkdir(parents=True, exist_ok=True)
            (d / p).write_text(t, encoding="utf-8")
        self.assertEqual(ap.artifact_files(d), tagged_pair())


class Retries(unittest.TestCase):
    """one GitHub server error among hundreds of reads must not refuse a whole intake PR; a write is never repeated"""

    def run_with(self, results, method="GET", path=f"repos/{REPO}/pulls/7"):
        calls = []

        def fake(cmd, **kw):
            calls.append(cmd)
            rc, out, err = results[min(len(calls), len(results)) - 1]
            return subprocess.CompletedProcess(cmd, rc, out, err)

        with mock.patch.object(ap.subprocess, "run", fake), mock.patch.object(ap.time, "sleep", lambda s: None):
            try:
                got = ap.gh_api(method, path)
            except ap.Refused as e:
                got = str(e)
        return got, len(calls)

    def test_a_read_that_gets_a_server_error_is_repeated(self):
        got, n = self.run_with([(1, "", "gh: Internal Server Error (HTTP 500)"), (1, "", "gh: HTTP 504"), (0, '{"ok": 1}', "")])
        self.assertEqual((got, n), ({"ok": 1}, 3))

    def test_a_read_that_keeps_failing_is_refused_after_four_tries(self):
        got, n = self.run_with([(1, "", "gh: HTTP 502")])
        self.assertEqual(n, 4)
        self.assertIn("HTTP 502", got)

    def test_a_missing_file_is_not_retried(self):
        got, n = self.run_with([(1, "", "gh: Not Found (HTTP 404)")])
        self.assertEqual(n, 1)

    def test_a_write_that_is_not_content_addressed_is_never_repeated(self):
        for method, path in (
            ("PATCH", f"repos/{REPO}/git/refs/heads/x"),
            ("POST", f"repos/{REPO}/git/commits"),
            ("POST", f"repos/{REPO}/issues/7/comments"),
        ):
            got, n = self.run_with([(1, "", "gh: HTTP 500")], method=method, path=path)
            self.assertEqual(n, 1, f"{method} {path}")

    def test_creating_a_blob_or_a_tree_is_repeated_after_a_transient_error(self):
        # npcompleteness-lean4 #709, 4 Nov 2026: one `POST git/blobs: unexpected end of JSON input` (an empty answer) refused the whole push
        for path in (f"repos/{REPO}/git/blobs", f"repos/{REPO}/git/trees"):
            got, n = self.run_with(
                [(1, "", "gh api POST: unexpected end of JSON input"), (1, "", "gh: HTTP 502"), (0, '{"sha": "abc"}', "")],
                method="POST",
                path=path,
            )
            self.assertEqual((got, n), ({"sha": "abc"}, 3), path)

    def test_a_blob_that_keeps_failing_is_refused_after_four_tries(self):
        got, n = self.run_with([(1, "", "gh: HTTP 500")], method="POST", path=f"repos/{REPO}/git/blobs")
        self.assertEqual(n, 4)
        self.assertIn("HTTP 500", got)


class Plan(unittest.TestCase):
    base = sct.Studied.base
    bundle = sct.Studied.bundle
    APP = {"AUTOTAG_ACTORS": "tengoku-supervisor[bot]"}

    def run_plan(self, r: Repo, author: str = "tengoku-supervisor[bot]", env: dict | None = None) -> dict:
        import os
        import subprocess

        p = subprocess.run(
            [
                sys.executable,
                str(HERE.parent / "autotag.py"),
                "plan",
                r.git("rev-parse", "main").strip(),
                r.git("rev-parse", "pr").strip(),
                author,
            ],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), **(env or {})},
        )
        self.assertEqual(p.returncode, 0, p.stderr)
        return json.loads(p.stdout.strip().splitlines()[-1])

    def test_the_marker_of_a_factory_bundle_is_not_a_module_to_tag(self):
        """Tengoku/<Library>/Deps.lean only marks the library; nothing imports it, so the build has no olean and the tagger died on it
        (azurite part 1, 2 Nov 2026)"""
        import os
        import subprocess

        r = Repo()
        r.write("Tengoku/FxLib/Deps.lean", "-- FxLib: a factory bundle. This file only marks the library for Tengoku/All.lean.\n")
        r.write("Tengoku/FxLib/Fx/A.lean", "import Tengoku\n\ntheorem t0 : 1 + 1 = 2 := rfl\n")
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.A\n")
        r.commit("a library arrives")
        code = "import sys, born_tagged as b; print(b.lane_modules(sys.argv[1], sys.argv[2], 'intake'))"
        p = subprocess.run(
            [sys.executable, "-c", code, r.git("rev-parse", "main").strip(), r.git("rev-parse", "pr").strip()],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "PYTHONPATH": str(HERE.parent)},
        )
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(p.stdout.strip(), "['Tengoku/FxLib/Fx/A.lean']")
        # a theorem placed in the marker is not hidden by its name
        r.write("Tengoku/FxLib/Deps.lean", "-- marker\ntheorem sneaked : 1 + 1 = 2 := rfl\n")
        r.commit("code in the marker")
        p = subprocess.run(
            [sys.executable, "-c", code, r.git("rev-parse", "main").strip(), r.git("rev-parse", "pr").strip()],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "PYTHONPATH": str(HERE.parent)},
        )
        self.assertEqual(p.stdout.strip(), "['Tengoku/FxLib/Deps.lean', 'Tengoku/FxLib/Fx/A.lean']")

    def test_a_studied_pr_from_the_app_is_planned(self):
        r = self.base()
        self.bundle(r)
        out = self.run_plan(r)
        self.assertEqual(out["lane"], "studied")
        self.assertEqual(out["modules"], [sct.mod_of(1), sct.mod_of(2)])
        self.assertEqual(out["refused"], "")
        self.assertFalse(out["tagged"])

    def test_a_pr_that_already_carries_its_tags_has_nothing_to_add(self):
        r = self.base()
        self.bundle(r)
        for n in (1, 2):
            r.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(n)[:12]}.lean", created(n))
        r.commit("tags")
        self.assertTrue(self.run_plan(r)["tagged"])

    def test_nothing_is_built_for_anyone_but_the_lanes_apps(self):
        r = self.base()
        self.bundle(r)
        self.assertEqual(self.run_plan(r, "mallory")["lane"], "")
        self.assertEqual(self.run_plan(r, "tengoku-supervisor[bot]", {"AUTOTAG_ACTORS": "renamed[bot]"})["lane"], "")

    def test_content_that_fails_its_gate_is_not_built(self):
        r = self.base()
        self.bundle(r)
        r.write(f"Tengoku/Studied/{sct.NS}/S{sct.entry_id(1)[:12]}.lean", sct.lean(1).replace("omega", "native_decide"))
        r.commit("a module the content rules refuse")
        out = self.run_plan(r)
        self.assertEqual(out["modules"], [])
        self.assertIn("gate does not pass", out["refused"])

    def test_the_intake_lane_is_left_alone_until_the_variable_switches_it_on(self):
        from test_born_tagged import Intake

        r = Intake().repo(False)
        out = self.run_plan(r, "tengoku-intake[bot]")
        self.assertEqual((out["lane"], out["modules"]), ("", []))
        on = self.run_plan(r, "tengoku-intake[bot]", {"TENGOKU_ISNAD_REQUIRED": "1"})
        self.assertEqual(on["lane"], "intake")
        self.assertIn(
            "intake gate does not pass", on["refused"]
        )  # this fixture is no real intake bundle; the point is that the plan looked at it

    def test_the_arguments_are_a_commit_a_commit_and_a_login(self):
        import subprocess

        for args in (
            ["plan", "main", "pr", "ada"],
            ["plan", "a" * 40, "b" * 40, "x y"],
            ["plan", "a" * 40, "b" * 40],
            ["tag", "a" * 40, "b" * 40, "ada"],
        ):
            p = subprocess.run([sys.executable, str(HERE.parent / "autotag.py"), *args], capture_output=True, text=True)
            self.assertEqual(p.returncode, 2, args)
            self.assertIn("usage", p.stderr)

    def test_other_prs_have_no_plan(self):
        r = Repo()
        r.write("scripts/x.py", "print(5)\n")
        r.commit("tooling")
        self.assertEqual(self.run_plan(r)["lane"], "")


class Workflows(unittest.TestCase):
    """What CodeRabbit and Gitar found in the two workflows of tengoku#649 (the half that holds the bot's token is main's code, so these are the only rehearsal it gets off main)."""

    @staticmethod
    def load(name):
        import yaml

        return yaml.safe_load((TREE / ".github" / "workflows" / name).read_text(encoding="utf-8"))

    def test_a_build_is_per_pr_and_a_push_per_branch_so_one_pr_never_cancels_anothers(self):
        build, push = self.load("autotag-build.yml"), self.load("autotag-push.yml")
        self.assertIn("github.event.pull_request.number", build["concurrency"]["group"])
        self.assertIn("github.event.workflow_run.head_branch", push["concurrency"]["group"])
        self.assertFalse(push["concurrency"]["cancel-in-progress"], "a push in flight is never cancelled")

    def test_the_push_runs_only_for_this_repositorys_own_runs(self):
        cond = self.load("autotag-push.yml")["jobs"]["push"]["if"]
        self.assertIn("github.event.workflow_run.head_repository.full_name == github.repository", cond)

    def test_the_artifact_is_data_its_pr_and_head_must_be_the_runs_own(self):
        job = self.load("autotag-push.yml")["jobs"]["push"]
        step = next(x for x in job["steps"] if x.get("name") == "The tags, onto the PR's branch")
        self.assertEqual(step["env"]["RUN_HEAD"], "${{ github.event.workflow_run.head_sha }}")
        self.assertIn("workflow_run.pull_requests", step["env"]["RUN_PRS"])
        self.assertIn('"$head" != "$RUN_HEAD"', step["run"])
        self.assertLess(
            step["run"].index('"$head" != "$RUN_HEAD"'), step["run"].index("autotag_push.py"), "checked before anything is pushed"
        )

    def run_the_fetch_of_mains_scripts(self, fails_first):
        """The step's own script, in bash as the runner runs it (-e, pipefail), with a `gh` that fails `fails_first` times with a server error and then answers, and a `sleep` that does not wait: (exit code, files written, `gh` calls)."""
        import os
        import subprocess
        import tempfile

        steps = self.load("autotag-push.yml")["jobs"]["push"]["steps"]
        script = next(x for x in steps if x.get("name") == "Main's scripts")["run"]
        with tempfile.TemporaryDirectory() as d:
            shim = Path(d) / "shim"
            shim.mkdir()
            (shim / "gh").write_text(
                '#!/usr/bin/env bash\nn=$(cat "$COUNT" 2>/dev/null || echo 0); echo $((n+1)) > "$COUNT"\n'
                'if [ "$n" -lt "$FAILS" ]; then echo "gh: Internal Server Error (HTTP 500)" >&2; exit 1; fi\necho "# a file"\n',
                encoding="utf-8",
            )
            (shim / "sleep").write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
            for f in shim.iterdir():
                f.chmod(0o755)
            work = Path(d) / "work"
            work.mkdir()
            env = {
                **os.environ,
                "PATH": f"{shim}{os.pathsep}{os.environ['PATH']}",
                "COUNT": str(Path(d) / "count"),
                "FAILS": str(fails_first),
            }
            env["GITHUB_REPOSITORY"] = "competemath/tengoku"
            r = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c", script], cwd=work, env=env, capture_output=True, text=True, check=False
            )
            wrote = sorted(str(p.relative_to(work)) for p in work.rglob("*") if p.is_file() and p.stat().st_size)
            calls = int((Path(d) / "count").read_text().strip())
            return r.returncode, wrote, calls

    def test_the_fetch_of_mains_scripts_goes_on_after_two_server_errors(self):
        code, wrote, calls = self.run_the_fetch_of_mains_scripts(2)
        self.assertEqual(code, 0)
        self.assertIn("scripts/isnad.py", wrote)
        self.assertIn("scripts/ci/tag_check.py", wrote)
        self.assertEqual(calls, 2 + 11, "the first read took three tries, the other ten one each")

    def test_the_fetch_of_mains_scripts_fails_after_four_server_errors_in_a_row(self):
        code, _, calls = self.run_the_fetch_of_mains_scripts(100)
        self.assertNotEqual(code, 0)
        self.assertEqual(calls, 4, "four tries at the first file, then the step stops")

    def test_a_run_that_uploaded_nothing_is_skipped_not_failed(self):
        steps = self.load("autotag-push.yml")["jobs"]["push"]["steps"]
        has = next(x for x in steps if x.get("id") == "has")
        self.assertIn("artifacts", has["run"])
        for x in steps:
            if "download-artifact" in x.get("uses", "") or x.get("name") == "The tags, onto the PR's branch":
                self.assertEqual(x.get("if"), "steps.has.outputs.any == 'true'", x.get("name") or x["uses"])

    def test_the_tag_lane_builds_the_prs_modules_and_never_the_whole_tree(self):
        # `lake build Tengoku.All` replayed the whole tree (28,650 jobs, 31 minutes) for azurite part 3's 214 modules, which alone take 7 (3 Nov 2026)
        job = self.load("autotag-build.yml")["jobs"]["tag"]
        for x in job["steps"]:
            self.assertNotIn("Tengoku.All", x.get("run", ""), x.get("name"))
        first = next(x for x in job["steps"] if x.get("name") == "The PR's modules on top of it")
        self.assertIn('json.load(open("plan.json"))["modules"]', first["run"])
        self.assertIn('lake build "${mods[@]}"', first["run"])

    def test_no_token_is_in_the_environment_of_the_step_that_builds_the_prs_modules(self):
        doc = self.load("autotag-build.yml")
        job = doc["jobs"]["tag"]
        self.assertNotIn("GH_TOKEN", doc.get("env", {}))
        self.assertNotIn("GH_TOKEN", job.get("env", {}))
        builds = [x for x in job["steps"] if "lake build" in x.get("run", "")]
        self.assertGreaterEqual(len(builds), 2)
        for x in builds:
            self.assertNotIn("GH_TOKEN", x.get("env", {}), x.get("name"))
            self.assertNotIn("cache.sh", x["run"], "the cache fetch (which needs the token) is a step of its own")


if __name__ == "__main__":
    unittest.main()
