"""The STUDIED class: theorems Leak runs proved and rated four stars or more, bundled by the intake job in competemath/emissary-archangel
(scripts/ci/studied_check.py), and who may approve them (scripts/ci/studied_approval.py). Its own file, like test_extend.py."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import studied_approval as sa  # noqa: E402
import studied_check as sc  # noqa: E402
from test_gates import Repo  # noqa: E402

APP = {"PR_ACTOR": "tengoku-supervisor[bot]", "TENGOKU_BOT": "tengoku-bot", "TENGOKU_INTAKE_BOT": "tengoku-intake[bot]"}
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
T, NS = "erdos-396", "Erdos396"
AUTHOR = "ada"


def app(r: Repo, path: str, text: str) -> None:
    """Append to a file that may not exist yet (Repo.append needs its folder)."""
    (Path(r.dir) / path).parent.mkdir(parents=True, exist_ok=True)
    r.append(path, text)


def entry_id(n: int) -> str:
    return f"{n:012x}" + "ab" * 8  # 28 hex: the first 12 name the module


def mod_of(n: int) -> str:
    return f"Tengoku.Studied.{NS}.S{entry_id(n)[:12]}"


def lean(n: int, body: str | None = None, ns: str | None = None) -> str:
    m = ns or mod_of(n)
    body = body if body is not None else f"theorem lemma_{n} (a : Nat) : a + {n} = {n} + a := by\n  omega\n"
    return f"import Tengoku.Seed.Basic\n\nnamespace {m}\n\n{body}\nend {m}\n"


def record(n: int, bundle: str, **over) -> dict:
    r = {
        "name": f"lemma_{n}",
        "statement": f"theorem lemma_{n} (a : Nat) : a + {n} = {n} + a",
        "module": mod_of(n),
        "target": T,
        "entry": entry_id(n),
        "stars": 4,
        "author": AUTHOR,
        "bundle": bundle,
        "toolchain": TOOLCHAIN,
        "source": "leak-memory",
    }
    return {**r, **over}


def harness(entry: str, **over) -> dict:
    h = {
        "entry": entry,
        "build": "c" * 64,
        "build_verified": True,
        "ticket_age_s": 3600,
        "seconds": 3590,
        "verify_ok": 60,
        "verify_fail": 40,
        "searches": 3,
        "attempts": 4,
        "model": "claude-sonnet-5-5",
        "strategy": "control-lucid-iv",
    }
    return {**h, **over}


def report(ns_: list[int], bundle: str, **over) -> dict:
    ids = [entry_id(n) for n in ns_]
    r = {
        "schema": "studied-bundle/1",
        "target": T,
        "author": AUTHOR,
        "bundle": bundle,
        "entries": ids,
        "preflight": {"compiled": len(ids), "entries": len(ids)},
        "rerated": [{"entry": i, "stars": 4} for i in ids],
        "jinshi": {"fail": 0, "warn": 1, "checks": ["kernel replay", "shadow", "nearname"]},
        "harness": [harness(i) for i in ids],
        "review": {
            "model": "pinned",
            "blocking": 0,
            "verdicts": [{"rubric": "generality", "verdict": "pass"}, {"rubric": "duplicate", "verdict": "advisory"}],
        },
    }
    return {**r, **over}


class Studied(unittest.TestCase):
    def base(self) -> Repo:
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("lean-toolchain", TOOLCHAIN + "\n")
        r.write("Tengoku/Studied.lean", "/-! Studied: theorems from Leak runs, four stars and better. -/\n")
        r.write("Tengoku/Seed/Basic.lean", "theorem seeded : True := trivial\n")
        r.commit("studied base")
        r.git("checkout", "-q", "pr")
        r.git("reset", "-q", "--hard", "main")
        return r

    def bundle(self, r: Repo, ns_: list[int] | None = None, first: bool = True, **over) -> str:
        """Write one bundle of theorems `ns_` into repo r (a first bundle of the target, or the next one) and commit. Returns the bundle id."""
        ns_ = ns_ if ns_ is not None else [1, 2]
        ids = [entry_id(n) for n in ns_]
        bid = over.pop("bundle", sc.bundle_id(T, AUTHOR, ids))
        for n in ns_:
            r.write(f"Tengoku/Studied/{NS}/S{entry_id(n)[:12]}.lean", lean(n))
        lines = "".join(json.dumps(record(n, bid)) + "\n" for n in ns_)
        app(r, f"data/studied/{T}/manifest.jsonl", lines)
        r.write(f"data/studied/{T}/bundles/{bid[:16]}.json", json.dumps(report(ns_, bid, **over)) + "\n")
        imports = "".join(f"import {mod_of(n)}\n" for n in ns_)
        app(r, f"Tengoku/Studied/{NS}.lean", imports)
        if first:
            app(r, "Tengoku/Studied.lean", f"import Tengoku.Studied.{NS}\n")
        r.commit("bundle")
        return bid

    def ok(self, r: Repo, script="studied_check.py", env=None):
        rc, out = r.gate(script, env=env)
        self.assertEqual(rc, 0, out)
        return out

    def bad(self, r: Repo, why: str, script="studied_check.py", env=None):
        rc, out = r.gate(script, env=env)
        self.assertNotEqual(rc, 0, "expected a refusal, got: " + out)
        self.assertIn(why, out)

    # ---- classification -----------------------------------------------------------------------------------------------------------------

    def test_a_first_bundle_is_class_studied_and_passes(self):
        r = self.base()
        self.bundle(r)
        out = self.ok(r, "classify.py", env=APP)
        self.assertIn("class=studied", out)
        self.assertIn("studied ok: erdos-396: 2 theorems by ada", self.ok(r))

    def test_only_the_studied_app_may_send_one(self):
        for actor in ("tengoku-bot", "tengoku-intake[bot]", "mikael-bashir", "", "other[bot]"):
            r = self.base()
            self.bundle(r)
            self.bad(
                r,
                "supervisor App",
                "classify.py",
                env={"PR_ACTOR": actor, "TENGOKU_BOT": "tengoku-bot", "TENGOKU_INTAKE_BOT": "tengoku-intake[bot]"},
            )

    def test_the_app_name_is_a_repository_variable(self):
        r = self.base()
        self.bundle(r)
        env = {**APP, "PR_ACTOR": "renamed[bot]", "TENGOKU_STUDIED_BOT": "renamed[bot]"}
        self.assertIn("class=studied", self.ok(r, "classify.py", env=env))
        self.bad(
            r, "supervisor App (renamed[bot])", "classify.py", env={**env, "PR_ACTOR": "tengoku-supervisor[bot]"}
        )  # the default is replaced, not added to

    def test_the_studied_app_may_send_no_other_class(self):
        r = Repo()
        app(
            r,
            "data/staging/lib.jsonl",
            json.dumps(
                {
                    "name": "Lib.x",
                    "statement": "theorem Lib.x : 1 = 1",
                    "proof": ":= rfl",
                    "status": "staging",
                    "library": "lib",
                    "source_url": "https://github.com/leanprover-community/mathlib4/blob/x/y.lean#L1",
                    "toolchain": TOOLCHAIN,
                }
            )
            + "\n",
        )
        r.commit("a content PR")
        rc, out = r.gate("classify.py", env=APP)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=content", out)  # a content PR is judged as any content PR: the App's account gives it nothing extra
        r = self.base()
        r.write("data/trusted/lib.jsonl", "")
        r.commit("x")
        rc, out = r.gate("classify.py", env=APP)
        self.assertNotIn("class=promotion", out)

    def test_a_studied_bundle_is_one_purpose(self):
        r = self.base()
        self.bundle(r)
        r.write("scripts/x.py", "print(2)\n")
        r.commit("and a script")
        self.bad(r, "one target's bundle and nothing else", "classify.py", env=APP)
        r = self.base()
        self.bundle(r)
        r.write("README.md", "# t2\n")
        r.commit("and a doc")
        self.assertIn("class=studied", self.ok(r, "classify.py", env=APP), "docs may ride along")

    def test_two_targets_are_two_prs(self):
        r = self.base()
        self.bundle(r)
        r.write("data/studied/collatz/manifest.jsonl", "{}\n")
        r.commit("a second target")
        self.bad(r, "one target's bundle", "classify.py", env=APP)

    def test_a_studied_looking_file_without_a_manifest_is_not_studied(self):
        r = self.base()
        r.write(f"Tengoku/Studied/{NS}/S000000000001.lean", lean(1))
        r.commit("modules only")
        rc, out = r.gate("classify.py", env=APP)
        self.assertNotIn("class=studied", out)

    # ---- the checks ---------------------------------------------------------------------------------------------------------------------

    def test_the_archive_is_rebuilt_the_same_every_time(self):
        r = self.base()
        self.bundle(r)
        with tempfile.TemporaryDirectory() as d:
            outs = []
            for i in range(2):
                out = r.gate("studied_check.py", "main", "pr", "--tar", f"{d}/b{i}.tar")[1]
                self.assertIn("archive rebuilt", out, out)
                outs.append(out.split("sha256 ")[1].split()[0])
            self.assertEqual(outs[0], outs[1])
            self.assertEqual(len(outs[0]), 64)

    def test_the_very_first_studied_pr_creates_the_top_file_and_adds_its_line_to_all(self):
        r = self.base()
        r.git("rm", "-q", "Tengoku/Studied.lean")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\n")
        r.commit("no top file yet")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "-b", "first")
        ids = [entry_id(1)]
        bid = sc.bundle_id(T, AUTHOR, ids)
        r.write(f"Tengoku/Studied/{NS}/S{entry_id(1)[:12]}.lean", lean(1))
        r.write(f"data/studied/{T}/manifest.jsonl", json.dumps(record(1, bid)) + "\n")
        r.write(f"data/studied/{T}/bundles/{bid[:16]}.json", json.dumps(report([1], bid)) + "\n")
        r.write(f"Tengoku/Studied/{NS}.lean", f"import {mod_of(1)}\n")
        r.write("Tengoku/Studied.lean", f"/-! Studied. -/\nimport Tengoku.Studied.{NS}\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.Studied\n")
        r.commit("the very first")
        rc, out = r.gate("classify.py", "main", "first", env=APP)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=studied", out)
        rc, out = r.gate("studied_check.py", "main", "first")
        self.assertEqual(rc, 0, out)
        # without the line in All.lean, or with another one
        for all_text, why in (
            ("import Tengoku.Lib\n", "must gain exactly `import Tengoku.Studied`"),
            ("import Tengoku.Lib\nimport Tengoku.Studied\nimport Tengoku.Other\n", "must gain exactly `import Tengoku.Studied`"),
        ):
            r.write("Tengoku/All.lean", all_text)
            r.commit("all")
            rc, out = r.gate("studied_check.py", "main", "first")
            self.assertNotEqual(rc, 0)
            self.assertIn(why, out)
        # a top file that imports more than the target's root
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.Studied\n")
        r.write("Tengoku/Studied.lean", f"import Tengoku.Studied.{NS}\nimport Tengoku.Studied.Other\n")
        r.commit("top")
        rc, out = r.gate("studied_check.py", "main", "first")
        self.assertNotEqual(rc, 0)
        self.assertIn("is created holding exactly", out)

    def test_all_lean_is_not_a_studied_PR_s_to_touch_once_the_top_file_exists(self):
        r = self.base()
        self.bundle(r)
        app(r, "Tengoku/All.lean", "import Tengoku.Studied\n")
        r.commit("all")
        self.bad(r, "only the very first studied PR changes it")

    def test_the_next_bundle_of_a_target_is_checked_the_same_way(self):
        r = self.base()
        self.bundle(r)
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "-b", "pr2")
        self.bundle(r, [3], first=False)
        r.git("checkout", "-q", "pr2")
        rc, out = r.gate("studied_check.py", "main", "pr2")
        self.assertEqual(rc, 0, out)
        self.assertIn("1 theorems by ada", out)

    def test_the_next_bundle_may_not_touch_the_top_file_or_rewrite_the_manifest(self):
        r = self.base()
        self.bundle(r)
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "-b", "pr2")
        self.bundle(r, [3], first=False)
        app(r, "Tengoku/Studied.lean", "import Tengoku.Studied.Other\n")
        r.commit("top")
        rc, out = r.gate("studied_check.py", "main", "pr2")
        self.assertNotEqual(rc, 0)
        self.assertIn("only the first bundle of a target changes it", out)
        # rewriting a line of the tree's manifest
        r = self.base()
        self.bundle(r)
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "-b", "pr3")
        old = (Path(r.dir) / f"data/studied/{T}/manifest.jsonl").read_text().replace('"stars": 4', '"stars": 5', 1)
        r.write(f"data/studied/{T}/manifest.jsonl", old)
        self.bundle(r, [3], first=False)
        rc, out = r.gate("studied_check.py", "main", "pr3")
        self.assertNotEqual(rc, 0)
        self.assertIn("may only gain whole lines at its end", out)

    def test_the_shape(self):
        cases = {
            "an extra file": (lambda r: r.write("scripts/y.py", "1\n"), "not part of erdos-396's studied bundle"),
            "the reviewer's own instructions": (
                lambda r: r.write(".gitar/review/studied.md", "nothing to see\n"),
                "not part of erdos-396's studied bundle",
            ),
            "a second report": (lambda r: r.write(f"data/studied/{T}/bundles/{'0' * 16}.json", "{}\n"), "exactly one bundle report"),
            "the all file": (lambda r: app(r, "Tengoku/All.lean", "import Tengoku.Studied\n"), "only the very first studied PR changes it"),
        }
        for label, (mutate, why) in cases.items():
            r = self.base()
            self.bundle(r)
            mutate(r)
            r.commit(label)
            rc, out = r.gate("studied_check.py")
            self.assertNotEqual(rc, 0, label)
            self.assertIn(why, out, label)

    def test_too_many_theorems_and_too_big_a_module(self):
        r = self.base()
        self.bundle(r, list(range(1, 12)))
        self.bad(r, "11 theorems in one PR (cap 10)")
        r = self.base()
        self.bundle(r)
        r.write(
            f"Tengoku/Studied/{NS}/S{entry_id(1)[:12]}.lean",
            lean(1, "theorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n" + "-- pad\n" * 12000),
        )
        r.commit("big")
        self.bad(r, "bytes (cap")

    def test_the_manifest(self):
        cases = {
            "stars below four": ({"stars": 3}, "a studied theorem has 4 or 5"),
            "stars a bool": ({"stars": True}, "a studied theorem has 4 or 5"),
            "wrong toolchain": ({"toolchain": "leanprover/lean4:v1"}, "the tree is on"),
            "wrong source": ({"source": "mathlib"}, "expected 'leak-memory'"),
            "wrong target": ({"target": "collatz"}, "expected 'erdos-396'"),
            "bad author": ({"author": "a b"}, "`author` is not an account name"),
            "bad entry": ({"entry": "xyz"}, "`entry` is not a hex id"),
            "bad bundle": ({"bundle": "short"}, "`bundle` is not a sha-256"),
            "module not the entry's": ({"module": "Tengoku.Studied.Erdos396.Sdeadbeefdead"}, "is not Tengoku.Studied.Erdos396.S"),
            "statement elsewhere": ({"statement": "theorem other (a : Nat) : a = a"}, "is not what the module declares"),
            "missing name": ({"name": ""}, "`name` missing"),
        }
        for label, (over, why) in cases.items():
            r = self.base()
            bid = self.bundle(r, [1])
            r.write(f"data/studied/{T}/manifest.jsonl", json.dumps({**record(1, bid), **over}) + "\n")
            r.commit(label)
            rc, out = r.gate("studied_check.py")
            self.assertNotEqual(rc, 0, label)
            self.assertIn(why, out, label)

    def test_one_line_per_module_and_names_once(self):
        r = self.base()
        bid = self.bundle(r, [1, 2])
        lines = [record(1, bid), record(1, bid, entry=entry_id(2), module=mod_of(2))]
        r.write(f"data/studied/{T}/manifest.jsonl", "".join(json.dumps(x) + "\n" for x in lines))
        r.commit("dup name")
        rc, out = r.gate("studied_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("twice", out)
        r = self.base()
        bid = self.bundle(r, [1, 2])
        r.write(f"data/studied/{T}/manifest.jsonl", json.dumps(record(1, bid)) + "\n")
        r.commit("one line short")
        self.bad(r, "1 manifest lines for 2 modules")

    def test_the_modules(self):
        cases = {
            "an import that is not the tree": (
                "import Mathlib\n\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nend {m}\n",
                "which is not the tree",
            ),
            "no namespace": (
                "import Tengoku.Seed.Basic\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n",
                "inside exactly one `namespace",
            ),
            "another namespace": (
                "import Tengoku.Seed.Basic\nnamespace Elsewhere\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nend {m}\nend Elsewhere\n",
                "inside exactly one `namespace",
            ),
            "an indented namespace": (
                "import Tengoku.Seed.Basic\nnamespace {m}\n  namespace Elsewhere\n  theorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n    omega\n  end Elsewhere\nend {m}\n",
                "inside exactly one `namespace",
            ),
            "a section": (
                "import Tengoku.Seed.Basic\nnamespace {m}\nsection\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nend\nend {m}\n",
                "inside exactly one `namespace",
            ),
            "scope commands on the line of a declaration": (
                "import Tengoku.Seed.Basic\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\ntheorem z : True := trivial end {m} namespace Elsewhere theorem b : 1 = 1 := rfl end Elsewhere namespace {m}\nend {m}\n",
                "inside exactly one `namespace",
            ),
            "a _root_ name": (
                "import Tengoku.Seed.Basic\nnamespace {m}\ntheorem _root_.Nat.lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nend {m}\n",
                "`_root_` would declare a name outside",
            ),
            "not closed": (
                "import Tengoku.Seed.Basic\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n",
                "the last line must be `end",
            ),
            "code after the end": (
                "import Tengoku.Seed.Basic\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nend {m}\ntheorem sneaky : True := trivial\n",
                "the last line must be `end",
            ),
            "an import after the namespace": (
                "import Tengoku.Seed.Basic\nnamespace {m}\nimport Tengoku.Seed.Basic\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nend {m}\n",
                "an import after the namespace opens",
            ),
            "run_cmd": (
                'import Tengoku.Seed.Basic\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\nrun_cmd Lean.logInfo "x"\nend {m}\n',
                "runs code while the tree compiles",
            ),
            "native_decide": (
                "import Tengoku.Seed.Basic\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  native_decide\nend {m}\n",
                "trusts the compiler",
            ),
            "#eval": (
                "import Tengoku.Seed.Basic\nnamespace {m}\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by\n  omega\n#eval 1\nend {m}\n",
                "no # commands in a record",
            ),
        }
        for label, (text, why) in cases.items():
            r = self.base()
            self.bundle(r, [1])
            r.write(f"Tengoku/Studied/{NS}/S{entry_id(1)[:12]}.lean", text.replace("{m}", mod_of(1)))
            r.commit(label)
            rc, out = r.gate("studied_check.py")
            self.assertNotEqual(rc, 0, label)
            self.assertIn(why, out, label)

    def test_the_root_files(self):
        r = self.base()
        self.bundle(r, [1, 2])
        r.write(f"Tengoku/Studied/{NS}.lean", f"import {mod_of(1)}\n")
        r.commit("root imports one only")
        self.bad(r, "must import each new module exactly once")
        r = self.base()
        self.bundle(r, [1])
        app(r, f"Tengoku/Studied/{NS}.lean", "import Tengoku.Seed.Basic\n")
        r.commit("root imports more")
        self.bad(r, "may only gain the imports of the new modules")
        r = self.base()
        self.bundle(r, [1], first=False)
        self.bad(r, "must gain exactly `import Tengoku.Studied.Erdos396`")

    def test_a_report_may_leave_jinshi_out(self):
        """Jinshi needs Lean and runs in the sandbox, advisory: the intake job's own mechanical checks are the report's `review`; a report that does list Jinshi must show it clean."""
        r = self.base()
        bid = self.bundle(r, [1])
        path = f"data/studied/{T}/bundles/{bid[:16]}.json"
        rep = json.loads((Path(r.dir) / path).read_text())
        del rep["jinshi"]
        r.write(path, json.dumps(rep) + "\n")
        r.commit("a report without Jinshi")
        self.ok(r)

    def test_the_report(self):
        cases = {
            "jinshi found a failure": ({"jinshi": {"fail": 1, "checks": ["x"]}}, "found no failure"),
            "jinshi did not run": ({"jinshi": {"fail": 0, "checks": []}}, "Jinshi must have run"),
            "jinshi is not an object": ({"jinshi": "ran"}, "Jinshi must have run"),
            "a reviewer blocked": (
                {"review": {"blocking": 1, "verdicts": [{"rubric": "g", "verdict": "pass"}]}},
                "none may block or reject",
            ),
            "a reviewer rejected": (
                {"review": {"blocking": 0, "verdicts": [{"rubric": "g", "verdict": "reject"}]}},
                "none may block or reject",
            ),
            "no reviewer": ({"review": {"blocking": 0, "verdicts": []}}, "none may block or reject"),
            "not every entry compiled": ({"preflight": {"compiled": 1, "entries": 2}}, "preflight must have compiled every entry"),
            "rerated lower": (
                {"rerated": [{"entry": entry_id(1), "stars": 3}, {"entry": entry_id(2), "stars": 4}]},
                "by the intake job's own rating",
            ),
            "not rerated": ({"rerated": []}, "by the intake job's own rating"),
            "wrong schema": ({"schema": "x/1"}, "expected 'studied-bundle/1'"),
            "other entries": ({"entries": [entry_id(1), entry_id(9)]}, "`entries` are not the manifest's"),
            "other author": ({"author": "eve"}, "must be the manifest's"),
        }
        for label, (over, why) in cases.items():
            r = self.base()
            self.bundle(r, [1, 2], **over)
            rc, out = r.gate("studied_check.py")
            self.assertNotEqual(rc, 0, label)
            self.assertIn(why, out, label)

    def test_the_harness_evidence(self):
        ids = [entry_id(1), entry_id(2)]

        def with_(**over):
            return {"harness": [harness(ids[0], **over), harness(ids[1])]}

        cases = {
            "no evidence at all": ({"harness": []}, "one evidence record per entry"),
            "an entry without a record": ({"harness": [harness(ids[0])]}, "one evidence record per entry"),
            "a record of another entry": ({"harness": [harness(ids[0]), harness("9" * 28)]}, "one evidence record per entry"),
            "not a list": ({"harness": {"x": 1}}, "one evidence record per entry"),
            "the build not verified": (with_(build_verified=False), "manifest id the server verified"),
            "the build not an id": (with_(build="abc"), "manifest id the server verified"),
            "a run too young": (with_(ticket_age_s=600, seconds=600), "a long-running effort is 30 minutes to 49 hours"),
            "a ticket too old": (with_(ticket_age_s=60 * 3600, seconds=60 * 3600), "a long-running effort is 30 minutes to 49 hours"),
            "a receipt that disagrees": (with_(seconds=2000), "does not match the ticket's age"),
            "a receipt shorter than the minimum": (with_(ticket_age_s=1800, seconds=1000), "does not match the ticket's age"),
            "too few verifications": (with_(verify_ok=3, verify_fail=4), "not those of a prover run"),
            "never failing": (with_(verify_ok=99, verify_fail=1), "not those of a prover run"),
            "never passing": (with_(verify_ok=0, verify_fail=50), "not those of a prover run"),
            "not a memory strategy": (with_(strategy="control-1"), "not a memory strategy"),
            "no attempt": (with_(attempts=0), "not a memory strategy, or no attempt"),
            "counters that are not whole numbers": (with_(verify_ok=60.5), "counters must be whole numbers"),
            "a negative counter": (with_(searches=-1), "counters must be whole numbers"),
        }
        for label, (over, why) in cases.items():
            r = self.base()
            self.bundle(r, [1, 2], **over)
            rc, out = r.gate("studied_check.py")
            self.assertNotEqual(rc, 0, label)
            self.assertIn(why, out, label)
        r = self.base()
        self.bundle(r, [1, 2], **with_(verify_ok=98, verify_fail=2, seconds=3900))
        rc, out = r.gate("studied_check.py")
        self.assertEqual(rc, 0, "the edges of the bands pass: " + out)

    def test_the_bundle_id_is_the_hash_of_what_it_holds(self):
        r = self.base()
        self.bundle(r, [1, 2], bundle="f" * 64)
        self.bad(r, "the bundle id is not the hash of its target, author and entries")
        self.assertEqual(sc.bundle_id(T, AUTHOR, ["b", "a"]), sc.bundle_id(T, AUTHOR, ["a", "b"]))
        self.assertNotEqual(sc.bundle_id(T, AUTHOR, ["a"]), sc.bundle_id(T, "eve", ["a"]))

    def test_the_queue_builds_exactly_the_modules_the_pr_adds(self):
        r = self.base()
        self.bundle(r, [1, 2])
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(out.split()), sorted(f"Tengoku.Studied.{NS}.S{entry_id(n)[:12]}" for n in (1, 2)))

    # ---- who may approve -----------------------------------------------------------------------------------------------------------------

    def data(self, reviews, **over):
        d = {
            "author": "tengoku-supervisor[bot]",
            "head": "H2",
            "owners": ["owner-main", "owner-alt"],
            "committers": ["tengoku-supervisor[bot]"],
            "permissions": {"w1": "write", "w2": "maintain", "w3": "admin", "r1": "read", "owner-main": "admin", "owner-alt": "write"},
            "reviews": reviews,
        }
        return {**d, **over}

    def rv(self, user, state="APPROVED", commit="H2", typ="User"):
        return {"user": user, "state": state, "commit_id": commit, "type": typ}

    def test_one_code_owner_is_enough(self):
        for who in ("owner-main", "owner-alt"):
            ok, why = sa.decide(self.data([self.rv(who)]))
            self.assertTrue(ok, why)
            self.assertIn("code owner", why)

    def test_two_independent_contributors_with_write_access_are_enough(self):
        ok, why = sa.decide(self.data([self.rv("w1"), self.rv("w2")]))
        self.assertTrue(ok, why)
        self.assertIn("two independent contributors", why)
        self.assertTrue(sa.decide(self.data([self.rv("w3"), self.rv("w1")]))[0])

    def test_one_contributor_is_not(self):
        ok, why = sa.decide(self.data([self.rv("w1")]))
        self.assertFalse(ok)
        self.assertIn("needs one code owner's approval, or two approvals", why)
        self.assertFalse(sa.decide(self.data([self.rv("w1"), self.rv("w1")]))[0], "the same person twice is one")
        self.assertFalse(sa.decide(self.data([]))[0])
        self.assertIn("no approval yet", sa.decide(self.data([]))[1])

    def test_read_access_does_not_count(self):
        self.assertFalse(sa.decide(self.data([self.rv("w1"), self.rv("r1")]))[0])
        self.assertFalse(sa.decide(self.data([self.rv("w1"), self.rv("stranger")]))[0])

    def test_the_author_the_app_and_committers_never_count(self):
        self.assertFalse(sa.decide(self.data([self.rv("tengoku-supervisor[bot]")]))[0])
        self.assertFalse(sa.decide(self.data([self.rv("w1"), self.rv("w2")], committers=["w2"]))[0], "w2 committed to the PR")
        self.assertFalse(sa.decide(self.data([self.rv("w1"), self.rv("w2")], author="w2"))[0], "w2 is the author")
        self.assertFalse(
            sa.decide(self.data([self.rv("w1"), self.rv("some-bot", typ="Bot")], permissions={"w1": "write", "some-bot": "write"}))[0]
        )
        self.assertFalse(sa.decide(self.data([self.rv("owner-main")], author="owner-main"))[0], "an owner cannot approve their own")

    def test_the_two_accounts_of_one_maintainer_never_pad_the_second_path(self):
        # they are code owners, so one of them passes by itself; but a contributor plus an owner who did not approve is still one contributor
        self.assertFalse(sa.decide(self.data([self.rv("w1")], owners=["w1x"]))[0])
        ok, _ = sa.decide(self.data([self.rv("w1"), self.rv("owner-alt")]))
        self.assertTrue(ok)

    def test_an_approval_of_an_older_commit_is_stale(self):
        self.assertFalse(sa.decide(self.data([self.rv("owner-main", commit="H1")]))[0])
        self.assertFalse(sa.decide(self.data([self.rv("w1", commit="H1"), self.rv("w2")]))[0])
        self.assertTrue(
            sa.decide(self.data([self.rv("w1", commit="H1"), self.rv("w1"), self.rv("w2")]))[0], "approving again on the new head counts"
        )

    def test_requested_changes_block_until_they_are_withdrawn(self):
        ok, why = sa.decide(self.data([self.rv("w1", "CHANGES_REQUESTED"), self.rv("owner-main")]))
        self.assertFalse(ok)
        self.assertIn("changes are requested by w1", why)
        self.assertTrue(sa.decide(self.data([self.rv("w1", "CHANGES_REQUESTED"), self.rv("w1", "DISMISSED"), self.rv("owner-main")]))[0])
        self.assertTrue(
            sa.decide(self.data([self.rv("w1", "CHANGES_REQUESTED"), self.rv("w1"), self.rv("owner-main")]))[0], "they approved afterwards"
        )
        self.assertFalse(
            sa.decide(self.data([self.rv("owner-main"), self.rv("w1", "CHANGES_REQUESTED", commit="H1")]))[0],
            "a request for changes stands on any commit",
        )

    def test_a_later_comment_changes_nothing_and_a_dismissed_approval_is_gone(self):
        self.assertTrue(sa.decide(self.data([self.rv("owner-main"), self.rv("owner-main", "COMMENTED")]))[0])
        self.assertFalse(sa.decide(self.data([self.rv("owner-main"), self.rv("owner-main", "DISMISSED")]))[0])
        self.assertFalse(sa.decide(self.data([self.rv("owner-main", "PENDING")]))[0])

    def test_the_command_line_exits_by_the_decision(self):
        with tempfile.TemporaryDirectory() as d:
            for reviews, code in (([self.rv("owner-main")], 0), ([], 1)):
                p = Path(d) / "d.json"
                p.write_text(json.dumps(self.data(reviews)))
                with p.open() as fh:
                    r = subprocess.run([sys.executable, str(HERE.parent / "studied_approval.py")], stdin=fh, capture_output=True, text=True)
                self.assertEqual(r.returncode, code, r.stdout + r.stderr)
            r = subprocess.run([sys.executable, str(HERE.parent / "studied_approval.py"), "d.json"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 2)
            r = subprocess.run([sys.executable, str(HERE.parent / "studied_approval.py")], input="not json", capture_output=True, text=True)
            self.assertEqual(r.returncode, 2)


if __name__ == "__main__":
    unittest.main()
