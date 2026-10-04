"""generate.py's verified generator: the tree is built from the records' verified contexts, never the corpus.
Checks the modules it writes (Lean is not run: the merge queue builds them)."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from generate import prelude_blocks, topo_order  # noqa: E402

HEAD = "set_option linter.all false -- [Emissary] lints are not drift; the kernel decides\n\n"


def prelude(mod: str, body: str, kind: str = "verbatim") -> str:
    return f"-- [Emissary prelude] {mod} — {kind} (imports stripped)\n{body}\n"


def own(path: str, line: int, body: str) -> str:
    return f"-- [Emissary] {path}, everything before line {line} (imports stripped; sibling theorems the target does not use omitted)\n{body}\n"


def rec(name: str, src: str, context: str, stmt: str | None = None) -> dict:
    return {
        "name": name,
        "statement": stmt or f"theorem {name} : True",
        "proof": ":= trivial",
        "context": context,
        "source_path": src,
        "status": "trusted",
        "promoted_at": "2026-01-01T00:00:00Z",
        "library": "lib-x",
        "source_url": f"https://example.com/{src}",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
    }


class Parsing(unittest.TestCase):
    def test_prelude_blocks_run_to_the_next_marker_or_the_own_file_marker(self):
        ctx = HEAD + prelude("Lx.A", "def a := 1") + prelude("Lx.B", "def b := a", "expanded") + own("Lx/C.lean", 9, "def c := b")
        blocks = prelude_blocks(ctx)
        self.assertEqual([m for m, _ in blocks], ["Lx.A", "Lx.B"])
        self.assertEqual(blocks[1][1].strip(), "def b := a")  # an expanded block counts too (the legacy generator missed it)
        self.assertNotIn("def c", blocks[1][1])

    def test_topo_order_respects_every_context(self):
        self.assertEqual(topo_order([["A", "B", "D"], ["C", "D"], ["B", "C"]]), ["A", "B", "C", "D"])


class Generate(unittest.TestCase):
    def setUp(self):
        self.out = Path(tempfile.mkdtemp())
        shutil.copytree(ROOT / "scripts", self.out / "scripts")
        (self.out / "schemas").mkdir()
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]}}})
        )
        (self.out / "Tengoku").mkdir()
        (self.out / "data" / "trusted").mkdir(parents=True)

    def tearDown(self):
        shutil.rmtree(self.out)

    def generate(self, records: list[dict]) -> str:
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return r.stdout

    def read(self, rel: str) -> str:
        return (self.out / "Tengoku" / rel).read_text()

    def test_deps_are_the_verified_blocks_and_nothing_from_outside_the_tree(self):
        a = prelude("Lx.A", "import Architect\n@[blueprint] def a := 1")  # what a block could never hold: the bridge strips it
        ctx1 = HEAD + prelude("Lx.A", "def a := 1") + prelude("Lx.B", "def b := a") + own("Lx/C.lean", 9, "namespace Lx\ndef c := b")
        ctx2 = HEAD + prelude("Lx.A", "def a := 1") + own("Lx/D.lean", 3, "")
        self.generate([rec("Lx.t1", "Lx/C.lean", ctx1), rec("t2", "Lx/D.lean", ctx2)])
        dep_a, dep_b = self.read("LibX/Deps/A.lean"), self.read("LibX/Deps/B.lean")
        self.assertIn("def a := 1", dep_a)
        self.assertIn("import Tengoku\n", dep_a)
        self.assertNotIn("Deps.B", dep_a)
        self.assertIn("import Tengoku.LibX.Deps.A", dep_b)  # the block before it in the context
        c = self.read("LibX/C.lean")
        self.assertIn("import Tengoku\nimport Tengoku.LibX.Deps.A\nimport Tengoku.LibX.Deps.B", c)
        self.assertIn("def c := b", c)
        self.assertIn("theorem Lx.t1 : True", c)
        self.assertTrue(c.rstrip().endswith("theorem Lx.t1 : True := trivial"), c)  # Lean closes the namespace left open
        self.assertNotIn("namespace LibX", c)  # never wrapped: the text is exactly what was verified
        for f in (self.out / "Tengoku").rglob("*.lean"):
            self.assertNotIn("Architect", f.read_text(), f)
        self.assertIn("import Tengoku.LibX", self.read("All.lean"))
        del a

    def test_the_most_common_block_version_wins(self):
        v1 = HEAD + prelude("Lx.A", "def a := 1") + own("Lx/C.lean", 2, "")
        v2 = HEAD + prelude("Lx.A", "def a := 2") + own("Lx/C.lean", 2, "")
        self.generate([rec("t1", "Lx/C.lean", v1), rec("t2", "Lx/C.lean", v1), rec("t3", "Lx/C.lean", v2)])
        dep = self.read("LibX/Deps/A.lean")
        self.assertIn("def a := 1", dep)
        self.assertIn("2 versions across records", dep)

    def test_pruned_block_versions_are_merged(self):
        # each record's block holds only what its theorem reaches: the Deps module must hold every part some record needed
        v1 = HEAD + prelude("Lx.A", "def a := 1\ndef b := 2") + own("Lx/C.lean", 2, "")
        v2 = HEAD + prelude("Lx.A", "def a := 1\ndef c := 3") + own("Lx/D.lean", 2, "")
        self.generate([rec("t1", "Lx/C.lean", v1), rec("t2", "Lx/C.lean", v1), rec("t3", "Lx/D.lean", v2)])
        dep = self.read("LibX/Deps/A.lean")
        for d in ("def a := 1", "def b := 2", "def c := 3"):
            self.assertIn(d, dep)
        self.assertEqual(dep.count("def a"), 1)
        self.assertLess(dep.index("def a"), dep.index("def c"))

    def test_a_theorem_a_deps_module_already_has_is_not_declared_again(self):
        # Lx/A.lean is another record's prelude; its own record (t_a, the original text) lives in Deps/A already
        ctx_b = HEAD + prelude("Lx.A", "def a := 1\ntheorem t_a : True := trivial") + own("Lx/B.lean", 4, "")
        ctx_a = HEAD + own("Lx/A.lean", 2, "def a := 1")
        self.generate([rec("t_b", "Lx/B.lean", ctx_b), rec("t_a", "Lx/A.lean", ctx_a)])
        a_mod = self.read("LibX/A.lean")
        self.assertNotIn("theorem t_a", a_mod)
        self.assertNotIn("def a := 1", a_mod)
        self.assertIn("import Tengoku.LibX.Deps.A", a_mod)  # its own Deps module
        self.assertIn("theorem t_b", self.read("LibX/B.lean"))

    def test_repeated_sections_are_aligned_not_collapsed(self):
        # two records of one file; the second's block repeats `section`/`end` further down: both pairs must survive
        pre1 = "section\ndef a := 1\nend"
        pre2 = pre1 + "\nsection\ndef b := 2\nend"
        self.generate([rec("t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 4, pre1)), rec("t2", "Lx/C.lean", HEAD + own("Lx/C.lean", 8, pre2))])
        c = self.read("LibX/C.lean")
        self.assertEqual(c.count("section\n"), 2, c)
        self.assertEqual(len([l for l in c.splitlines() if l == "end"]), 2, c)
        self.assertLess(c.index("theorem t1"), c.index("def b := 2"))  # each theorem right after its own block
        self.assertLess(c.index("def b := 2"), c.index("theorem t2"))

    def test_constructor_and_deriving_lines_stay_with_their_declaration(self):
        pre = "inductive Col\n| red\n| blue\nderiving DecidableEq"
        self.generate([rec("t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 5, pre)), rec("t2", "Lx/C.lean", HEAD + own("Lx/C.lean", 5, pre))])
        c = self.read("LibX/C.lean")
        self.assertIn("inductive Col\n| red\n| blue\nderiving DecidableEq", c)
        self.assertEqual(c.count("deriving DecidableEq"), 1)

    def test_a_doc_comment_left_by_a_theorem_in_deps_is_dropped(self):
        ctx_b = HEAD + prelude("Lx.A", "def a := 1\ntheorem t_a : True := trivial") + own("Lx/B.lean", 4, "")
        ctx_a = HEAD + own("Lx/A.lean", 3, "def a := 1\n/-- about t_a -/")  # the harvester's line points below the doc comment
        self.generate([rec("t_b", "Lx/B.lean", ctx_b), rec("t_a", "Lx/A.lean", ctx_a)])
        self.assertNotIn("about t_a", self.read("LibX/A.lean"))

    def test_deps_imports_follow_the_corpus_import_graph(self):
        # contexts list A after B (a harmless reordering); B's file imports A, so Deps/B must import Deps/A
        corpus = self.out / "corpus"
        (corpus / "Lx").mkdir(parents=True)
        (corpus / "Lx" / "A.lean").write_text("import Mathlib\ndef a := 1\n")
        (corpus / "Lx" / "B.lean").write_text("import Lx.A\nimport Architect\ndef b := a\n")
        ctx = HEAD + prelude("Lx.B", "def b := a") + prelude("Lx.A", "def a := 1") + own("Lx/C.lean", 2, "")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(rec("t1", "Lx/C.lean", ctx)) + "\n")
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("import Tengoku.LibX.Deps.A", self.read("LibX/Deps/B.lean"))
        self.assertNotIn("Deps.B", self.read("LibX/Deps/A.lean"))
        self.assertNotIn("Architect", self.read("LibX/Deps/B.lean"))

    def test_the_same_short_name_in_two_namespaces_is_two_declarations(self):
        pre = "namespace P\ntheorem lemma1 : True := trivial\nend P\nnamespace Q\ntheorem lemma1 : True := trivial\nend Q"
        self.generate([rec("t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 7, pre))])
        self.assertEqual(self.read("LibX/C.lean").count("theorem lemma1"), 2)

    def test_a_deps_name_in_another_namespace_does_not_hide_a_local_one(self):
        ctx_b = HEAD + prelude("Lx.A", "namespace P\ndef f := 1\nend P") + own("Lx/B.lean", 5, "namespace Q\ndef f := 2\nend Q")
        self.generate([rec("t_b", "Lx/B.lean", ctx_b)])
        self.assertIn("def f := 2", self.read("LibX/B.lean"))  # Q.f is not P.f

    def generate_with_corpus(self, records: list[dict], files: dict[str, str]) -> None:
        corpus = self.out / "corpus"
        for rel, text in files.items():
            (corpus / rel).parent.mkdir(parents=True, exist_ok=True)
            (corpus / rel).write_text(text)
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_an_agent_script_is_not_merged_and_its_theorem_stands_where_the_original_did(self):
        src = "namespace Lx\ntheorem t1 : True := trivial\ntheorem t2 : True := trivial\ntheorem t3 : True := trivial\nend Lx\n"
        agent_ctx = HEAD + "namespace Lx\ndef helper := 5\nend Lx\n"  # restated, no markers
        self.generate_with_corpus(
            [
                rec("Lx.t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 2, "namespace Lx"), "theorem t1 : True"),
                rec("Lx.t2", "Lx/C.lean", agent_ctx, "theorem t2 : True"),
                rec("Lx.t3", "Lx/C.lean", HEAD + own("Lx/C.lean", 4, "namespace Lx"), "theorem t3 : True"),
            ],
            {"Lx/C.lean": src},
        )
        c = self.read("LibX/C.lean")
        self.assertNotIn("helper", c)
        self.assertEqual(c.count("namespace Lx"), 1, c)
        self.assertLess(c.index("theorem t1"), c.index("theorem t2"))
        self.assertLess(c.index("theorem t2"), c.index("theorem t3"))

    def test_an_agent_theorem_under_other_namespaces_is_named_in_full(self):
        src = "namespace Lx\nnamespace Inner\ntheorem t1 : True := trivial\nend Inner\ntheorem t2 : True := trivial\nend Lx\n"
        self.generate_with_corpus(
            [
                rec("Lx.Inner.t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 3, "namespace Lx\nnamespace Inner"), "theorem t1 : True"),
                rec("Lx.t2", "Lx/C.lean", HEAD + "namespace Lx\nend Lx\n", "theorem t2 : True"),
            ],
            {"Lx/C.lean": src},
        )
        self.assertIn("theorem _root_.Lx.t2 : True", self.read("LibX/C.lean"))

    def test_an_attribute_on_the_line_above_the_theorem_stays(self):
        # the prefix is the self-contained text's, whose lines need not be the corpus file's
        src = "def a := 1\n\n\n@[fun_prop]\ntheorem t_a : a = 1 := rfl\n"
        self.generate_with_corpus(
            [rec("t_a", "Lx/C.lean", HEAD + own("Lx/C.lean", 3, "def a := 1\n@[simp]"), "theorem t_a : a = 1")], {"Lx/C.lean": src}
        )
        c = self.read("LibX/C.lean")
        self.assertIn("@[simp]", c)
        self.assertLess(c.index("@[simp]"), c.index("theorem t_a"))

    def test_an_identical_copy_is_kept_once_and_a_different_one_renamed(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps(
                {
                    "corpora": {
                        "lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]},
                        "lib-y": {"repo": "r", "commit": "c", "roots": ["Ly"]},
                    }
                }
            )
        )
        box = "namespace S\nstructure Box where\n  v : {ty}\ntheorem Box.v_eq (b : Box) : b.v = b.v := rfl\nend S\n"
        helper = "theorem Nat.helper : True := trivial"
        x = rec("S.t", "Lx/C.lean", HEAD + own("Lx/C.lean", 8, box.format(ty="Nat") + helper), "theorem S.t (b : S.Box) : b.v_eq = b.v_eq")
        y = dict(
            rec(
                "S.u",
                "Ly/C.lean",
                HEAD + own("Ly/C.lean", 8, box.format(ty="Int") + helper),
                "theorem S.u (b : S.Box) : Nat.helper = Nat.helper",
            ),
            library="lib-y",
        )
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(x) + "\n")
        (self.out / "data" / "trusted" / "lib-y.jsonl").write_text(json.dumps(y) + "\n")
        runs = [
            subprocess.run(
                [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", lib],
                cwd=self.out,
                capture_output=True,
                text=True,
            )
            for lib in ("lib-x", "lib-y")
        ]
        for r in runs:
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn(
            "3 clashes with other libraries (2 identical, 1 differing): 1 kept once (imported), 1 renamed *__lib_y", runs[1].stdout
        )
        cx, cy = self.read("LibX/C.lean"), self.read("LibY/C.lean")
        self.assertIn("structure Box where", cx)  # the library already in the tree keeps its names
        self.assertIn("structure Box__lib_y where", cy)  # a different Box: renamed, its lemma with it
        self.assertIn("theorem Box__lib_y.v_eq (b : Box__lib_y)", cy)
        self.assertNotIn("theorem Nat.helper", cy)  # the identical helper: lib-x's, imported
        self.assertIn("import Tengoku.LibX.C", cy)
        self.assertIn("theorem S.u (b : S.Box__lib_y) : Nat.helper = Nat.helper", cy)
        # regenerating either one again changes nothing: the newcomer keeps its renames, the incumbent its names
        for lib in ("lib-x", "lib-y"):
            subprocess.run(
                [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", lib],
                cwd=self.out,
                capture_output=True,
                text=True,
            )
        self.assertEqual((cx, cy), (self.read("LibX/C.lean"), self.read("LibY/C.lean")))

    def test_a_rename_stays_where_the_declaration_is_in_scope(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps(
                {
                    "corpora": {
                        "lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]},
                        "lib-y": {"repo": "r", "commit": "c", "roots": ["Ly"]},
                    }
                }
            )
        )
        x = rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 3, "def f (n : Nat) : Nat := n"), "theorem t : f 0 = 0")
        y1 = dict(
            rec("u", "Ly/C.lean", HEAD + own("Ly/C.lean", 3, "def f (n : Nat) : Nat := n + 0"), "theorem u : f 0 = Nat.add (n := 0) 0"),
            library="lib-y",
        )
        y2 = dict(rec("v", "Ly/D.lean", HEAD + own("Ly/D.lean", 1, ""), "theorem v (f : Nat → Nat) : f 0 = f 0"), library="lib-y")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(x) + "\n")
        (self.out / "data" / "trusted" / "lib-y.jsonl").write_text(json.dumps(y1) + "\n" + json.dumps(y2) + "\n")
        for lib in ("lib-x", "lib-y"):
            r = subprocess.run(
                [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", lib],
                cwd=self.out,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        c = self.read("LibY/C.lean")
        self.assertIn("def f__lib_y (n : Nat)", c)
        self.assertIn("theorem u : f__lib_y 0 = Nat.add (n := 0) 0", c)  # a named argument is a parameter's name
        self.assertIn("theorem v (f : Nat → Nat) : f 0 = f 0", self.read("LibY/D.lean"))  # f is not in scope there

    def test_an_indented_end_is_a_scope_line(self):
        pre = "section Aux\ntheorem a : True := trivial\n  end Aux\nsection Aux\n  end Aux"
        self.generate([rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 6, pre))])
        c = self.read("LibX/C.lean")
        self.assertEqual(c.count("section Aux"), c.count("end Aux"), c)
        self.assertLess(c.index("theorem t"), len(c))
        self.assertNotIn("  end Aux", c)

    def test_a_declaration_stays_before_what_uses_it_when_blocks_omit_different_parts(self):
        # the file: def c, lemma c_apply, lemma p, theorem t1, lemma i (uses c_apply), theorem t2
        # t1's block omits c_apply; t2's block omits p: merged, c_apply must still come before i
        b1 = "def c := 1\nlemma p : c = c := rfl"
        b2 = "def c := 1\nlemma c_apply : c = 1 := rfl\nlemma i : c = 1 := c_apply"
        self.generate(
            [
                rec("t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 4, b1)),
                rec("t2", "Lx/C.lean", HEAD + own("Lx/C.lean", 6, b2)),
            ]
        )
        c = self.read("LibX/C.lean")
        self.assertLess(c.index("lemma c_apply"), c.index("lemma i"))
        self.assertLess(c.index("theorem t1"), c.index("theorem t2"))

    def test_a_theorem_a_later_block_carries_is_used_as_the_file_wrote_it(self):
        # t1's record started a line late (no `variable (n) in`); t2's block carries t1 as the file wrote it
        pre1 = "variable {n : Nat}"
        pre2 = "variable {n : Nat}\nvariable (n) in\ntheorem t1 : n = n := rfl"
        self.generate(
            [
                rec("t1", "Lx/C.lean", HEAD + own("Lx/C.lean", 3, pre1), "theorem t1 : n = n"),
                rec("t2", "Lx/C.lean", HEAD + own("Lx/C.lean", 5, pre2), "theorem t2 : t1 0 = t1 0"),
            ]
        )
        c = self.read("LibX/C.lean")
        self.assertIn("variable (n) in\ntheorem t1", c)
        self.assertEqual(c.count("theorem t1"), 1)

    def test_an_unnamed_instance_another_library_declares_gets_a_name(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps(
                {
                    "corpora": {
                        "lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]},
                        "lib-y": {"repo": "r", "commit": "c", "roots": ["Ly"]},
                    }
                }
            )
        )
        pre = "local instance : Inhabited Nat := ⟨0⟩"
        x = rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 2, pre))
        y = dict(rec("u", "Ly/C.lean", HEAD + own("Ly/C.lean", 2, pre)), library="lib-y")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(x) + "\n")
        (self.out / "data" / "trusted" / "lib-y.jsonl").write_text(json.dumps(y) + "\n")
        for lib in ("lib-x", "lib-y"):
            r = subprocess.run(
                [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", lib],
                cwd=self.out,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("local instance : Inhabited Nat", self.read("LibX/C.lean"))
        self.assertRegex(self.read("LibY/C.lean"), r"local instance inst_[0-9a-f]{8}__lib_y : Inhabited Nat")

    def test_an_unknown_generator_mode_is_refused(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"], "generator": "Legacy"}}})
        )
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 1, ""))) + "\n")
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("neither", r.stdout + r.stderr)

    def test_a_named_instance_goes_after_its_doc_comment_and_priority(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps(
                {
                    "corpora": {
                        "lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]},
                        "lib-y": {"repo": "r", "commit": "c", "roots": ["Ly"]},
                    }
                }
            )
        )
        pre = "/-- the instance we need -/\ninstance (priority := low) : Inhabited Nat := ⟨0⟩"
        x = rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 3, pre))
        y = dict(rec("u", "Ly/C.lean", HEAD + own("Ly/C.lean", 3, pre)), library="lib-y")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(x) + "\n")
        (self.out / "data" / "trusted" / "lib-y.jsonl").write_text(json.dumps(y) + "\n")
        for lib in ("lib-x", "lib-y"):
            subprocess.run(
                [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", lib],
                cwd=self.out,
                capture_output=True,
                text=True,
            )
        c = self.read("LibY/C.lean")
        self.assertIn("/-- the instance we need -/", c)
        self.assertRegex(c, r"instance \(priority := low\) inst_[0-9a-f]{8}__lib_y : Inhabited Nat")

    def candidates(self, staged: list[dict], order: list[tuple[str, str]]) -> None:
        """The merge queue: each file's candidate generated in turn (only that file's records of the group), built at the end."""
        (self.out / "data" / "staging").mkdir(parents=True, exist_ok=True)
        (self.out / "data" / "staging" / "lib-x.jsonl").write_text("".join(json.dumps(dict(r, status="staging")) + "\n" for r in staged))
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text("")
        for sp, names in order:
            r = subprocess.run(
                [
                    sys.executable,
                    "scripts/generate.py",
                    "--corpus",
                    "/nonexistent",
                    "--libraries",
                    "lib-x",
                    "--candidate",
                    sp,
                    "--candidate-names",
                    names,
                ],
                cwd=self.out,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_an_earlier_candidates_deps_module_survives_a_later_candidate(self):
        e = rec("e", "Lx/E.lean", HEAD + prelude("Lx.Bit", "def bit := 1") + own("Lx/E.lean", 2, ""), "theorem e : bit = bit")
        f = rec("f", "Lx/F.lean", HEAD + prelude("Lx.Other", "def other := 2") + own("Lx/F.lean", 2, ""), "theorem f : other = other")
        self.candidates([e, f], [("Lx/E.lean", "e"), ("Lx/F.lean", "f")])
        self.assertTrue((self.out / "Tengoku" / "LibX" / "Deps" / "Bit.lean").exists())  # _candidate_E imports it
        self.assertIn("import Tengoku.LibX.Deps.Bit", self.read("LibX/_candidate_E.lean"))

    def test_a_candidate_keeps_what_only_another_candidates_deps_module_has(self):
        # B's record carries A's module as a prelude; A's own candidate does not import that Deps module
        b = rec("b", "Lx/B.lean", HEAD + prelude("Lx.A", "def a := 1") + own("Lx/B.lean", 2, ""), "theorem b : a = a")
        a = rec("ta", "Lx/A.lean", HEAD + own("Lx/A.lean", 2, "def a := 1"), "theorem ta : a = a")
        self.candidates([b, a], [("Lx/B.lean", "b"), ("Lx/A.lean", "ta")])
        c = self.read("LibX/_candidate_A.lean")
        self.assertIn("def a := 1", c)
        self.assertNotIn("Deps.A", c)

    def test_a_credit_correction_shows_in_the_module_and_the_record_stays(self):
        doc = "/-- One plus one.\n\nAuthor: Mallory (https://example.org/m). -/\n"
        t = rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 1, ""), doc + "theorem t : True")
        corr = {
            "credit_correction": "t",
            "credit": "Author: Alice (https://example.org/a)",
            "evidence": "https://example.org/proof",
            "by": "x",
            "at": "2026-09-29",
        }
        note = {"tombstone_note": "gone", "note": "see elsewhere", "by": "x", "at": "2026-09-29"}
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text("".join(json.dumps(x) + "\n" for x in (t, corr, note)))
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        c = self.read("LibX/C.lean")
        self.assertIn("Author: Alice (https://example.org/a)", c)
        self.assertIn("Credit corrected; evidence: https://example.org/proof", c)
        self.assertNotIn("Mallory", c)
        self.assertIn("Mallory", (self.out / "data" / "trusted" / "lib-x.jsonl").read_text())  # the record is never edited

    def test_the_newest_credit_correction_wins_and_a_leading_comment_is_kept(self):
        doc = "-- a note\n/-- One plus one.\n\nAuthor: Mallory (https://example.org/m). -/\n"
        t = rec("t", "Lx/C.lean", HEAD + own("Lx/C.lean", 1, ""), doc + "theorem t : True")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(t) + "\n")
        (self.out / "data" / "trusted" / "lib-x").mkdir()
        new = {"credit_correction": "t", "credit": "Author: Newest", "evidence": "https://example.org/2", "by": "x", "at": "2026-09-30"}
        old = {"credit_correction": "t", "credit": "Author: Older", "evidence": "https://example.org/1", "by": "x", "at": "2026-09-01"}
        (self.out / "data" / "trusted" / "lib-x" / "a.jsonl").write_text(json.dumps(new) + "\n")
        (self.out / "data" / "trusted" / "lib-x" / "z.jsonl").write_text(json.dumps(old) + "\n")  # read last, still older
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        c = self.read("LibX/C.lean")
        self.assertIn("Author: Newest", c)
        self.assertNotIn("Author: Older", c)
        self.assertNotIn("Mallory", c)
        self.assertEqual(c.count("/--"), 1)
        self.assertIn("-- a note\n/-- One plus one.", c)  # what came before the docstring is kept

    def test_legacy_libraries_are_untouched_by_the_verified_path(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"], "generator": "legacy"}}})
        )
        corpus = self.out / "corpus"
        (corpus / "Lx").mkdir(parents=True)
        (corpus / "Lx" / "A.lean").write_text("def a := 1\n")
        ctx = HEAD + prelude("Lx.A", "def a := 1") + own("Lx/C.lean", 2, "")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(rec("t1", "Lx/C.lean", ctx)) + "\n")
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("namespace LibX", self.read("LibX/Deps/A.lean"))  # the legacy generator wraps; the verified one never does


if __name__ == "__main__":
    unittest.main()
