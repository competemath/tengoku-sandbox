"""generate.py writes the module names of the seed as the tree it generates into spells them: Tengoku.Seed.* in the Seed layout, Tengoku.* in the
earlier one (told apart by the folder Tengoku/Seed). Library modules are the same in both."""

from __future__ import annotations

import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import generate  # noqa: E402


def write(root: Path, rel: str, text: str) -> Path:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")
    return p


HEAD = "set_option linter.all false -- [Emissary] lints are not drift; the kernel decides\n\n"
CORPUS_A = "import Mathlib.Data.Nat.Basic\nimport Batteries.Data.List.Basic\nimport Mathlib\nimport Lean\ndef a := 1\n"
CORPUS_C = "import Mathlib.Order.Basic\nimport Lx.A\n"


def record(name: str, ctx: str) -> dict:
    return {
        "name": name,
        "statement": f"theorem {name} : True",
        "proof": ":= trivial",
        "context": ctx,
        "source_path": "Lx/C.lean",
        "status": "trusted",
        "promoted_at": "2026-01-01T00:00:00Z",
        "library": "lib-x",
        "source_url": "https://example.com/Lx/C.lean",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
    }


class Generating(unittest.TestCase):
    """generate.py writes the seed's module names as the tree it generates into spells them."""

    def tree(self, seeded: bool, generator: str = "legacy") -> Path:
        out = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, out)
        write(
            out,
            "schemas/sources.json",
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"], "generator": generator}}}),
        )
        write(out, "Tengoku/Seed/Init.lean" if seeded else "Tengoku/Init.lean", "module\n")
        write(out, "corpus/Lx/A.lean", CORPUS_A)
        write(out, "corpus/Lx/C.lean", CORPUS_C)
        ctx = HEAD + "-- [Emissary prelude] Lx.A — verbatim (imports stripped)\ndef a := 1\n"
        ctx += "-- [Emissary] Lx/C.lean, everything before line 2 (imports stripped)\n"
        write(out, "data/trusted/lib-x.jsonl", json.dumps(record("t1", ctx)) + "\n")
        return out

    def generate(self, out: Path, *libraries: str) -> str:
        argv = ["generate.py", "--corpus", str(out / "corpus"), "--out", str(out), "--libraries", *(libraries or ("lib-x",))]
        buf = io.StringIO()
        with mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(buf):
            generate.main()
        return buf.getvalue()

    def files(self, out: Path) -> dict[str, str]:
        return {p.relative_to(out).as_posix(): p.read_text(encoding="utf-8") for p in sorted((out / "Tengoku").rglob("*.lean"))}

    def test_the_earlier_layout_gets_the_earlier_names(self):
        out = self.tree(seeded=False)
        self.generate(out)
        deps = (out / "Tengoku" / "LibX" / "Deps" / "A.lean").read_text()
        self.assertIn(
            "import Tengoku.Data.Nat.Basic\nimport Tengoku.Std.Data.List.Basic\nimport Tengoku\nimport Lean\nimport Tengoku.Init\n", deps
        )
        mod = (out / "Tengoku" / "LibX" / "C.lean").read_text()
        self.assertIn("import Tengoku.Order.Basic\nimport Tengoku.LibX.Deps.A\n", mod)

    def test_the_seed_layout_gets_the_seed_names(self):
        out = self.tree(seeded=True)
        self.generate(out)
        deps = (out / "Tengoku" / "LibX" / "Deps" / "A.lean").read_text()
        self.assertIn(
            "import Tengoku.Seed.Data.Nat.Basic\nimport Tengoku.Seed.Std.Data.List.Basic\nimport Tengoku\nimport Lean\nimport Tengoku.Seed.Init\n",
            deps,
        )
        mod = (out / "Tengoku" / "LibX" / "C.lean").read_text()
        self.assertIn("import Tengoku.Seed.Order.Basic\nimport Tengoku.LibX.Deps.A\n", mod)

    def test_the_aggregator_lists_the_library_not_the_seed(self):
        out = self.tree(seeded=True)
        write(out, "Tengoku/Seed/Algebra/X.lean", "module\n")
        self.generate(out)
        self.assertEqual((out / "Tengoku" / "All.lean").read_text().splitlines()[1:], ["import Tengoku", "import Tengoku.LibX"])
        self.assertEqual(
            (out / "Tengoku" / "Seed" / "Algebra" / "X.lean").read_text(), "module\n"
        )  # a library's regeneration leaves the seed alone

    def test_the_verified_generator_does_not_depend_on_the_layout(self):
        outs = [self.tree(seeded=s, generator="verified") for s in (False, True)]
        for out in outs:
            self.generate(out)
        old, new = (self.files(o) for o in outs)
        seed_files = {k for k in new if k.startswith("Tengoku/Seed/")}
        self.assertEqual({k: v for k, v in new.items() if k not in seed_files}, {k: v for k, v in old.items() if k != "Tengoku/Init.lean"})
        self.assertIn("import Tengoku\n", new["Tengoku/LibX/C.lean"])


if __name__ == "__main__":
    unittest.main()
