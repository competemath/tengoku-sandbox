"""Bulk attribution, property-tested: files assembled at random from every lead-in shape the tool
knows (docstring forms, attributes, modifiers, `open … in`, comments, mutual blocks, decoys), each
with the output the spec says the tool must produce. Exact output, idempotence, counts."""

from __future__ import annotations

import importlib.util
import random
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("attribute", ROOT / "tools" / "attribute" / "attribute.py")
attribute = importlib.util.module_from_spec(spec)
sys.modules["attribute"] = attribute
spec.loader.exec_module(attribute)

CREDIT = "Author: Ada Lovelace (https://github.com/ada), with Claude Fable 5.1."
OTHER = "Author: Someone Else (https://example.org)."

# Every declaration compiles under `namespace Gen` with `import Mathlib`: the property test never
# compiles, but the same files are what the Leak IV compile check runs.
BODIES = {
    "theorem": "{n} (k : Nat) : k + 0 = k := rfl",
    "lemma": "{n} (k : Nat) : k + 0 = k := rfl",
    "def": "{n} : Nat := 1",
    "abbrev": "{n} : Nat := 1",
    "instance": "{n} : Inhabited Nat := ⟨1⟩",
    "structure": "{n} where\n  x : Nat",
    "inductive": "{n} where\n  | a",
    "class": "{n} where\n  x : Nat",
    "opaque": "{n} : Nat",
}
ATTRS = {  # name -> (same-line form, own-lines form)
    "simp": ("@[simp] ", "@[simp]\n"),
    "multi": (None, "@[simp,\n  nolint unusedArguments]\n"),
    "string": ('@[deprecated "use [x]" (since := "2026-01-01")] ', '@[deprecated "use [x]" (since := "2026-01-01")]\n'),
}
PRE = ["", "-- a comment\n", "/- a block\ncomment -/\n", "/-! A module doc that mentions\ntheorem not_here : True := trivial -/\n"]
IN = ["", "open Nat in\n", "set_option maxHeartbeats 400000 in\n", "open Nat in\nset_option maxHeartbeats 400000 in\n"]
DECOYS = [
    "example : True := trivial\n",
    "/-- An example. -/ example : True := trivial\n",
    "/-- Documented.\n-/\nexample : True := trivial\n",
    "-- theorem dead : True := trivial\n",
    "/- theorem dead2 : True := trivial -/\n",
    "attribute [simp] Nat.add_zero\n",
]


def block(rng: random.Random, n: int, indent: str = "", in_mutual: bool = False, kind: str = "") -> tuple[str, str, str]:
    """One declaration: (original text, expected credited text, 'credited' | 'already' | 'other')."""
    kind = kind or rng.choice(
        ["theorem", "theorem", "lemma", "def", "def", "abbrev", "instance", "structure", "inductive", "class", "opaque"]
    )
    name = f"d{n}"
    body = BODIES[kind].format(n=name)
    mods = ""
    if kind in ("theorem", "lemma", "def", "abbrev"):
        mods = rng.choice(
            ["", "", "private ", "protected ", "private\n"] + (["noncomputable "] if kind in ("def", "abbrev") and not in_mutual else [])
        )
    attr_same, attr_own = "", ""
    if kind in ("theorem", "lemma", "def", "abbrev", "instance") and rng.random() < 0.5:
        s, o = ATTRS[rng.choice(list(ATTRS))]
        if s and rng.random() < 0.5:
            attr_same = s
        else:
            attr_own = o
    if mods == "private\n" and attr_same:  # a modifier on its own line: attributes go on their own lines above it
        attr_own, attr_same = attr_same.rstrip() + "\n", ""
    tc = rng.choice(["", "", " -- trailing"])  # after a docstring's `-/` or an attribute line
    if attr_own and tc:
        attr_own = attr_own.rstrip("\n") + tc + "\n"
    doc = rng.choice(
        [
            "none",
            "none",
            "single",
            "multi_own",
            "multi_blank",
            "multi_text",
            "already",
            "other",
            "inline",
            "closing",
            "closing_text",
            "doc_attrs",
        ]
    )
    if doc in ("inline", "closing", "closing_text") and (attr_own or mods == "private\n"):
        doc = "single" if doc == "inline" else "multi_text"
    if doc == "doc_attrs" and not attr_own:
        doc = "none"
    gap = "" if in_mutual or doc in ("inline", "closing", "closing_text", "doc_attrs") else rng.choice(["", "", "\n", "-- note\n"])
    pre = "" if in_mutual else rng.choice(PRE) + "\n" * rng.randint(0, 2)
    inn = "" if in_mutual else rng.choice(IN)

    def ind(s: str) -> str:
        return "".join(indent + l if l.strip() else l for l in s.splitlines(True))

    lead, rest = ind(attr_own), ind(gap) + ind(f"{attr_same}{mods}{kind} {body}\n")
    decl = lead + rest
    C = f"{indent}{CREDIT}"
    d1, d2 = f"{indent}/-- Doc for {name}.", f"{indent}More about {name}."
    if doc == "none":
        orig = decl
        exp = f"{indent}/-- {CREDIT} -/\n{decl}" if lead else f"{ind(gap)}{indent}/-- {CREDIT} -/\n{rest[len(ind(gap)) :]}"
    elif doc == "single":
        orig, exp = f"{d1} -/{tc}\n{decl}", f"{d1}\n\n{C} -/{tc}\n{decl}"
    elif doc == "multi_own":
        orig, exp = f"{d1}\n{d2}\n{indent}-/{tc}\n{decl}", f"{d1}\n{d2}\n\n{C}\n{indent}-/{tc}\n{decl}"
    elif doc == "multi_blank":
        orig, exp = f"{d1}\n\n{indent}-/{tc}\n{decl}", f"{d1}\n\n{C}\n{indent}-/{tc}\n{decl}"
    elif doc == "multi_text":
        orig, exp = f"{d1}\n{d2} -/{tc}\n{decl}", f"{d1}\n{d2}\n\n{C} -/{tc}\n{decl}"
    elif doc == "already":
        orig = exp = f"{d1}\n\n{C} -/{tc}\n{decl}"
    elif doc == "other":
        orig = exp = f"{d1}\n\n{indent}{OTHER} -/{tc}\n{decl}"
    elif doc == "inline":
        orig, exp = f"{d1} -/ {decl.lstrip()}", f"{d1}\n\n{C} -/ {decl.lstrip()}"
    elif doc == "closing":
        orig, exp = f"{d1}\n{d2}\n{indent}-/ {decl.lstrip()}", f"{d1}\n{d2}\n\n{C}\n{indent}-/ {decl.lstrip()}"
    elif doc == "closing_text":
        orig, exp = f"{d1}\n{d2} -/ {decl.lstrip()}", f"{d1}\n{d2}\n\n{C} -/ {decl.lstrip()}"
    else:  # doc_attrs: the docstring's line carries (or opens) the attributes
        orig, exp = f"{d1} -/ {attr_own.rstrip()}\n{rest}", f"{d1}\n\n{C} -/ {attr_own.rstrip()}\n{rest}"
    return pre + inn + orig, pre + inn + exp, {"already": "already", "other": "other"}.get(doc, "credited")


def generate(rng: random.Random, decls: int) -> tuple[str, str, dict]:
    """A file: header, then `decls` declarations with decoys and the odd mutual block between."""
    orig, exp = "import Mathlib\n\nnamespace Gen\n\n", "import Mathlib\n\nnamespace Gen\n\n"
    counts = {"credited": 0, "already": 0, "other": 0}
    n = 0
    while n < decls:
        if rng.random() < 0.15:
            d = rng.choice(DECOYS)
            orig += d + "\n"
            exp += d + "\n"
            continue
        if rng.random() < 0.12:  # Lean refuses a mutual block mixing theorems and definitions
            mk = rng.choice(["theorem", "def"])
            o1, e1, k1 = block(rng, n, "  ", True, mk)
            o2, e2, k2 = block(rng, n + 1, "  ", True, mk)
            orig += f"mutual\n{o1}{o2}end\n\n"
            exp += f"mutual\n{e1}{e2}end\n\n"
            counts[k1] += 1
            counts[k2] += 1
            n += 2
            continue
        o, e, k = block(rng, n)
        orig += o + "\n"
        exp += e + "\n"
        counts[k] += 1
        n += 1
    return orig + "end Gen\n", exp + "end Gen\n", counts


class AttributeProperties(unittest.TestCase):
    def test_generated_files(self):
        rng = random.Random(20260923)
        d = Path(tempfile.mkdtemp())
        for i in range(250):
            orig, exp, counts = generate(rng, rng.randint(3, 14))
            p = d / f"F{i}.lean"
            p.write_text(orig, encoding="utf-8")
            st = attribute.attribute_file(p, CREDIT, set(attribute.KINDS), False)
            self.assertEqual(p.read_text(encoding="utf-8"), exp, f"file {i}\n--- original ---\n{orig}")
            self.assertEqual(
                (st["credited"], st["already"], len(st["other"])), (counts["credited"], counts["already"], counts["other"]), f"file {i}"
            )
            st2 = attribute.attribute_file(p, CREDIT, set(attribute.KINDS), False)
            self.assertEqual(p.read_text(encoding="utf-8"), exp, f"file {i}: second run changed the file")
            self.assertEqual(st2["credited"], 0, f"file {i}: second run credited again")
            self.assertEqual(st2["already"], counts["credited"] + counts["already"], f"file {i}")


if __name__ == "__main__":
    unittest.main()
