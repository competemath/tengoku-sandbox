"""allowlist.py — what a record that the tree will compile may contain: an allow-list, not a list of known dangers.

A staging or trusted record is pasted into a module that CI compiles and every Leak service imports, and compiling
Lean runs code (commands, attributes and elaborators can execute anything). So a record passes only if everything in
it is known to be inert (comments and strings aside: scripts/ci/lean_lex.py):
- each top-level command starts with an allowed keyword (after its attributes and modifiers); a line that starts
  with a symbol continues the command above it (`| 0 => …`);
- no code-running keyword appears anywhere, indented or not (`initialize`, `elab`, `#eval`, `native_decide`, …);
- every attribute is one that annotates data or asks the tree's own tactics to use a lemma, never one that registers
  code of the record's to run later (norm_num/positivity extensions, simprocs, elaborators, native implementations);
- every set_option is on schemas/allowed-options.json.
"""

from __future__ import annotations

import re

from lean_lex import code_only

COMMANDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
    "class",
    "structure",
    "inductive",
    "namespace",
    "section",
    "end",
    "variable",
    "universe",
    "open",
    "set_option",
    "attribute",
    "omit",
    "include",
    "alias",
    "export",
    "deriving",
    "mutual",
    "noncomputable",
    "private",
    "protected",
    "where",  # auxiliary definitions of the declaration above
    # Mathlib commands that configure or document, running the tree's code on the record's data
    "initialize_simps_projections",
    "irreducible_def",
    "add_decl_doc",
    "library_note",
    "recall",
    "assert_not_exists",
}
MODIFIERS = {"private", "protected", "noncomputable", "nonrec", "scoped", "local", "public"}
# attributes that register nothing of the record's own to run: simp sets, lemma tags for the tree's tactics,
# generators whose code is the tree's (to_additive, simps, reassoc), documentation tags
ATTRIBUTES = {
    "simp",
    "to_additive",
    "inherit_doc",
    "to_dual",
    "reassoc",
    "norm_cast",
    "fun_prop",
    "ext",
    "gcongr",
    "deprecated",
    "grind",
    "to_fun",
    "elab_as_elim",
    "stacks",
    "mfld_simps",
    "continuity",
    "mono",
    "elementwise",
    "nontriviality",
    "push",
    "bound",
    "rclike_simps",
    "trans",
    "aesop",
    "symm",
    "instance",
    "refl",
    "alias_in",
    "measurability",
    "to_app",
    "nolint",
    "congr",
    "coassoc_simps",
    "induction_eliminator",
    "push_cast",
    "closedness",
    "inclusion_op",
    "compactness",
    "wikidata",
    "simps",
    "cases_eliminator",
    "arith_mult",
    "expose",
    "parity_simps",
    "higher_order",
    "dlmf",
    "hypothesis_op",
    "functor_norm",
    "integral_simps",
    "elab_without_expected_type",
    "int_toBitVec",
    "rify_simps",
    "qify_simps",
    "reducible",
    "irreducible",
    "semireducible",
    "inline",
    "specialize",
    "match_pattern",
    "coe",
    "field_simps",
    "ring_nf",
    "zify_simps",
    "pp_nodot",
    "nosimp",
    "always_inline",
    "macro_inline",
    "noinline",
    "reducible_on_demand",
    "local",
    "scoped",
    "simps!",
    "norm_num_rules",
}
# anywhere, whole word: each runs code while the tree compiles, or trusts the compiler
FORBIDDEN_WORDS = [
    "import",
    "initialize",
    "builtin_initialize",
    "elab",
    "elab_rules",
    "macro",
    "macro_rules",
    "syntax",
    "declare_syntax_cat",
    "notation",
    "notation3",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "run_cmd",
    "run_tac",
    "run_elab",
    "by_elab",
    "opaque",
    "axiom",
    "implemented_by",
    "extern",
    "unsafeCast",
    "unsafeIO",
    "unsafeBaseIO",
    "simproc",
    "dsimproc",
]
_WORD = re.compile(r"(?<![\w.'!?])(" + "|".join(map(re.escape, FORBIDDEN_WORDS)) + r")(?![\w'!?])")
# `#s` is a term (Mathlib's notation for a finite set's size), so a `#word` is refused where a command stands, at the
# start of a line, and the commands that run or reach anything are refused wherever they appear
# `unsafe` and `partial` as declaration modifiers (aesop's `unsafe 50%` rules and `partial` in prose stay allowed)
_UNSAFE_DECL = re.compile(
    r"(?<![\w.'])(unsafe|partial)\s+(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|opaque|inductive|structure|class|example)\b|^[ \t]*(unsafe|partial)\b",
    re.M,
)
# trusting the compiler, also as a component of a longer name: native_decide leaves auxiliary axioms such as
# `Foo._native.native_decide.ax_12`, and a proof term that cites one trusts compiled code just the same
_TRUST = re.compile(r"(?<![\w'!?])(native_decide|ofReduceBool|reduceBool|trustCompiler)(?![\w'!?])")
_HASH_COMMANDS = [
    "eval",
    "exec",
    "guard",
    "guard_expr",
    "guard_msgs",
    "print",
    "check",
    "check_failure",
    "reduce",
    "exit",
    "synth",
    "simp",
    "norm_num",
    "conv",
    "time",
    "help",
    "lint",
    "find",
    "where",
    "count_heartbeats",
    "explode",
    "leansearch",
    "loogle",
    "moogle",
    "min_imports",
    "long_names",
    "adaptation_note",
    "with_exporting",
    "sample",
    "test",
]
_HASH = re.compile(r"(?<![\w'])#(?:" + "|".join(_HASH_COMMANDS) + r")(?![\w'!?])|^[ \t]*#[A-Za-z_]\w*", re.M)
_IO = re.compile(r"(?<![\w.])(?:IO|System)\.[A-Za-z]\w*")
_ATTR_OPEN = re.compile(r"@\[|^[ \t]*(?:(?:scoped|local)[ \t]+)?attribute[ \t]*\[", re.M)
_SET_OPTION = re.compile(r"\bset_option\s+([A-Za-z_][\w.]*)")
_LEAD = re.compile(r"^[^\s(\[{:⦃]+")


def _attribute_blocks(code: str):
    for m in _ATTR_OPEN.finditer(code):
        i, depth = m.end(), 1
        while i < len(code) and depth:
            depth += {"[": 1, "]": -1}.get(code[i], 0)
            i += 1
        yield code[m.end() : i - 1], m.start(), i


def _attribute_names(block: str) -> list[str]:
    parts, cur, depth = [], "", 0
    for ch in block + ",":
        depth += {"(": 1, "[": 1, "{": 1, ")": -1, "]": -1, "}": -1}.get(ch, 0)
        if ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    names = []
    for p in parts:
        w = p.lstrip("-").split()
        while w and w[0] in ("scoped", "local"):
            w = w[1:]
        if w:
            names.append((w[0].rstrip("↓←!"), p))  # simp↓, simp←, simps!: the same attribute
    return names


def violations(text: str, allowed_options: set[str]) -> list[str]:
    code = code_only(text)
    out: list[str] = []
    for m in _WORD.finditer(code):
        out.append(f"`{m.group(1)}` runs code while the tree compiles (or trusts the compiler)")
    for m in _TRUST.finditer(code):
        out.append(f"`{m.group(1)}` trusts the compiler")
    for m in _UNSAFE_DECL.finditer(code):
        out.append(f"`{m.group(1) or m.group(2)}` declarations are not for records")
    for m in _HASH.finditer(code):
        out.append(f"`{m.group(0).strip()}`: no # commands in a record")
    for m in _IO.finditer(code):
        out.append(f"`{m.group(0)}`: IO and System are not for records")
    stripped = code
    for block, start, end in _attribute_blocks(code):
        for name, full in _attribute_names(block):
            if name not in ATTRIBUTES:
                out.append(f"attribute `{name}` is not on the allow-list")
            elif name == "aesop" and re.search(r"\btactic\b", full):
                out.append("an aesop `tactic` rule runs the record's own code in later proofs")
        stripped = stripped[:start] + " " * (end - start) + stripped[end:]
    for opt in _SET_OPTION.findall(code):
        if opt not in allowed_options:
            out.append(f"set_option {opt} is not on the allowlist")
    for line in stripped.split("\n"):
        if not line.strip() or line[0].isspace():
            continue
        m = _LEAD.match(line)
        if not m or not re.match(r"[A-Za-z_]", m.group(0)):
            continue  # a symbol at column 0 continues the command above (`| 0 => …`, `⟨…⟩`)
        words = line.split()
        while words and words[0] in MODIFIERS:
            words = words[1:]
        lead = _LEAD.match(words[0]).group(0) if words else ""
        if lead and lead not in COMMANDS:
            out.append(f"`{lead}` does not start an allowed command")
    return list(dict.fromkeys(out))
