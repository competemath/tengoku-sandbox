# The content lint of a bundle

Compiling Lean runs code, so a bundle's modules pass an allow-list (`scripts/ci/allowlist.py`) before the tree takes them: every command is a known-inert one,
every attribute and `set_option` is on a list, and the words that run code or trust the compiler are refused wherever they appear. The repository variable
`TENGOKU_INTAKE_LINT` picks one of three readings (the factory cuts all three bundles, `scripts/bump/bundle.py`; the gate and the queue read the variable):

| Mode | Adds to the allow-list | Why it is safe to add |
|---|---|---|
| `strict` | nothing | |
| `proposed` | the notation commands (`notation`, `notation3`, `infix`, `infixl`, `infixr`, `prefix`, `postfix`), `scoped` or `local` only | each is a rewrite rule that elaborates a term; none runs the library's code |
| `wide` | also the macro family (`macro`, `macro_rules`, `syntax`, `declare_syntax_cat`); `macro` and `syntax` `scoped` or `local` only | a macro runs in Lean's pure macro monad, which cannot reach IO; the words that could (`unsafe`, `IO.`, `run_cmd`, `#eval`, `elab`, `initialize`, `implemented_by`, `extern`, `native_decide`, `axiom`, `opaque`) stay refused wherever they appear, in a quotation too |

The merge queue's own content lint (`scripts/ci/lint_banked.py`) reads the same variable the same way: notation commands in `proposed` and `wide`, the macro family in
`wide` only, `elab` and `elab_rules` in no mode.

**A global notation is refused in every mode.** A `notation`, `infix`, `prefix`, `postfix`, `notation3` (and in `wide` a `macro` or `syntax`) that is not `scoped` or `local` changes how every other
module of the tree parses, whatever library it is in: lean-pool's `prefix:80 "-" => complement` made `-(3 * x)` on the reals fail on every Leak service ("Ambiguous term"), and the atoms of
a global notation, syntax or macro (`v`, `ω`, `na`) became reserved tokens of the whole tree (`fun v => …`: "unexpected token 'v'"). Where a mode allows these commands it allows them with
`scoped` or `local` in front, and nothing else; the factory scopes them before it cuts a bundle (`scripts/bump/scope_rewrite.py`), and `scripts/generate.py` scopes the modules it writes
(`scripts/scope_notation.py`: `scoped` in front of the command, `open scoped <Namespace>` where the library uses it, and an error when a command cannot be scoped or when the gate's own check still finds a global one afterwards,
so a leak stops the generator instead of reaching the tree). The lint reads every occurrence of the keyword, not the start of a line (Lean needs no line break between commands: `def a := 1 prefix:80 "-" => f`, `private infix …`, `open Nat in notation …`); a keyword is a token of Lean's, never an identifier, so a word in code is a command, and `scoped`, `local` or Mathlib's `scoped[NS]` directly before it is what makes it pass. The check also reads Lean syntax quotations: a quoted keyword is not an active command, but it is not exempt. Names (`List.prefix`, `«prefix»`), comments and strings are not commands. For a changed module, a global command counts when it is on an added line or when the module has more of them than the base had (deleting the `scoped` line in front of an unchanged `notation` makes it global). A PR that makes an existing
notation `scoped` or `local` (the scope-fix class, or a regeneration of a generated library: modules modified in place, the old line with the word in front, nothing else) is not a new declaration.

In every mode a word at column 0 starts a command only if it is a command keyword of the tree's Lean (`schemas/command-keywords.json`, the leading tokens of
Lean's `command` parser category, read from Lean itself). Any other word there continues the command above (`termination_by`, `decreasing_by`, `by`, `fun`, a
proof term), and Lean refuses it if it does not parse. The old reading took every unknown word for a command and refused 10,937 of lean-pool's 79,378
Gate-2-passed theorems for it. A few commands that carry no code and change no statement are allowed (`grind_pattern`, `suppress_compilation`,
`unsuppress_compilation`, `recommended_spelling`, `deprecated_module`, and `meta` as a modifier).

What stays refused in every mode, whatever it would cost: `elab`, `elab_rules`, `initialize`, `run_cmd` (code in the elaborator), `#eval` and the other `#`
commands (diagnostics are cut from a bundle, never kept), `unsafe`/`partial` declarations, `IO.`/`System.`, `implemented_by`/`extern`, `native_decide`,
`axiom`, `opaque`, simprocs. They cost at most half a percent of the theorems on the two largest libraries and each is a real way to run or trust code.

The tests are `scripts/ci/tests/test_lint_modes.py` (each mode on each family; what runs code and a global notation are refused in all three, a macro cannot smuggle a forbidden word
in a quotation) and `scripts/tests/test_scope_notation.py` (the generator's pass). The list of command keywords is the tree's: `tools/CommandKeywords.lean` prints it from Lean, the nightly build compares it with the file and annotates a difference
(it never blocks the cache), and `kw=$(mktemp schemas/.kw.XXXXXX) && lake env lean --run tools/CommandKeywords.lean | python3 scripts/ci/cmdkw_check.py --emit > "$kw" && mv "$kw" schemas/command-keywords.json` regenerates it when the seed changes.
