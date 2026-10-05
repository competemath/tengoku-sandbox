# isnad — the identity of a theorem

*Isnad* is the chain of transmission that vouches for a report. Here it is the name of Tengoku's theorem identity system: what a theorem *is*
(its statement, not its name or its proof), where it came from, and, later, how many independent chains agree on it (*tawatur*).
This document is the specification of format version 1 and of the tools that compute it and write it down. No theorem of the tree carries a tag
yet: what exists is the recipe, the program that computes it, the tagger that writes the tags, and the checks that pin all three.

## 1. What is computed

For a theorem `T`, from the **elaborated statement** (the type of the constant, after elaboration, as it is in the compiled environment):

```
id    = <kind>.<hyps>h<vars>v.s<size>.<sig>           eq.1h3v.s4.01215b3d171d
shape = sha256(shape form)[:8]                        3fa9c1d2
vocab = sha256(vocabulary)[:8]                        b27e40a1
```

| Part | Meaning |
|---|---|
| `kind` | what `T` concludes: `eq` (=), `le` (≤ ≥), `lt` (< >), `ne`, `iff`, `ex` (∃), `and`, `or`, `not`; any other head constant is the last component of its name, lower-cased, letters and digits only, at most 8 characters (never a `.`); `var`, `sort`, `other` for non-constant heads |
| `hyps` / `vars` | binders whose type is a proposition / all other binders; typeclass binders are not counted. A heuristic and part of the recipe: a binder whose type is a propositional *variable* (`hp : p`) counts as a variable |
| `size` | `floor(log2 n)` of the number of expression nodes `n`: `s4` is 16 to 31 nodes |
| `sig` | the first 12 hex digits of the **sha256 of the canonical form** (below) |
| `shape` | the canonical form with every constant replaced by `c<order of first appearance>/<arity>`, numerals and strings masked, instance arguments dropped (the arguments at the instance-implicit parameters of the applied constant, a bound instance variable included): the same shape is the same pattern over different objects (`a+b=b+a` over ℕ and over ℝ) |
| `vocab` | the sorted, distinct, quoted names of the constants mentioned, without `Eq And Or Not Iff Exists True False OfNat.ofNat Ne` and without instances: the same vocab is the same objects arranged differently |

The tag, the last line of a theorem's docstring (machine-owned, plain ASCII, no `-/`, no `/-`):

```
@isnad1 id=eq.1h3v.s4.01215b3d171d from=seed src=0 shape=3fa9c1d2 vocab=b27e40a1
@isnad1 id=eq.1h3v.s4.01215b3d171d from=translated src=- shape=3fa9c1d2 vocab=b27e40a1
```

`@isnad1` is the version of the **recipe**: if the canonical form ever changes, new lines say `@isnad2` and old lines stay valid for their own version
(a reader refuses a version whose recipe it does not implement: it could not say what was verified).
`from` is `seed` (upstream code under `Tengoku/Seed/`), `translated` (a verified translation of another library) or `novel` (new content written
for Tengoku, today the `competemath` records; later `Tengoku/Native/`). `src` is one claim with `from`: `0` for a theorem that is not a translation (`seed`, `novel`), and for a translation (`translated`) `-` when its source side
is not available, or the 12-digit `sig` of the source statement (the same canonical form applied to the original; equal to this theorem's own `sig` when
the statement was kept exactly). `from=translated src=0` and `from=seed src=-` are refused. Axioms are **not** in the tag: they depend on the proof, an identity is a passport (they go to the index).

## 2. The canonical form (version 1)

An S-expression, a pure function of the elaborated statement; sha256 is computed by `scripts/isnad.py`, never by Lean (`String.hash` is not a
specification). Every node is an atom or `(head child…)`, children separated by one space:

| Expression | Written |
|---|---|
| bound variable | `v<de Bruijn index>` (binder names do not enter) |
| sort | `(T <level>)` |
| constant | its cleaned name as a quoted string, `"Nat.add_comm"`, followed by `{level …}` when it has universe levels |
| application | `(<head> <arg>…)`; a proof term (an application of a theorem, `Eq.refl`, `rfl`, `of_decide_eq_true`, `Eq.mpr`, `Eq.mp`) is `⊢` |
| `λ`, `Π`, `let` | `(λ T B)`, `(Π T B)`, `(L T V B)` |
| projection | `(π<i> "<structure>" e)` |
| literal | `n<number>`, `s"<escaped string>"` |
| universe level | `0`, `(S l)`, `(M a b)`, `(I a b)`, `p<order of first appearance>` (universe parameter names do not enter) |

Names are cleaned (macro scopes removed; a `private` constant keeps its whole name, `_private.<Module>.0.<name>`: two private constants called `p` in two
modules are different constants, and a statement that mentions one is module-specific by nature) and **quoted**: every atom is self-delimiting, so no two different statements
share a canonical string because names and separators run together (the first lab recipe wrote `Π(A.B.C)`, which reads two ways).

What does **not** enter: the theorem's own name, its namespace and module, binder names and binder info (implicit or explicit), universe parameter
names, docstrings and the proof. What does: every constant the statement mentions, library-local definitions included, with its universe levels
and, for instances, the instance terms as elaborated.

Which declarations: theorems (`thmInfo`) whose name is not internal, has no macro scopes, and does not start with `eq_`, `proof_`, `match_`,
`sizeOf_`, `_` or equal `injEq`.

### Known limits (they are part of v1, not bugs)

- **Instance paths.** Two statements that mean the same but elaborated through different instance paths (`mul_inv_cancel_right` in Mathlib and the same
  sentence written in a fresh file) have different `sig` and the same `shape` and `vocab`. That is what `shape` and `vocab` are for.
- **Universe levels are not normalised**: `max u v` and `max v u` differ.
- **`hyps`/`vars` is a heuristic** (a hypothesis whose type is a propositional variable counts as a variable).
- An identity says which statement this is. It says nothing about whether the proof is good, or the statement true.

## 3. Repeat it yourself

Anyone with the pinned toolchain gets the same bytes. In a clone of this repository (no cache, no tree build needed: the program imports only Lean):

```bash
lake build tengoku-isnad                          # one executable; it imports only Lean
python3 scripts/isnad.py selftest                 # the golden ids of Lean core theorems (tools/isnad/golden.tsv)
python3 scripts/isnad.py laws                     # renaming changes nothing, a different statement does: on real elaborated statements
python3 scripts/isnad.py explain 'eq.1h3v.s4.01215b3d171d'     # decode an id or a whole tag, offline
python3 scripts/isnad.py id --module Tengoku.Seed.Logic.Basic  # the ids of a module's theorems (needs the module built: scripts/cache.sh get)
python3 scripts/isnad.py verify '@isnad1 id=… from=… src=… shape=… vocab=…' --module M --name T   # recompute one tag
```

`selftest` and `laws` run in CI on every PR that touches the recipe (`pr-tests`, job `isnad`), from a clean checkout. The golden file holds theorems of
Lean's own core library, so it depends on neither Mathlib nor this tree, only on the toolchain; if the toolchain changes a statement, `selftest`
says so (and the right answer is a new recipe version, not a silent edit of the file).

`laws` runs the same code as the executable: the script is generated from the `BEGIN CANON … END CANON` block of `TengokuIsnad.lean`, so there is one
source of truth. The laws were also run on Leak IV (Lean 4.34.0-rc2) with a negative control: a law deliberately broken is reported.

### The tagger

`isnad.py tag` writes each theorem's tag into the file the theorem is written in, as the last line of its docstring (a theorem that has no docstring gets a
new one that holds only the tag):

```lean
/-- Addition of natural numbers is commutative.
@isnad1 id=eq.0h2v.s4.… from=seed src=0 shape=… vocab=…
-/
theorem Nat.add_comm …
```

```bash
python3 scripts/isnad.py tag --module Tengoku.Seed.Logic.Basic              # a dry run: what would be written, what is skipped and why
python3 scripts/isnad.py tag --module Tengoku.Seed.Logic.Basic --write
python3 scripts/isnad.py strip Tengoku/Seed/Logic/Basic.lean --write         # the tags out again (a directory: all its *.lean files)
python3 scripts/isnad.py tagtest                                             # the tagger on a real compile (CI)
```

*Where* a theorem is written is not guessed: Lean records the range of every declaration (its docstring and attributes included, and the declared name),
and `tengoku-isnad --ranges` prints them. The tagger reads text only to skip comments and strings, so a `/--` inside a string or a comment is never taken for a
docstring. It leaves a theorem alone, and says why, when the text at the name's position is not its name or the command starts inside an attribute (a theorem
a macro generated: `to_additive`'s twin, `ext_iff`), when its range is only its name (a structure's field, `ext`'s theorem), when several theorems start at one
command, when the file has Windows line endings, when a docstring is never closed, or when the command does not start its line. A twin has no place in the
source to carry a tag (its docstring is not copied from the original either: measured), so its id goes in the module's list instead. On ten real modules of
the tree (1,392 theorems: Mathlib's group, order, set and logic basics, and two of Carleson's) the tagger tags 997, leaves 383 twins, 11 fields and 1 other alone,
and every result passes the rule below. The tag text is the same for `from=seed` (anything under `Tengoku/Seed/`), `from=novel` (`Tengoku/Native/`) and `from=translated`
(every other library); `--origin` and `--src` override it.

The rule that makes it safe (`equivalent` in `scripts/isnad_tag.py`): after the tags are taken out of both versions, the code is byte for byte the same and every
docstring has the same words. Two things are allowed to differ: the whitespace in front of a docstring's closing `-/` (`/-- text -/` becomes
`/-- text` and the tag and `-/` on their own lines, and pure insertion cannot put it back), and a docstring with no words left, which goes with the tags (the one the
tagger made for a theorem that had none, or an empty `/-- -/`: they look the same once tagged). `tag --write` never writes a result that breaks the rule.

`tagtest` compiles `tools/isnad/tagger/Fixture.lean` (twelve theorems in the shapes that break naive taggers: one-line and many-line docstrings, an attribute
before or after the docstring, a nested comment inside a docstring, a dotted protected name, guillemets, unicode, indentation, a tag already there; and the shapes
it must leave alone: `ext`'s two theorems and the fields of a structure, one of them with a docstring of its own) and checks that
Lean's ranges are the ones pinned in `ranges.json`, that tagging, tagging again and stripping each leave every theorem's id, shape and vocab as they were
(the statements are compiled again after each step), that the second tag changes nothing, and that the stripped file is equivalent to the original. The unit tests
(`scripts/tests/test_isnad_tag.py`) run the same shapes on the pinned ranges, 300 random files, and every function of the tagger was checked against deliberately
broken versions of itself.

## 4. What is not built yet

| Piece | State |
|---|---|
| the recipe, the executable `tengoku-isnad`, `scripts/isnad.py`, golden ids, laws, CI job | **done** (this change) |
| module block `@isnad1-module` (per-module list of ids, `mh` = hash of the list, `edit=` notice) | designed, not implemented |
| the tagger (`tag`, `strip`, `tagtest`: writes tags with Lean's declaration ranges; stripping restores the code byte for byte) | **done**; not yet run on the tree |
| a `tag` PR class and the queue's recomputation (a tag that differs from the recomputed value ejects the PR) | not built |
| the bundle factory writes tags (born tagged); the sweep of the landed libraries; `src` backfill from the factory's exports | not built |
| `@isnad-runtime` (the dynamic layer: an external index joined per request, shown in the infoview and on the website) | not built |
| **tawatur** (a trusted theorem with four or more proofs whose dependency closures are disjoint after ignoring a forced set X) | not built; measured today: no statement has more than 3 proofs, so the set is empty |

Content classified by elimination: everything under `Tengoku/Seed/` is `seed`; a library built by the factory from another project is `translated`;
anything else (`competemath`, and `Tengoku/Native/` when it exists) is `novel`. Seeded and translated content is not edited for tags except by a
gated PR class; reorganising is allowed for novel content only, and the id does not change when a theorem moves (it never depends on its module).
