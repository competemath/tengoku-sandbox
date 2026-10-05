# isnad — the identity of a theorem

*Isnad* is the chain of transmission that vouches for a report. Here it is the name of Tengoku's theorem identity system: what a theorem *is*
(its statement, not its name or its proof), where it came from, and, later, how many independent chains agree on it (*tawatur*).
This document is the specification of format version 1 and of the tool that computes it. Nothing here changes a Lean file yet: no theorem
carries a tag today. What exists is the recipe, the program that computes it, and the checks that pin it.

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
| `shape` | the canonical form with every constant replaced by `c<order of first appearance>/<arity>`, numerals and strings masked, instance arguments dropped (the arguments at the instance-implicit parameters of the applied constant, a bound instance
variable included): the same shape is the same pattern over different objects (`a+b=b+a` over ℕ and over ℝ) |
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

## 4. What is not built yet

| Piece | State |
|---|---|
| the recipe, the executable `tengoku-isnad`, `scripts/isnad.py`, golden ids, laws, CI job | **done** (this change) |
| module block `@isnad1-module` (per-module list of ids, `mh` = hash of the list, `edit=` notice) | designed, not implemented |
| the tagger (writes tags with Lean's declaration ranges; stripping the tags must restore every module byte for byte) | not built |
| a `tag` PR class and the queue's recomputation (a tag that differs from the recomputed value ejects the PR) | not built |
| the bundle factory writes tags (born tagged); the sweep of the landed libraries; `src` backfill from the factory's exports | not built |
| `@isnad-runtime` (the dynamic layer: an external index joined per request, shown in the infoview and on the website) | not built |
| **tawatur** (a trusted theorem with four or more proofs whose dependency closures are disjoint after ignoring a forced set X) | not built; measured today: no statement has more than 3 proofs, so the set is empty |

Content classified by elimination: everything under `Tengoku/Seed/` is `seed`; a library built by the factory from another project is `translated`;
anything else (`competemath`, and `Tengoku/Native/` when it exists) is `novel`. Seeded and translated content is not edited for tags except by a
gated PR class; reorganising is allowed for novel content only, and the id does not change when a theorem moves (it never depends on its module).
