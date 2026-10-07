/-
lineage — the same proof, twice (docs/jinshi.md). A proof term with the names of its binders erased and its universe parameters
numbered is a fingerprint of HOW a theorem was proved. Two theorems with the same fingerprint were proved the same way: a copy
(a library's theorem whose proof is the seed's or another library's, character for character), or the same automation output.
For a theorem of a library whose proof is the proof of a seed theorem: `warn` (the proof was taken, with or without the statement:
provenance to record); the same proof in two libraries, or in two theorems of one library: `info`. Proofs of fewer than MIN
nodes are not fingerprinted: `rfl` is everybody's proof.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

def MIN : Nat := 12

/-- binder names and binder info erased, universe parameters numbered by position, mdata dropped -/
partial def canonProof (lps : List Name) (e : Expr) : Expr :=
  let e := e.instantiateLevelParams lps ((List.range lps.length).map fun i => .param (Name.num .anonymous i))
  let rec go : Expr → Expr
    | .lam _ t b _ => .lam .anonymous (go t) (go b) .default
    | .forallE _ t b _ => .forallE .anonymous (go t) (go b) .default
    | .letE _ t v b _ => .letE .anonymous (go t) (go v) (go b) false
    | .app f a => .app (go f) (go a)
    | .mdata _ b => go b
    | .proj s i b => .proj s i (go b)
    | e => e
  go e

def lineage (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  -- the index: fingerprint hash -> theorems, over the whole environment
  let mut index : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let .thmInfo t := ci | continue
    unless okName n do continue
    if t.value.approxDepth < 3 then continue
    let fp := canonProof t.levelParams (mkApp t.type t.value)  -- the statement and the proof together: `rfl` proves many things
    if fp.sizeWithoutSharing < MIN then continue
    index := index.insert fp.hash ((index.getD fp.hash #[]).push n)
  let mut out := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo t := ci | continue
    unless okName n do continue
    let fp := canonProof t.levelParams (mkApp t.type t.value)
    if fp.sizeWithoutSharing < MIN then continue
    let others := (index.getD fp.hash #[]).filter fun k => k != n &&
      (match env.find? k with | some (.thmInfo t') => canonProof t'.levelParams (mkApp t'.type t'.value) == fp | _ => false)
    if others.isEmpty then continue
    let seedOnes := others.filter (isSeedOrCore c env)
    let sev := if !(c.seed.isPrefixOf m) && !seedOnes.isEmpty then "warn" else "info"
    let show_ := (others.toList.take 5).map fun k => s!"{k} ({(moduleOf env k).getD `_})"
    out := out.push { check := "lineage", severity := sev, module := m, name := n, line := ← lineOf n,
                      detail := (if sev == "warn" then "the proof is a seed theorem's, verbatim: " else "the same proof, verbatim, as: ") ++ ", ".intercalate show_ ++ (if others.size > 5 then s!" and {others.size - 5} more" else "") ++ s!" (proof of {fp.sizeWithoutSharing} nodes)" }
  return out

end Jinshi
