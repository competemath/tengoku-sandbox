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

/-- a capped raw node count: enough to know whether a term has at least `cap` nodes -/
partial def sizeAtLeast (cap : Nat) (e : Expr) (acc : Nat := 0) : Nat :=
  if acc ≥ cap then acc else
  match e with
  | .app f a => sizeAtLeast cap a (sizeAtLeast cap f (acc + 1))
  | .lam _ t b _ | .forallE _ t b _ => sizeAtLeast cap b (sizeAtLeast cap t (acc + 1))
  | .letE _ t v b _ => sizeAtLeast cap b (sizeAtLeast cap v (sizeAtLeast cap t (acc + 1)))
  | .mdata _ b | .proj _ _ b => sizeAtLeast cap b (acc + 1)
  | _ => acc + 1

/-- binder names and binder info erased, universe parameters numbered by position, mdata dropped. Through `Core.transform`, whose
cache keeps the term's sharing: a proof term is a DAG, and rebuilding it node by node without a cache is exponential (the first
version of this did that over every theorem of the environment and exhausted a 7 GB runner). -/
def canonProof (lps : List Name) (e : Expr) : MetaM Expr := do
  let e := e.instantiateLevelParams lps ((List.range lps.length).map fun i => .param (Name.num .anonymous i))
  Core.transform e (post := fun e => return .done <| match e with
    | .lam _ t b _ => .lam .anonymous t b .default
    | .forallE _ t b _ => .forallE .anonymous t b .default
    | .letE _ t v b _ => .letE .anonymous t v b false
    | .mdata _ b => b
    | e => e)

def lineage (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  -- the index: fingerprint hash -> theorems, over the whole environment
  let mut index : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let .thmInfo t := ci | continue
    unless okName n do continue
    if t.value.approxDepth < 3 then continue
    let fp ← canonProof t.levelParams (mkApp t.type t.value)  -- the statement and the proof together: `rfl` proves many things
    if sizeAtLeast MIN fp < MIN then continue
    index := index.insert fp.hash ((index.getD fp.hash #[]).push n)
  let mut out := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo t := ci | continue
    unless okName n do continue
    let fp ← canonProof t.levelParams (mkApp t.type t.value)
    if sizeAtLeast MIN fp < MIN then continue
    let mut others := #[]
    for k in index.getD fp.hash #[] do
      if k == n then continue
      let some (.thmInfo t') := env.find? k | continue
      if (← canonProof t'.levelParams (mkApp t'.type t'.value)) == fp then others := others.push k
    if others.isEmpty then continue
    let seedOnes := others.filter (isSeedOrCore c env)
    let sev := if !(c.seed.isPrefixOf m) && !seedOnes.isEmpty then "warn" else "info"
    let show_ := (others.toList.take 5).map fun k => s!"{k} ({(moduleOf env k).getD `_})"
    out := out.push { check := "lineage", severity := sev, module := m, name := n, line := ← lineOf n,
                      detail := (if sev == "warn" then "the proof is a seed theorem's, verbatim: " else "the same proof, verbatim, as: ") ++ ", ".intercalate show_ ++ (if others.size > 5 then s!" and {others.size - 5} more" else "") ++ s!" (at least {MIN} nodes)" }
  return out

end Jinshi
