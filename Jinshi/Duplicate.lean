/-
Jinshi, `duplicate`: the same statement proved twice (docs/jinshi.md). The identity of a theorem is its elaborated statement, not
its name (docs/isnad.md): two theorems whose types are the same up to binder names and universe parameter names prove one claim.
Once per run the whole environment (the seed included) is indexed by a cheap canonical hash of each theorem's type; then every
theorem of an examined module is looked up and each candidate confirmed by alpha-equivalence of the canonical types.

  warn  a theorem of a library proves again what the seed already has
  warn  a theorem of a library proves again what the same library already has (redundancy)
  info  two theorems of two libraries, or two of the seed, prove one statement: tawatur, several proofs of one claim
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-- the library a module belongs to: its first two components (`Tengoku.Seed`, `Tengoku.<Library>`, `JinshiFixtures.<Fixture>`) -/
def libraryOf (m : Name) : Name :=
  match m.components with
  | a :: b :: _ => a ++ b
  | _ => m

/-- the type with binder names, binder info, `let` flags and metadata erased, and the universe parameters renamed by position:
two theorems of one statement have equal canonical types (`==` on `Expr` is alpha-equivalence) and equal hashes -/
partial def canonType (levelParams : List Name) (type : Expr) : Expr :=
  go (type.instantiateLevelParams levelParams ((List.range levelParams.length).map fun i => Level.param (Name.num .anonymous i)))
where
  go : Expr → Expr
    | .forallE _ t b _ => .forallE .anonymous (go t) (go b) .default
    | .lam _ t b _ => .lam .anonymous (go t) (go b) .default
    | .letE _ t v b _ => .letE .anonymous (go t) (go v) (go b) false
    | .app f a => .app (go f) (go a)
    | .mdata _ b => go b
    | .proj s i b => .proj s i (go b)
    | e => e

def canonOf (ci : ConstantInfo) : Expr := canonType ci.levelParams ci.type

/-- `hash → the theorems of the whole environment whose canonical type has that hash` (names only: the environment is large) -/
def duplicateIndex (env : Environment) : Std.HashMap UInt64 (Array Name) := Id.run do
  let mut idx : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    let h := (canonOf ci).hash
    idx := idx.insert h ((idx.getD h #[]).push n)
  return idx

def duplicate (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let idx := duplicateIndex env
  let mut out := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    let mine := canonOf ci
    let twins := ((idx.getD mine.hash #[]).filter fun k => k != n && (env.find? k).any fun kci => canonOf kci == mine).qsort (·.toString < ·.toString)
    if twins.isEmpty then continue
    let selfSeed := c.seed.isPrefixOf m
    let lib := libraryOf m
    let show_ (k : Name) := s!"`{k}` ({(moduleOf env k).getD `_})"
    let ofSeed := twins.filter fun k => isSeedOrCore c env k
    let ofLib := twins.filter fun k => !isSeedOrCore c env k && (moduleOf env k).any (libraryOf · == lib)
    let others := twins.filter fun k => !ofSeed.contains k && !ofLib.contains k
    let more (xs : Array Name) := if xs.size > 5 then s!" and {xs.size - 5} more" else ""
    let names (xs : Array Name) := ", ".intercalate ((xs.toList.take 5).map show_) ++ more xs
    let mut parts := #[]
    let mut severity := "info"
    if !ofSeed.isEmpty then
      if selfSeed then parts := parts.push s!"tawatur: the seed proves this statement again as {names ofSeed}"
      else
        severity := "warn"
        parts := parts.push s!"proves again what the seed already has: {names ofSeed}"
    if !ofLib.isEmpty then
      if selfSeed then parts := parts.push s!"tawatur: the seed proves this statement again as {names ofLib}"
      else
        severity := "warn"
        parts := parts.push s!"the same library proves this statement again as {names ofLib} (redundancy)"
    if !others.isEmpty then
      parts := parts.push s!"tawatur: the same statement is also proved by {names others}"
    out := out.push { check := "duplicate", severity, module := m, name := n, line := ← lineOf n,
                      detail := "; ".intercalate parts.toList }
  return out

end Jinshi
