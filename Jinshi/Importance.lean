/-
importance — how much of the tree stands on each theorem (docs/jinshi.md). The proof of every declaration names the constants it
uses; counting, over the whole environment, how many proofs use each theorem gives its in-degree: a theorem used by five hundred
proofs is load-bearing, one used by none is a leaf. A finding on a load-bearing theorem outranks a hundred on leaves, so every
other examination's report is read against this one. Per examined theorem: `info` with the in-degree and the number of distinct
modules that use it; per examined module: the load-bearing theorems (in-degree ≥ LOAD) listed once, most used first.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-- in-degree ≥ this is load-bearing -/
def LOAD : Nat := 25

/-- the number of proofs/values of the whole environment that mention each constant, and the modules they come from (capped at 8 per constant) -/
def usage (env : Environment) : Std.HashMap Name (Nat × Array Name) := Id.run do
  let mut m : Std.HashMap Name (Nat × Array Name) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    -- `ConstantInfo.value?` is empty for imported theorems on this toolchain: match the record
    let some v := (match ci with | .thmInfo t => some t.value | .defnInfo d => some d.value | _ => none) | continue
    let here := (moduleOf env n).getD .anonymous
    for k in v.getUsedConstants do
      let (cnt, mods) := m.getD k (0, #[])
      let mods := if mods.size < 8 && !mods.contains here then mods.push here else mods
      m := m.insert k (cnt + 1, mods)
  return m

def importance (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let use := usage env
  let mut out := #[]
  let mut perModule : Std.HashMap Name (Array (Name × Nat)) := {}
  for (m, n, ci) in selected c env do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    let (cnt, mods) := use.getD n (0, #[])
    if cnt == 0 then continue  -- a leaf: nothing stands on it, nothing to say
    if cnt ≥ LOAD then
      perModule := perModule.insert m ((perModule.getD m #[]).push (n, cnt))
    out := out.push { check := "importance", severity := "info", module := m, name := n, line := ← lineOf n,
                      detail := s!"used by {cnt} proof(s) in {mods.size}{if mods.size ≥ 8 then "+" else ""} module(s)" ++ (if cnt ≥ LOAD then " — load-bearing" else "") }
  for (m, thms) in perModule.toList do
    let top := (thms.qsort fun a b => a.2 > b.2).toList.take 10
    out := out.push { check := "importance", severity := "info", module := m, name := .anonymous,
                      detail := s!"{thms.size} load-bearing theorem(s) (used by ≥ {LOAD} proofs): " ++ ", ".intercalate (top.map fun (n, k) => s!"{n} ({k})") }
  return out

end Jinshi
