/-
decide — a proven statement, computed again (docs/jinshi.md, head K). A closed statement that has a `Decidable` instance can be
evaluated: `Decidable.decide stmt` reduces to `true` or `false` by Lean's own reduction, with no proof involved. A theorem whose
statement reduces to `false` is a theorem the kernel accepted for a false claim: a kernel bug, or a bypass of it. This is the
empirical member of the tawatur: not another type checker, but a computation that must agree with every one of them.

Only closed statements (no binders) with a synthesizable `Decidable` instance are tried, under a heartbeat cap; a statement that
does not evaluate within it is left alone (`info`, so the count is known). A statement that evaluates to `true` is counted, not listed.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

def decideOne (stmt : Expr) : MetaM (Option Bool) := do
  let inst ← synthInstance? (mkApp (mkConst ``Decidable) stmt)
  let some inst := inst | return none
  let e := mkApp2 (mkConst ``Decidable.decide) stmt inst
  let r ← withTransparency .all <| whnf e
  if r.isConstOf ``Bool.true then return some true
  if r.isConstOf ``Bool.false then return some false
  -- whnf may stop early on a stuck term: try the kernel-style full reduction once
  let r ← withTransparency .all <| reduce e (skipTypes := true) (skipProofs := true)
  if r.isConstOf ``Bool.true then return some true
  if r.isConstOf ``Bool.false then return some false
  return none

def decide (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out := #[]
  let mut tried := 0
  let mut confirmed := 0
  let mut stuck := 0
  for (m, n, ci) in selected c env do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    let ty := ci.type
    if ty.isForall || ty.hasLooseBVars || ty.hasMVar then continue
    unless (← isProp ty) do continue
    tried := tried + 1
    let verdict ← try
        withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 2000 * 1000 }) (decideOne ty)
      catch _ => pure none
    match verdict with
    | some true => confirmed := confirmed + 1
    | some false =>
      out := out.push { check := "decide", severity := "fail", module := m, name := n, line := ← lineOf n,
                        detail := "the statement is closed and decidable, and EVALUATES TO FALSE: a proof of it was accepted (a kernel bug, or a proof that bypassed the kernel)" }
    | none => stuck := stuck + 1
  if tried > 0 then
    out := out.push { check := "decide", severity := "info", module := (c.mods.headD .anonymous), name := .anonymous,
                      detail := s!"{tried} closed decidable statements tried: {confirmed} evaluate to true, {out.size} to false, {stuck} did not evaluate within the cap or have no Decidable instance" }
  return out

end Jinshi
