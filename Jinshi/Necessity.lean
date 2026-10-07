/-
Jinshi — necessity: every hypothesis justified by a counterexample (docs/jinshi.md).

A theorem `∀ x…, H₁ → … → Hₙ → C` claims to need each Hᵢ. A hypothesis is JUSTIFIED when a concrete counterexample shows the
claim fails without it: values for the variables under which every other hypothesis holds and the conclusion fails. A theorem
whose every hypothesis is justified is exactly as general as it reads. A hypothesis that is neither used by the proof (the
structural test of unusedhyp, its complement) nor justified is one a reader must think about: the theorem may hold without it.

The search is small-domain enumeration, no proof involved: a variable of type `Nat` (0..4), `Int` (-2..2), `Bool`, `Fin k`
(k ≤ 8), `Prop` (True, False), `List Nat` or `List Bool` (length ≤ 2) takes each value of its domain; the assignments are
enumerated the smallest first (by the sum of the value indices, then in binder order; at most 2000 per theorem), and under each
one every hypothesis and the conclusion, now closed, are evaluated as `decide` does (Jinshi/Decide.lean: `Decidable.decide`
reduced by whnf under a heartbeat cap; no instance or no reduction, and the assignment is skipped). The assignments serve every
hypothesis at once: one under which exactly one hypothesis fails and the conclusion fails justifies that hypothesis; one under
which every hypothesis holds and the conclusion fails is a theorem that EVALUATES TO FALSE (`fail`, as in `decide`). A theorem
with a variable of any other type, more than 6 variables or more than 6 hypotheses, or a hypothesis that a later binder or the
conclusion mentions, is not examined, and says so. Instance-implicit binders are never hypotheses (the instance is synthesized
under each assignment). The seed is examined too: this examines proofs and statements, not a library's text.
JINSHI_NECESSITY_MAX caps the theorems examined per module (default 100).
-/
import Jinshi.Base
import Jinshi.Decide
open Lean Meta

namespace Jinshi

/-- an expression as a reader sees it, on one line, cut at `width` -/
private def shown (e : Expr) (width : Nat) : MetaM String := do
  let s ← try
      let s ← withOptions (fun o => pp.maxSteps.set (pp.proofs.set o false) 200) (ppExpr e)
      pure ((toString s).replace "\n" " ")
    catch _ => pure "?"
  return if s.length > width then String.ofList (s.toList.take width) ++ "…" else s

/-- `k : ty` as the reader writes it: `OfNat.ofNat ty k _` with the instance synthesized -/
private def numeral (ty : Expr) (k : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some ty, some (mkRawNatLit k), none]

/-- a variable's small domain: each value as a term and as the reader sees it; `none` for a type that has none -/
private def smallDomain (ty : Expr) : MetaM (Option (Array (Expr × String))) := do
  let ty ← instantiateMVars ty
  if ty.isConstOf ``Nat then
    return some ((List.range 5).toArray.map fun k => (mkNatLit k, toString k))
  if ty.isConstOf ``Bool then
    return some #[(mkConst ``Bool.false, "false"), (mkConst ``Bool.true, "true")]
  if ty == .sort .zero then
    return some #[(mkConst ``True, "True"), (mkConst ``False, "False")]
  if ty.isConstOf ``Int then
    let mut out := #[]
    for i in [(-2 : Int), -1, 0, 1, 2] do
      let pos ← numeral ty i.natAbs
      let e ← if i < 0 then mkAppOptM ``Neg.neg #[some ty, none, some pos] else pure pos
      out := out.push (e, toString i)
    return some out
  if let .app (.const ``Fin _) bound := ty then
    let some k ← (evalNat bound).run | return none
    if k > 8 then return none
    let mut out := #[]
    for i in [0:k] do
      out := out.push (← numeral ty i, toString i)
    return some out
  if let .app (.const ``List _) elem := ty then
    if elem.isConstOf ``Nat then
      let ls : List (List Nat) := [[], [0], [1], [0, 1], [1, 0], [2]]
      return some (ls.toArray.map fun l => (toExpr l, toString l))
    if elem.isConstOf ``Bool then
      let ls : List (List Bool) := [[], [true], [false], [true, false], [false, true]]
      return some (ls.toArray.map fun l => (toExpr l, toString l))
  return none

/-- the tuples of indices, the `i`-th below `sizes[i]`, whose sum is `s` -/
private partial def tuplesOfSum : List Nat → Nat → List (List Nat)
  | [], s => if s == 0 then [[]] else []
  | d :: rest, s => (List.range (min d (s + 1))).foldr (fun i acc => ((tuplesOfSum rest (s - i)).map (i :: ·)) ++ acc) []

/-- every tuple of indices, the smallest first (by the sum of the indices, then in binder order), at most `cap` -/
private def gradedTuples (sizes : List Nat) (cap : Nat) : Array (Array Nat) := Id.run do
  if sizes.any (· == 0) then return #[]
  let maxSum := sizes.foldl (fun a d => a + (d - 1)) 0
  let mut out := #[]
  for s in [0:maxSum + 1] do
    if out.size ≥ cap then break
    for t in tuplesOfSum sizes s do
      if out.size ≥ cap then break
      out := out.push t.toArray
  return out

/-- the positions of the outer binders of `ty` that the matching lambda body of `val` never mentions and that no later binder nor
the conclusion mentions: unusedhyp's structural test, by position -/
private partial def unusedPositions (ty val : Expr) (i : Nat) (acc : Array Nat) : Array Nat :=
  match ty, val.consumeMData with
  | .forallE _ _ tb _, .lam _ _ vb _ =>
    unusedPositions tb vb (i + 1) (if vb.hasLooseBVar 0 || tb.hasLooseBVar 0 then acc else acc.push i)
  | _, _ => acc

/-- a closed proposition evaluated as `decide` does, under its own heartbeat cap; `none` when it does not evaluate -/
private def evalClosed (p : Expr) : MetaM (Option Bool) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 200 * 1000 }) (decideOne p))
    (fun _ => pure none)

private inductive Binder where
  | var (name : Name) (dom : Array (Expr × String))
  | hyp (name : Name) (shown : String)
  | inst
  | unknown (name : Name) (shown : String)
  deriving Inhabited

/-- the findings on one theorem, as (severity, detail); empty when it has no hypothesis -/
private def examineOne (t : TheoremVal) : MetaM (Array (String × String)) :=
  forallTelescope t.type fun xs body => do
    let body ← instantiateMVars body
    let mut kinds : Array Binder := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let ty ← instantiateMVars decl.type
      let nm := decl.userName.eraseMacroScopes
      if decl.binderInfo == .instImplicit then kinds := kinds.push .inst
      else if ← (try Meta.isProp ty catch _ => pure false) then kinds := kinds.push (.hyp nm (← shown ty 120))
      else match ← (try smallDomain ty catch _ => pure none) with
        | some d => kinds := kinds.push (.var nm d)
        | none => kinds := kinds.push (.unknown nm (← shown ty 120))
    let hyps := (List.range xs.size).filter (fun i => kinds[i]! matches Binder.hyp _ _) |>.toArray
    if hyps.isEmpty then return #[]
    for k in kinds do
      if let .unknown nm ty := k then
        return #[("info", s!"not examined: variable `{nm} : {ty}` has no small domain (Nat, Int, Bool, Fin k with k ≤ 8, Prop, List Nat, List Bool)")]
    let vars := (List.range xs.size).filter (fun i => kinds[i]! matches Binder.var _ _) |>.toArray
    if vars.size > 6 then return #[("info", s!"not examined: {vars.size} variables (the cap is 6)")]
    if hyps.size > 6 then return #[("info", s!"not examined: {hyps.size} hypotheses (the cap is 6)")]
    -- a hypothesis that a later binder or the conclusion mentions: no value can stand for it
    for i in hyps do
      let .hyp nm _ := kinds[i]! | continue
      let h := xs[i]!.fvarId!
      let mut mentioned := body.containsFVar h
      for x in xs do
        if (← instantiateMVars (← x.fvarId!.getType)).containsFVar h then mentioned := true
      if mentioned then return #[("info", s!"not examined: the hypothesis `{nm}` is mentioned by a later binder or by the conclusion")]
    let hypName (i : Nat) : String := match kinds[i]! with | .hyp nm ty => s!"`{nm} : {ty}`" | _ => "?"
    let sizes := vars.toList.map fun i => match kinds[i]! with | .var _ d => d.size | _ => 0
    let mut justified : Array (Option (String × String)) := hyps.map fun _ => none
    let mut remaining := hyps.size
    for tuple in gradedTuples sizes 2000 do
      if remaining == 0 then break
      -- the values, in binder order: a variable takes its value, an instance is synthesized, a hypothesis gets nothing
      let mut fvs : Array Expr := #[]
      let mut vals : Array Expr := #[]
      let mut assigned : Array String := #[]
      let mut ok := true
      let mut vi := 0
      for i in [0:xs.size] do
        match kinds[i]! with
        | .var nm d =>
          let (v, s) := d[tuple[vi]!]!
          vi := vi + 1
          fvs := fvs.push xs[i]!; vals := vals.push v; assigned := assigned.push s!"{nm} = {s}"
        | .inst =>
          let ty := (← instantiateMVars (← xs[i]!.fvarId!.getType)).replaceFVars fvs vals
          match ← (if ty.hasFVar then pure none else tryCatchRuntimeEx (synthInstance? ty) fun _ => pure none) with
          | some inst => fvs := fvs.push xs[i]!; vals := vals.push inst
          | none => ok := false; break
        | _ => pure ()
      unless ok do continue
      let concl := body.replaceFVars fvs vals
      if concl.hasFVar then continue
      let some false ← evalClosed concl | continue
      -- the hypotheses that do not hold here
      let mut bad : Array Nat := #[]
      for j in [0:hyps.size] do
        let ht := (← instantiateMVars (← xs[hyps[j]!]!.fvarId!.getType)).replaceFVars fvs vals
        if ht.hasFVar || (← evalClosed ht) != some true then bad := bad.push j
        if bad.size > 1 then break
      let where_ := if assigned.isEmpty then "with no variable to assign" else "for " ++ ", ".intercalate assigned.toList
      if bad.isEmpty then
        return #[("fail", s!"the statement EVALUATES TO FALSE {where_}: every hypothesis holds and the conclusion fails (`{← shown concl 160}` is false): a proof of it was accepted (a kernel bug, or a proof that bypassed the kernel)")]
      if bad.size == 1 && justified[bad[0]!]!.isNone then
        justified := justified.set! bad[0]! (some (where_, ← shown concl 160))
        remaining := remaining - 1
    let unused := if t.value.hasSorry then #[] else unusedPositions t.type t.value 0 #[]
    let mut out := #[]
    for j in [0:hyps.size] do
      let i := hyps[j]!
      match justified[j]! with
      | some (where_, concl) =>
        let others := if hyps.size == 1 then "" else "the other hypotheses hold and "
        out := out.push ("info", s!"hypothesis {hypName i} is justified: {where_} {others}the conclusion fails (`{concl}` is false)")
      | none =>
        if unused.contains i then
          out := out.push ("warn", s!"hypothesis {hypName i} is neither used by the proof nor justified by a counterexample in the small domain: the theorem may hold without it")
        else
          let why := if t.value.hasSorry then "the proof is a sorry" else "the hypothesis is used by the proof"
          out := out.push ("info", s!"hypothesis {hypName i}: no counterexample in the small domain ({why})")
    if remaining == 0 then
      out := out.push ("info", s!"every hypothesis is justified by a counterexample ({hyps.size} of {hyps.size})")
    return out

def necessity (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let cap := ((← IO.getEnv "JINSHI_NECESSITY_MAX").bind String.toNat?).getD 100
  let mut out := #[]
  let mut examined : NameMap Nat := {}
  let mut skipped : NameMap Nat := {}
  for (m, n, ci) in selected c env do
    let .thmInfo t := ci | continue
    unless okName n do continue
    if (examined.find? m).getD 0 ≥ cap then
      skipped := skipped.insert m ((skipped.find? m).getD 0 + 1)
      continue
    let findings ← try examineOne t catch _ => pure #[]
    if findings.isEmpty then continue
    examined := examined.insert m ((examined.find? m).getD 0 + 1)
    let line ← lineOf n
    for (severity, detail) in findings do
      out := out.push { check := "necessity", severity, module := m, name := n, line, detail }
  for (m, k) in skipped do
    out := out.push { check := "necessity", severity := "info", module := m, name := .anonymous,
                      detail := s!"{k} theorems with hypotheses not examined: the module's cap of {cap} (JINSHI_NECESSITY_MAX) was reached" }
  return out

end Jinshi
