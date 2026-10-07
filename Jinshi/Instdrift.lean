/-
Jinshi — instdrift: the statement a reader would get TODAY differs from the statement that was proved (docs/jinshi.md).

The tree is one environment that keeps growing. A theorem's statement was elaborated once, with the instances the environment
held then; when a later module registers a global instance (a norm, an order, a decidability, a `Weight`), the same statement
text now elaborates to a different term. The theorem is still true for the instance it was proved with, and no longer applies
to what people now write. The seed is not exempt: a library that leaks an instance makes the seed's own statements drift.

For every theorem of an examined module: the statement is opened (`forallTelescope`, the hypotheses and the conclusion), every
application of a constant is looked at, and each instance-implicit argument `inst : T` is compared with what `synthInstance? T`
returns in the environment of this run. A synthesized instance that is not definitionally the stored one is the finding (warn);
a class for which nothing is found today is reported once per theorem (info: the statement cannot be re-stated as written).
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-- heartbeats allowed to one synthesis or one definitional comparison (the raw count: 1000 of these are one unit of `maxHeartbeats`) -/
def instdriftHeartbeats : Nat := 200 * 1000

/-- instance arguments looked at per theorem -/
def instdriftArgsPerTheorem : Nat := 200

/-- run `x` under a heartbeat cap; a failure of any kind, the cap included, is `none` -/
def underCap (x : MetaM α) : MetaM (Option α) :=
  withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := instdriftHeartbeats }) <|
    tryCatchRuntimeEx (some <$> x) fun _ => pure none

/-- the head constant of an instance term, as a reader would name it -/
def instHead (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => toString n
  | .fvar _ => "a local instance"
  | _ => "an anonymous instance term"

/-- one finding per class per theorem (`drift`), the "no instance today" at most once (`none`), the synthesis of each class type once -/
structure DriftState where
  seen : Nat := 0
  drifted : NameSet := {}
  missing : Bool := false
  synth : ExprMap (Option Expr) := {}
  out : Array Finding := #[]

/-- the instance-implicit arguments of the applications in `e`, each compared with today's synthesis -/
partial def driftWalk (c : Ctx) (m n : Name) (line : Option Nat) (e : Expr) : StateRefT DriftState MetaM Unit := do
  if (← get).seen ≥ instdriftArgsPerTheorem then return
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const _ _ := f then
      if !e.hasLooseBVars then
        let info? ← (underCap (getFunInfoNArgs f args.size) : MetaM _)
        if let some info := info? then
          for h : i in [:args.size] do
            if h' : i < info.paramInfo.size then
              if info.paramInfo[i].binderInfo == .instImplicit then
                examine c m n line args[i]
    driftWalk c m n line f
    for a in args do driftWalk c m n line a
  | .lam nm t b bi | .forallE nm t b bi =>
    driftWalk c m n line t
    if b.hasLooseBVars then withLocalDecl nm bi t fun x => driftWalk c m n line (b.instantiate1 x)
    else driftWalk c m n line b
  | .letE nm t v b _ =>
    driftWalk c m n line t
    driftWalk c m n line v
    if b.hasLooseBVars then withLetDecl nm t v fun x => driftWalk c m n line (b.instantiate1 x)
    else driftWalk c m n line b
  | .mdata _ b | .proj _ _ b => driftWalk c m n line b
  | _ => pure ()
where
  examine (c : Ctx) (m n : Name) (line : Option Nat) (inst : Expr) : StateRefT DriftState MetaM Unit := do
    if (← get).seen ≥ instdriftArgsPerTheorem then return
    modify fun st => { st with seen := st.seen + 1 }
    if inst.hasLooseBVars || inst.hasMVar then return
    let some T ← (underCap (do instantiateMVars (← inferType inst)) : MetaM _) | return
    if T.hasLooseBVars || T.hasMVar then return
    let some cls ← (underCap (isClass? T) : MetaM _) | return
    let some cls := cls | return
    let env ← getEnv
    let now? ← match (← get).synth[T]? with
      | some r => pure r
      | none => do
        let r := (← (underCap (synthInstance? T) : MetaM _)).join
        modify fun st => { st with synth := st.synth.insert T r }
        pure r
    match now? with
    | none =>
      if (← get).missing then return
      if (← get).drifted.contains cls then return
      let shown ← (underCap (do pure (toString (← ppExpr T))) : MetaM _)
      let f : Finding :=
        { check := "instdrift", severity := "info", module := m, name := n, line,
          detail := s!"no instance is found today for {shown.getD (toString cls)} (class {cls}): the statement cannot be re-stated as written; it was proved with `{instHead inst}`" }
      modify fun st => { st with missing := true, out := st.out.push f }
    | some now =>
      if (← get).drifted.contains cls then return
      let same? ← (underCap (withNewMCtxDepth (isDefEq inst now)) : MetaM _)
      if same? == some true then return
      let shownT ← (underCap (do pure (toString (← ppExpr T))) : MetaM _)
      let nowHead := now.getAppFn.constName?
      let nowMod := match nowHead with
        | some h => (moduleOf env h).map toString |>.getD "a module not in the tree"
        | none => "a module not in the tree"
      let verdict := if same?.isNone then "could not be compared with" else "is not definitionally"
      let f : Finding :=
        { check := "instdrift", severity := "warn", module := m, name := n, line,
          detail := s!"class {cls}: the statement was proved with `{instHead inst}` for {shownT.getD (toString cls)}, and today the same text elaborates to `{instHead now}` ({nowMod}), which {verdict} the stored one: the theorem no longer speaks of what a reader now writes" }
      modify fun st => { st with drifted := st.drifted.insert cls, out := st.out.push f }

def instdrift (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    let line ← lineOf n
    let found ← try
        forallTelescope ci.type fun xs body => do
          let (_, st) ← (do
              for x in xs do driftWalk c m n line (← instantiateMVars (← inferType x))
              driftWalk c m n line (← instantiateMVars body) : StateRefT DriftState MetaM Unit).run {}
          return st.out
      catch _ => pure #[]
    out := out ++ found
  return out

end Jinshi
