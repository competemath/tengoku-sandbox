/-
roundtrip — what the reader SEES is not what the kernel CHECKED (docs/jinshi.md, head E).

A theorem's statement reaches people through the pretty printer (hover, docs, search), not through the elaborated term the
kernel checked. For every theorem of an examined module the statement is printed as a reader would see it (the default
options, plus `pp.fullNames` so that names resolve without any `open`), parsed back as a term, elaborated as a type in a fresh
context with auto-bound implicits off (an unbound name must be an error, not a silently quantified variable), and compared with
the type the kernel checked by `isDefEq`. The two are the same statement: nothing. The printed text does not parse: `info`. It
parses but does not elaborate (a private or hygienic name, a proof the printer elided as `⋯`): `info`. It elaborates to a
DIFFERENT statement: `warn`, with both statements printed — this is a notation that hides an argument, a coercion that prints
invisibly, an instance that resolves differently, a numeral whose type the text does not show. A difference only in universe
levels is `info`.

Everything runs under a heartbeat cap and `withoutModifyingEnv`, every exception (runtime ones included) is a finding, never a
crash.
-/
import Jinshi.Base
open Lean Meta Elab

namespace Jinshi

/-- heartbeats (in the option's unit of 1000) each pretty-print, elaboration and comparison may spend -/
def roundtripHeartbeats : Nat := 100000

/-- the options the round trip runs with: the reader's defaults, full names, no auto-bound implicits -/
def roundtripOptions (o : Options) : Options :=
  o.setBool `pp.fullNames true |>.setBool `autoImplicit false |>.setBool `relaxedAutoImplicit false

/-- at most `n` characters, on one line -/
def roundtripCut (s : String) (n : Nat) : String :=
  let s := s.replace "\n" " "
  if s.length > n then String.ofList (s.toList.take n) ++ "…" else s

/-- every universe level replaced by a fresh level metavariable: two types `isDefEq` after this differ at most in universes
(zeroing the levels instead would make `Eq.{0} Nat …` ill-typed, and `isDefEq` then compares proofs by irrelevance) -/
def roundtripFreshLevels (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    match e with
    | .sort _ => return .done (.sort (← mkFreshLevelMVar))
    | .const n ls => return .done (.const n (← ls.mapM fun _ => mkFreshLevelMVar))
    | _ => return .continue)

/-- run `x` with its own heartbeat budget, and turn every exception, runtime ones included, into `Except` -/
def roundtripGuard (x : MetaM α) : MetaM (Except String α) :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := roundtripHeartbeats * 1000 }) <|
    withCurrHeartbeats <|
      tryCatchRuntimeEx (Except.ok <$> x) fun e => do
        let msg ← try e.toMessageData.toString catch _ => pure "exception"
        return Except.error msg

inductive RoundtripVerdict where
  | same
  | universes
  | noParse (shown err : String)
  | noElab (shown err : String)
  | differs (shown proved : String)

/-- print `ty` as a reader sees it, read it back, elaborate it as a type and compare with `ty` -/
def roundtripOne (n : Name) (ci : ConstantInfo) : MetaM RoundtripVerdict := withoutModifyingEnv do
  let ty := ci.type
  let shown ← roundtripGuard (withOptions roundtripOptions do
    let f ← ppExpr ty
    pure (toString f))
  let shown ← match shown with
    | .ok s => pure s
    | .error e => return .noElab "?" s!"the statement could not be printed: {e}"
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term shown "<roundtrip>" with
    | .ok stx => pure stx
    | .error e => return .noParse shown e
  -- an elaboration error is LOGGED, not thrown (the term is left as a metavariable): the message log is the error channel
  let saved ← Core.getMessageLog
  Core.setMessageLog {}
  let reelab ← roundtripGuard (withOptions roundtripOptions do
    Term.TermElabM.run' (ctx := { declName? := some n }) (s := { levelNames := ci.levelParams }) do
      Term.withoutErrToSorry do
        let e ← Term.elabType stx
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e)
  let log ← Core.getMessageLog
  Core.setMessageLog saved
  let re ← match reelab with
    | .ok e => pure e
    | .error e => return .noElab shown e
  if log.hasErrors then
    let firstErr ← (log.toList.filter (·.severity == .error)).headD default |>.data.toString
    return .noElab shown firstErr
  let same ← roundtripGuard (withOptions roundtripOptions do
    let re ← instantiateMVars re
    let ty ← instantiateMVars ty
    isDefEq ty re)
  if same matches .ok true then return .same
  -- the same statement up to universe levels?
  let upToLevels ← roundtripGuard do
    isDefEq (← roundtripFreshLevels (← instantiateMVars ty)) (← roundtripFreshLevels (← instantiateMVars re))
  if upToLevels matches .ok true then return .universes
  -- both sides for the reader: the default printing first, and the explicit one when the two read the same
  let print (e : Expr) (explicit : Bool) : MetaM String := do
    match ← roundtripGuard (withOptions (fun o => (roundtripOptions o).setBool `pp.explicit explicit) do pure (toString (← ppExpr e))) with
    | .ok s => pure s
    | .error _ => pure "?"
  let mut a ← print ty false
  let mut b ← print re false
  if a == b then
    a ← print ty true
    b ← print re true
  return .differs b a

def roundtrip (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    let verdict ← try roundtripOne n ci catch e => do
      let msg ← try e.toMessageData.toString catch _ => pure "exception"
      pure (.noElab "?" s!"the round trip failed: {msg}")
    let push (sev detail : String) : CoreM (Array Finding) := do
      return out.push { check := "roundtrip", severity := sev, module := m, name := n, line := ← lineOf n, detail }
    match verdict with
    | .same => pure ()
    | .universes =>
      out ← push "info" "the printed statement elaborates to the same statement up to universe levels (the text does not show them)"
    | .noParse shown err =>
      out ← push "info" s!"the printed statement does not parse: `{roundtripCut shown 120}` ({roundtripCut err 120})"
    | .noElab shown err =>
      out ← push "info" s!"the printed statement does not elaborate: {roundtripCut err 200} — shown as `{roundtripCut shown 120}`"
    | .differs shown proved =>
      out ← push "warn" s!"the printed statement elaborates to a different statement: shown `{roundtripCut shown 200}`, proved `{roundtripCut proved 200}`"
  return out

end Jinshi
