/-
Vacuity check: for every theorem of the given modules, try to prove `False` from its
hypotheses alone. A theorem whose assumptions can never all hold is vacuously true: it
proves nothing about anything, and Lean cannot tell, because it is still correct.

Run inside the built Lake project the modules belong to:

  lake env lean --run vacuity.lean <Module> [<Module> …]

One line per vacuous theorem — `VACUOUS <theorem> <module> <tactic>` followed by its
hypotheses — and a summary. A theorem whose conclusion is `False` (a negation) is not
reported: deriving `False` is its content. Exit code 0 either way; this is a warning.
-/
import Lean
open Lean Meta Elab

/-- Tactics tried, in order, each under its own heartbeat budget. Ones this toolchain or
project does not know are skipped. -/
def candidates : List String :=
  ["omega", "simp_all", "decide", "linarith", "positivity", "grind", "aesop"]

def parseTactic (env : Environment) (s : String) : Option Syntax :=
  match Parser.runParserCategory env `tactic s with
  | .ok stx => some stx
  | .error _ => none

/-- Inside the theorem's binders, is `False` provable? Returns the tactic that did it. -/
def refutes (thm : ConstantInfo) (tactics : List (String × Syntax)) : Term.TermElabM (Option String) :=
  forallTelescope thm.type fun _ body => do
    if body.isConstOf ``False then return none  -- a negation: deriving False is its content
    for (name, stx) in tactics do
      -- heartbeat exhaustion is a runtime exception, which a plain `catch` does not see
      let ok ← tryCatchRuntimeEx
        (do
          let mvar ← mkFreshExprMVar (mkConst ``False)
          let remaining ← withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 40000 * 1000 }) do
            Tactic.run mvar.mvarId! (Tactic.evalTactic stx)
          pure remaining.isEmpty)
        (fun _ => pure false)
      if ok then return some name
    return none

def hypotheses (thm : ConstantInfo) : MetaM (List String) :=
  forallTelescope thm.type fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if !d.userName.hasMacroScopes && !(← isClass? d.type).isSome then
        if (← isProp d.type) then out := out ++ [s!"{d.userName} : {← ppExpr d.type}"]
    return out

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  let src := String.intercalate "\n" (mods.map fun m => s!"import {m}")
  let inputCtx := Parser.mkInputContext src "<vacuity>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    for m in messages.toList do IO.eprintln (← m.toString)
    throw (IO.userError "imports failed")
  let tactics := candidates.filterMap fun s => (parseTactic env s).map (s, ·)
  IO.println s!"tactics available: {tactics.map (·.1)}"
  let modIdxs := mods.filterMap env.getModuleIdx?
  let thms := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ =>
      if n.isInternal then acc else
      match env.getModuleIdxFor? n with
      | some i => if modIdxs.contains i then acc.push ci else acc
      | none => acc
    | _ => acc
  let cmdState := Command.mkState env messages {}
  let fctx : Frontend.Context := { inputCtx }
  let mut vacuous := 0
  for ci in thms do
    let modName := (env.getModuleIdxFor? ci.name).bind (env.header.moduleNames[·]?) |>.getD .anonymous
    let (res, _) ← (Frontend.runCommandElabM (Command.liftTermElabM do
        let r ← refutes ci tactics
        match r with
        | some t => return some (t, ← hypotheses ci)
        | none => return none) |>.run fctx).run { commands := #[], commandState := cmdState, parserState, cmdPos := 0 }
    if let some (t, hyps) := res then
      vacuous := vacuous + 1
      IO.println s!"VACUOUS {ci.name} {modName} {t}"
      IO.println s!"  its assumptions can never all hold; `{t}` derives a contradiction from:"
      for h in hyps do IO.println s!"    {h}"
  IO.println s!"checked {thms.size} theorems in {mods.length} modules: {vacuous} vacuous"
