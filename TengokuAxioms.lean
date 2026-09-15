/-
Axiom check for the merge queue: every declaration of a module must rest only
on propext, Classical.choice and Quot.sound.

  lake build tengoku-axioms
  lake env .lake/build/bin/tengoku-axioms --module Tengoku.Lib._candidate_x
-/
import Lean
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def check (mods : List Name) : CoreM UInt32 := do
  let env ← getEnv
  let mut bad := 0
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    if !mods.contains m then continue
    if n.isInternal || n.hasMacroScopes then continue
    let axioms ← collectAxioms n
    checked := checked + 1
    let extra := axioms.filter (!allowed.contains ·)
    if !extra.isEmpty then
      bad := bad + 1
      IO.println s!"error: {n} depends on {extra.toList} (allowed: propext, Classical.choice, Quot.sound){if extra.contains ``sorryAx then " — the proof contains sorry" else ""}"
  IO.println s!"axioms: {checked} declarations checked, {bad} with non-standard axioms"
  return (if bad == 0 then 0 else 1)

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let mods := (argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == "--module" then some b.toName else none
  if mods.isEmpty then IO.eprintln "usage: tengoku-axioms --module <M> [--module <M>…]"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<tengoku-axioms>", fileMap := default, maxHeartbeats := 0 }
  let (code, _) ← (check mods).toIO ctx { env }
  return code
