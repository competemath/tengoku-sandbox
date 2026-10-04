/-
Leak scan for the merge queue: what a library changes for everybody else.

A global instance or simp lemma whose statement mentions only constants of OTHER libraries (Mathlib, core, a sibling library) changes how
every statement of every other library elaborates once the tree is imported as one: `attribute [instance] Matrix.linftyOpNormedAddCommGroup`
made `‖A‖` the L∞ operator norm on every matrix in the tree (Mathlib keeps it `scoped` on purpose). An instance or simp lemma about the
library's own types can never fire elsewhere and is harmless. This reads the compiled environment (not the text): every global entry that
the library's modules registered in the instance and simp extensions, and whether its statement mentions a constant of the library.

  lake build tengoku-leakscan
  lake env .lake/build/bin/tengoku-leakscan --module Tengoku.Lib [--prefix Tengoku.Lib …] [--tree-prefix Tengoku.Lib] [--strict]

Report only unless `--strict` (then exit 1 when anything leaks). `--prefix` defaults to the modules named. `--tree-prefix` is put in front
of every module name in the report: the factory scans the library under its own module names, and the report is read in the tree's
(`Tengoku.<Library>.<module>`, scripts/bump/scope_rewrite.py).
-/
import Lean
open Lean Meta

/-- one global registration whose statement mentions nothing of its own library -/
structure Leak where
  kind : String
  name : Name
  registeredIn : Name
  /-- where it is declared, when that is a module of the library (an `attribute` command registers a declaration of ANOTHER library) -/
  line : Option Nat
  declaredIn : Option Name
  /-- an instance's priority when it is not the default (1000): a local re-registration must keep it -/
  prio : Option Nat := none

structure Counts where
  inst : Nat := 0
  instScoped : Nat := 0
  simp : Nat := 0
  simpScoped : Nat := 0
  /-- declarations of the library whose name has one component: nothing in the name says which library they belong to -/
  roots : Array Name := #[]

def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | e => e

/-- the part of a simp lemma's statement that triggers it: the left-hand side of `=`/`↔`, else the statement -/
def trigger (ty : Expr) : Expr :=
  let b := stripForall ty
  match b.eq? with
  | some (_, l, _) => l
  | none => match b.iff? with
    | some (l, _) => l
    | none => b

def scan (pfxs : List Name) : CoreM (Array Leak × Counts) := do
  let env ← getEnv
  let idxs := (List.range env.header.moduleNames.size).filter fun i => pfxs.any (·.isPrefixOf env.header.moduleNames[i]!)
  let own (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some m => idxs.contains m
    | none => false
  let mut leaks : Array Leak := #[]
  let mut counts : Counts := {}
  for i in idxs do
    let modName := env.header.moduleNames[i]!
    for e in instanceExtension.ext.getModuleEntries env i do
      match e with
      | .scoped _ _ => counts := { counts with instScoped := counts.instScoped + 1 }
      | .global ie =>
        counts := { counts with inst := counts.inst + 1 }
        let n := ie.globalName?.getD (ie.val.constName?.getD `_)
        let ty := ((env.find? n).map (·.type)).getD (.sort .zero)
        unless ty.getUsedConstants.any own do
          let r ← findDeclarationRanges? n
          let dm := (env.getModuleIdxFor? n).bind fun m => env.header.moduleNames[m]?
          leaks := leaks.push { kind := "instance", name := n, registeredIn := modName, declaredIn := dm,
                                line := if dm == some modName then r.map (·.range.pos.line) else none,
                                prio := if ie.priority == 1000 then none else some ie.priority }
    for e in simpExtension.ext.getModuleEntries env i do
      match e with
      | .scoped _ _ => counts := { counts with simpScoped := counts.simpScoped + 1 }
      | .global (.thm t) =>
        counts := { counts with simp := counts.simp + 1 }
        let n := t.origin.key
        let ty := ((env.find? n).map (·.type)).getD (.sort .zero)
        unless (trigger ty).getUsedConstants.any own do
          let r ← findDeclarationRanges? n
          let dm := (env.getModuleIdxFor? n).bind fun m => env.header.moduleNames[m]?
          leaks := leaks.push { kind := "simp", name := n, registeredIn := modName, declaredIn := dm,
                                line := if dm == some modName then r.map (·.range.pos.line) else none }
      | .global _ => pure ()
  for (n, _) in env.constants.map₁.toList do
    if let some m := env.getModuleIdxFor? n then
      if idxs.contains m && n.isAtomic && !n.isInternal && !n.hasMacroScopes then
        counts := { counts with roots := counts.roots.push n }
  return (leaks, counts)

def report (treePrefix : Name) (leaks : Array Leak) (c : Counts) : List String :=
  let rows := leaks.toList.map fun l =>
    s!"leak: {l.kind} {l.name} registered in {treePrefix ++ l.registeredIn}" ++
      (match l.prio with | some p => s!" (priority {p})" | none => "") ++
      (match l.line, l.declaredIn with
       | some n, _ => s!" (declared at line {n})"
       | none, some m => s!" (declared in {m}: an `attribute` command of the library turns it on)"
       | none, none => "")
  rows ++ [s!"roots: {c.roots.size} declarations of the library are in the root namespace (nothing in their names tells libraries apart; a second library declaring one fails to import): " ++
    s!"{(c.roots.toList.take 20).map toString}"] ++ [s!"leakscan: {c.inst} global instances ({(leaks.filter (·.kind == "instance")).size} touch no type of the library), {c.instScoped} scoped; " ++
    s!"{c.simp} global simp lemmas ({(leaks.filter (·.kind == "simp")).size} trigger on nothing of the library), {c.simpScoped} scoped"]

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let flag (f : String) := (argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == f then some b.toName else none
  let treePrefix := (flag "--tree-prefix").headD .anonymous
  let mods := flag "--module"
  let pfxs := if (flag "--prefix").isEmpty then mods else flag "--prefix"
  if mods.isEmpty then
    IO.eprintln "usage: tengoku-leakscan --module <M> [--module <M>…] [--prefix <P>…] [--tree-prefix <P>] [--strict]"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<tengoku-leakscan>", fileMap := default, maxHeartbeats := 0 }
  let ((leaks, counts), _) ← (scan pfxs).toIO ctx { env }
  for ln in report treePrefix leaks counts do IO.println ln
  return (if argv.contains "--strict" && !leaks.isEmpty then 1 else 0)
