/-
ic_graph — the import graph of a set of root modules, from Lean's own module reader, without building an environment:
  lake env lean --run ic_graph.lean Tengoku.All > graph.tsv
one line per module (every module reachable from the roots, the roots included):  <module> TAB <olean path> TAB <direct imports, space separated>
It reads each module's header with `readModuleData` (the same reader the loader uses) and follows its imports; nothing is cached or assumed.
The independent check's planner and its coverage check both read this file.
-/
import Lean
open Lean

partial def visit (seen : IO.Ref (Std.HashSet Name)) (out : IO.Ref (Array String)) (n : Name) : IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let path ← findOLean n
  let (data, region) ← readModuleData path
  let imps := data.imports.map (·.module)
  out.modify (·.push s!"{n}\t{path}\t{" ".intercalate (imps.toList.map toString)}")
  region.free
  for i in imps do visit seen out i

def main (roots : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let seen ← IO.mkRef ({} : Std.HashSet Name)
  let out ← IO.mkRef (#[] : Array String)
  for r in roots do visit seen out r.toName
  for line in (← out.get) do IO.println line
  return 0
