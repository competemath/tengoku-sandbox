/-
ic_graph — the import graph of a set of root modules, from Lean's own loader, without building an environment:
  lake env lean --run ic_graph.lean Tengoku.All > graph.tsv
one line per module (every module reachable from the roots, the roots included):  <module> TAB <olean path> TAB <direct imports, space separated>
The independent check's planner and its coverage check both read this file; nothing here is trusted beyond Lean's module loader.
-/
import Lean
open Lean

def main (roots : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := roots.toArray.map fun m => ({ module := m.toName } : Import)
  let (_, st) ← (importModulesCore imports).run {}
  for i in [0:st.moduleNames.size] do
    let name := st.moduleNames[i]!
    let data := st.moduleData[i]!
    let path ← findOLean name
    let imps := data.imports.map (fun (imp : Import) => imp.module.toString)
    IO.println s!"{name}\t{path}\t{" ".intercalate imps.toList}"
  return 0
