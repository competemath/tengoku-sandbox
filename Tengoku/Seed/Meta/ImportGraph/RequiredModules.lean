/-
Changed for Tengoku: copied from import-graph (leanprover-community/import-graph at d8823026ac7e); import paths rewritten.
-/
module

public import Tengoku.Seed.Meta.ImportGraph.Imports.RequiredModules
import Lean

open Lean

-- deprecated 2026-02-01
#eval do
  logWarning "`ImportGraph.RequiredModules` is deprecated! use `import ImportGraph.Imports.RequiredModules` instead."
