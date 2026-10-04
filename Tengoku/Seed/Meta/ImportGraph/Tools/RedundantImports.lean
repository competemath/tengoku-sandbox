/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
Changed for Tengoku: copied from import-graph (leanprover-community/import-graph at d8823026ac7e); import paths rewritten.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Widget.UserWidget
public meta import Tengoku.Seed.Meta.ImportGraph.Imports.Redundant

public meta section

open Lean

/--
List the imports in this file which can be removed
because they are transitively implied by another import.
-/
elab "#redundant_imports" : command => do
  let redundant := (← Elab.Command.liftCoreM do redundantImports)
  if redundant.isEmpty then
    logInfo "No transitively redundant imports found."
  else
    logInfo <| "Found the following transitively redundant imports:\n" ++
      m!"{Format.joinSep redundant.toList "\n"}"
