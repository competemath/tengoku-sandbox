/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
Changed for Tengoku: copied from ProofWidgets (leanprover-community/ProofWidgets4 at a8acbfd87375); import paths rewritten.
-/

module

public import Tengoku.Seed.Widgets.Component.Basic

open ProofWidgets

public meta section
open Lean

structure MaximizableProps where
  deriving ToJson, FromJson

/-- Wraps its children in a `<div>` that can be maximized to take up the whole viewport
by clicking a button in the top-right corner. -/
@[widget_module]
def Maximizable : Component MaximizableProps where
  javascript := include_str ".." / ".." / "widget" / "js" / "maximizable.js"
