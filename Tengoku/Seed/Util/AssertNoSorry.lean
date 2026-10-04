/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Init
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# Defines the `assert_no_sorry` command.

Throws an error if the given identifier uses sorryAx.
-/

public meta section

open Lean Meta Elab Command

/-- Throws an error if the given identifier uses sorryAx. -/
elab "assert_no_sorry " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``sorryAx
  then throwError "{n} contains sorry"
