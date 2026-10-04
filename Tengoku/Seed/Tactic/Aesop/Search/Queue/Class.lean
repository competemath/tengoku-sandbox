/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
Changed for Tengoku: copied from Aesop (leanprover-community/aesop at 18889deb9e83); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Aesop.Tree.Data

public section

open Lean

namespace Aesop

class Queue (Q : Type) where
  init : BaseIO Q
  addGoals : Q → Array GoalRef → BaseIO Q
  popGoal : Q → BaseIO (Option GoalRef × Q)

namespace Queue

def init' [Queue Q] (grefs : Array GoalRef) : BaseIO Q := do
  addGoals (← init) grefs

end Aesop.Queue
