/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Batteries (leanprover-community/batteries at d54dddc581e0); import paths rewritten.
-/
module

public import Tengoku.Seed.Std.Lean.System.IO
public import Tengoku.Seed.Std.Data.MLList.Basic

@[expose] public section

/-!
# IO operations using monadic lazy lists.
-/

namespace MLList

/--
Give a list of tasks, return the monadic lazy list which
returns the values as they become available.
-/
def ofTaskList (tasks : List (Task α)) : MLList BaseIO α :=
  fix?' (init := tasks) fun t => do
    if h : 0 < t.length then
      some <$> IO.waitAny' t h
    else
      pure none
