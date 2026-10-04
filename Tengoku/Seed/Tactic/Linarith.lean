/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public meta import Tengoku.Seed.Tactic.Hint
public import Tengoku.Seed.Tactic.Linarith.Frontend
public import Tengoku.Seed.Tactic.NormNum

/-!
We register `linarith` with the `hint` tactic.
-/

public meta section

register_hint 100 linarith
