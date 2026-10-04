/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.PPWithUniv

/-! # `ToLevel` class

This module defines `Lean.ToLevel`, which is the `Lean.Level` analogue to `Lean.ToExpr`.

**Warning:** Import `Mathlib/Tactic/ToExpr.lean` instead of this one if you are writing `ToExpr`
instances. This ensures that you are using the universe polymorphic `ToExpr` instances that
override the ones from Lean 4 core.

-/

public meta section

namespace Lean

attribute [pp_with_univ] toLevel

end Lean
