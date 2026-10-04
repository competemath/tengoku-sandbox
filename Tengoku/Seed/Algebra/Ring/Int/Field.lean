/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Field.IsField
public import Tengoku.Seed.Algebra.Ring.Int.Defs

/-! # `ℤ` is not a field -/

/-- `ℤ` with its usual ring structure is not a field. -/
public theorem Int.not_isField : ¬IsField ℤ := fun ⟨_, _, h⟩ ↦ have := @h 2; by grind
