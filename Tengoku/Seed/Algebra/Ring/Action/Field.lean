/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Ring.Action.Basic
public import Tengoku.Seed.Algebra.Field.Defs
public import Tengoku.Seed.Algebra.GroupWithZero.Units.Lemmas

/-!
# Group action on fields
-/

public section

variable {M} [Monoid M] {F} [DivisionRing F]

/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  map_inv₀ (MulSemiringAction.toRingHom M F x) _
