/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Field.Defs
public import Tengoku.Seed.Algebra.GroupWithZero.Action.Defs

/-!
# Actions by nonnegative rational numbers
-/

public section

assert_not_exists IsOrderedMonoid

variable {R : Type*}

/-! ### Scalar multiplication -/

namespace NNRat
variable [DivisionSemiring R]

instance (priority := 100) instDistribSMul : DistribSMul ℚ≥0 R where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]

instance instIsScalarTowerRight : IsScalarTower ℚ≥0 R R where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end NNRat

namespace Rat
variable [DivisionRing R]

instance (priority := 100) instDistribSMul : DistribSMul ℚ R where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]

instance instIsScalarTowerRight : IsScalarTower ℚ R R where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end Rat
