/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Submonoid.Defs
public import Tengoku.Seed.Algebra.GroupWithZero.Divisibility

/-!
# Submonoid of primal elements
-/

@[expose] public section

assert_not_exists RelIso Ring

/-- The submonoid of primal elements in a cancellative commutative monoid with zero. -/
def Submonoid.isPrimal (M₀ : Type*) [CommMonoidWithZero M₀] [IsCancelMulZero M₀] :
    Submonoid M₀ where
  carrier := {a | IsPrimal a}
  mul_mem' := .mul
  one_mem' := isUnit_one.isPrimal
