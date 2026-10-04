/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Ring.Defs
public import Tengoku.Seed.Algebra.Order.Ring.Unbundled.Rat
public import Tengoku.Seed.Algebra.Ring.Rat

/-!
# The rational numbers form a linear ordered commutative ring

This file proves that the linear order on `ℚ` makes it into an ordered ring.

`ℚ` is in fact a linearly ordered field. To access this fact, one must also import
`Mathlib/Algebra/Field/Rat.lean`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

public section

assert_not_exists Field Finset Set.Icc GaloisConnection

namespace Rat

instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ ab _ => Rat.add_le_add_right.2 ab

instance instIsStrictOrderedRing : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ ha hb ↦
  (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

end Rat
