/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Monoid.Prod
public import Tengoku.Seed.Algebra.Order.Ring.Defs
public import Tengoku.Seed.Algebra.Ring.Prod

/-!
# Products of ordered rings
-/

public section

variable {α β : Type*}

instance [Semiring α] [PartialOrder α] [IsOrderedRing α]
    [Semiring β] [PartialOrder β] [IsOrderedRing β] : IsOrderedRing (α × β) where
  zero_le_one := ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_left hbc.1 ha.1, mul_le_mul_of_nonneg_left hbc.2 ha.2⟩
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_right hbc.1 ha.1, mul_le_mul_of_nonneg_right hbc.2 ha.2⟩
