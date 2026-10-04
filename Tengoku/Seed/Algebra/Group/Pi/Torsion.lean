/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Pi.Basic
public import Tengoku.Seed.Algebra.Group.Torsion

/-!
# Torsion of products

This file proves that products of torsion-free monoids are torsion-free.
-/

public section

assert_not_exists AddMonoidWithOne MonoidWithZero

variable {ι : Type*} {M : ι → Type*}

namespace Pi

@[to_additive]
instance instIsMulTorsionFree [∀ i, Monoid (M i)] [∀ i, IsMulTorsionFree (M i)] :
    IsMulTorsionFree (∀ i, M i) where
  pow_left_injective n hn a b hab := by ext i; exact pow_left_injective hn <| congr_fun hab i

end Pi
