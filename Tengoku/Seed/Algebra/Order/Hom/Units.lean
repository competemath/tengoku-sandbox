/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Units.Equiv
public import Tengoku.Seed.Algebra.Order.Hom.Monoid
public import Tengoku.Seed.Algebra.Order.Monoid.Units

/-! # Isomorphism of ordered monoids descends to units
-/

@[expose] public section

variable {α β : Type*} [Preorder α] [Monoid α] [Preorder β] [Monoid β] (e : α ≃*o β)

/-- An isomorphism of ordered monoids descends to their units. -/
@[simps!]
def OrderMonoidIso.unitsCongr : αˣ ≃*o βˣ where
  __ := Units.mapEquiv e.toMulEquiv
  map_le_map_iff' {x y} := by simp [← Units.val_le_val]

lemma OrderMonoidIso.unitsCongr_symm_apply (x : βˣ) : e.unitsCongr.symm x = e.symm x := rfl
