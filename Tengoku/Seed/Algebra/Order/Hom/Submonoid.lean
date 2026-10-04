/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Submonoid.Operations
public import Tengoku.Seed.Algebra.Order.Hom.Monoid

/-!
# Isomorphism of submonoids of ordered monoids
-/

@[expose] public section

/-- The top submonoid is order isomorphic to the whole monoid. -/
@[simps!]
def Submonoid.topOrderMonoidIso {α : Type*} [Preorder α] [Monoid α] : (⊤ : Submonoid α) ≃*o α where
  __ := Submonoid.topEquiv
  map_le_map_iff' := Iff.rfl
