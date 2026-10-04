/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.TransferInstance
public import Tengoku.Seed.Algebra.Ring.Shrink

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [CommSemiring R]

namespace Shrink

instance [Semiring α] [Algebra R α] : Algebra R (Shrink.{v} α) := (equivShrink α).symm.algebra _

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves algebra structure. -/
@[simps!]
def algEquiv [Semiring α] [Algebra R α] : Shrink.{v} α ≃ₐ[R] α :=
  (equivShrink α).symm.algEquiv _

end Shrink
