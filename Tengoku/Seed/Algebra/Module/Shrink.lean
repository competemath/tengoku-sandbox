/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Shrink
public import Tengoku.Seed.Algebra.Module.TransferInstance

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

@[expose] public noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [Semiring R] [AddCommMonoid α] [Module R α]

namespace Shrink

instance : Module R (Shrink.{v} α) := addEquiv.module R

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves module structure. -/
@[simps!]
def linearEquiv : Shrink.{v} α ≃ₗ[R] α := (addEquiv (α := α)).linearEquiv R

end Shrink
