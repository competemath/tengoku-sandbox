/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Action.Pointwise.Set.Basic
public import Tengoku.Seed.Algebra.Order.Group.Action.End
public import Tengoku.Seed.Order.Preorder.Chain

/-!
# Action on flags

Order isomorphisms act on flags.
-/

public section

open scoped Pointwise

variable {α : Type*}

namespace Flag
variable [Preorder α]

instance : SMul (α ≃o α) (Flag α) where smul e := map e

@[simp, norm_cast]
lemma coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s := rfl

instance : MulAction (α ≃o α) (Flag α) := SetLike.coe_injective.mulAction _ coe_smul

end Flag
