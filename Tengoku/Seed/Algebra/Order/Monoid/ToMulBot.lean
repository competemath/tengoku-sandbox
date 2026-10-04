/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.GroupWithZero.Canonical
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.TypeTags
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.WithTop

/-!
Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

@[expose] public section


universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _

@[simp]
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

@[simp]
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α) :=
  rfl

@[simp]
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

@[simp]
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

variable [Preorder α] (a b : WithZero (Multiplicative α))

theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun _ _ => id

@[simp]
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl

end WithZero
