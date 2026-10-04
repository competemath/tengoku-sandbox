/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Group.Nat
public import Tengoku.Seed.Algebra.Order.GroupWithZero.Canonical
public import Tengoku.Seed.Algebra.Order.Ring.Defs
public import Tengoku.Seed.Algebra.Ring.Parity
public import Tengoku.Seed.Order.BooleanAlgebra.Set

/-!
# The natural numbers form an ordered semiring

This file contains the commutative linear ordered semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

public section

namespace Nat

/-! ### Instances -/

instance instIsStrictOrderedRing : IsStrictOrderedRing ℕ where
  mul_lt_mul_of_pos_left _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_right hbc ha

instance instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ where
  bot := 0
  bot_le := zero_le
  isBot_zero := zero_le

/-! ### Miscellaneous lemmas -/

lemma isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_ofPred, isCompl_compl, ← not_even_iff_odd]

end Nat
