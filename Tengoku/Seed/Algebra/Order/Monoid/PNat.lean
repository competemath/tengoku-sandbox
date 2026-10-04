/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.NonZeroDivisors
public import Tengoku.Seed.Algebra.Order.Hom.Monoid
public import Tengoku.Seed.Data.PNat.Basic

/-!
# Equivalence between `ℕ+` and `nonZeroDivisors ℕ`
-/

@[expose] public section

/-- `ℕ+` is equivalent to `nonZeroDivisors ℕ` in terms of order and multiplication. -/
@[simps]
def PNat.equivNonZeroDivisorsNat : ℕ+ ≃*o nonZeroDivisors ℕ where
  toFun x := ⟨x.val, by simp⟩
  invFun x := ⟨x.val, by simp [Nat.pos_iff_ne_zero]⟩
  map_mul' := by simp
  map_le_map_iff' := by simp
