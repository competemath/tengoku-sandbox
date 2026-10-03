/-
Copyright (c) 2023 Gian Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Sanjaya
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 2008, Problem 4

Determine all functions f from the positive reals to the positive reals
such that

   (f(w)² + f(x)²) / (f(y)² + f(z)²) = (w² + x²) / (y² + z²)

for all positive real numbers w,x,y,z satisfying xw = yz.
-/

namespace Imo2008P4

abbrev PosReal : Type := { x : ℝ // 0 < x }

lemma positive_pow_eq_pow
    {n : ℕ} (h : 0 < n) {a b : PosReal} : a ^ n = b ^ n ↔ a = b := by
  rw [← Subtype.coe_inj, Positive.val_pow, ← Subtype.coe_inj, Positive.val_pow]
  exact pow_left_inj₀ (le_of_lt a.2) (le_of_lt b.2) (Nat.ne_of_gt h)

-- In mathlib3, mul_two automatically worked on PosReal. In mathlib4 it does not.
-- See https://github.com/leanprover-community/mathlib4/blob/7cc262f36953b78637c096c4bc6634c2af0b2a0a/Mathlib/Algebra/Ring/Defs.lean#L176-L179.
lemma PosReal.mul_two (x : PosReal) : x * ⟨2, two_pos⟩ = x + x := by
  obtain ⟨x, hx⟩ := x
  rw [Subtype.ext_iff]
  simp [_root_.mul_two]

lemma PosReal.two_mul (x : PosReal) : ⟨2, two_pos⟩ * x = x + x := by
  obtain ⟨x, hx⟩ := x
  rw [Subtype.ext_iff]
  simp [_root_.two_mul]

abbrev solution_set : Set (PosReal → PosReal) := { f | f = id ∨ f = fun x ↦ 1 / x }

end Imo2008P4
