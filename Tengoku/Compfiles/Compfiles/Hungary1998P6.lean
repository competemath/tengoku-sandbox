/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# Hungarian Mathematical Olympiad 1998, Problem 6

Let x, y, z be integers with z > 1. Show that

 (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ yᶻ.
-/

namespace Hungary1998P6

lemma sum_range_square_mul_six (n : ℕ) :
    (∑i ∈ Finset.range n, (i + 1)^2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

lemma sum_range_square (n : ℕ) :
    ∑i ∈ Finset.range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1)/6 :=
  by rw [← sum_range_square_mul_six n, Nat.mul_div_cancel]
     norm_num

lemma cast_sum_square (n : ℕ) :
  ∑i ∈ Finset.range n, ((i:ℤ)+1)^2 =
   (((∑i ∈ Finset.range n, (i+1)^2) : ℕ) : ℤ) := by norm_cast

end Hungary1998P6
