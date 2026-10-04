/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Constantin Seebach
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1991, Problem 6

An infinite sequence x₀,x₁,x₂,... of real numbers is said to be *bounded*
if there is a constant C such that |xᵢ| ≤ C for every i ≥ 0.

Given any real number a > 1, construct a bounded infinite sequence
x₀,x₁,x₂,... such that

                  |xᵢ - xⱼ|⬝|i - j|ᵃ ≥ 1

for every pair of distinct nonnegative integers i, j.
-/

namespace Imo1991P6

abbrev Bounded (x : ℕ → ℝ) : Prop := ∃ C, ∀ i, |x i| ≤ C

/-!
We take the sequence construction from https://artofproblemsolving.com/wiki/index.php/1991_IMO_Problems/Problem_6, Solution 2.
-/

theorem fract_sqrt_two_mul_gt (k : ℕ) (pk : 0 < k) : 1 / (2 * (√2 * k + 1)) < Int.fract (√2 * k) := by
  rw [div_lt_iff₀ (by positivity)]

  set x : ℝ := √2 * k
  let y := ⌊x⌋
  have fract_eq : Int.fract x = x - y := rfl
  have : x > 0 := by positivity
  have : 0 ≤ (y:ℝ) := by positivity

  have fract_pos : 0 < Int.fract x := by
    have := (irrational_sqrt_two.mul_ratCast (q:=k) (Nat.cast_ne_zero.mpr pk.ne')).ne_rat y
    rw [Int.fract_pos]
    apply this

  have h_diff : (x - y) * (x + y) = 2 * k ^ 2 - y ^ 2 := by
    rw [show 2 * k ^ 2 = x^2 by unfold x; simp [mul_pow]]
    rw [mul_comm, sq_sub_sq]

  have h_diff_pos : 2 * k ^ 2 - y ^ 2 ≥ 1 := by
    apply Int.le_of_sub_one_lt
    rify
    rw [← h_diff]
    nlinarith

  rify at h_diff_pos
  rw [fract_eq]
  nlinarith

section Int.fract
open Int
variable {R : Type} [Ring R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] [AddLeftMono R]

theorem Int.fract_sub_eq (a b : R) : ∃ z : Fin 2, fract (a - b) = fract a - fract b + z := by
  by_cases h1 : fract b ≤ fract a
  · use 0
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, add_zero]
    rw [fract_eq_iff]
    and_intros
    · exact sub_nonneg_of_le h1
    · rw [sub_lt_iff_lt_add]
      apply lt_of_lt_of_le (b:=1) <;> simp [fract_lt_one _]
    · rw [fract, fract]
      use ⌊a⌋-⌊b⌋
      rw [Int.cast_sub, sub_sub_sub_comm, sub_sub_cancel, sub_sub_cancel]
  · simp at h1
    use 1
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one]
    rw [fract_eq_iff]
    and_intros
    · rw [add_comm, add_sub, le_sub_iff_add_le]
      apply le_trans (b:=1) <;> simp [le_of_lt (fract_lt_one _)]
    · exact (add_lt_add_left (sub_neg_of_lt h1) 1).trans_eq (zero_add (1 : R))
    · rw [fract, fract]
      use ⌊a⌋-⌊b⌋-1
      rw [Int.cast_sub, Int.cast_sub, sub_sub_sub_comm, sub_add, sub_sub_cancel]
      simp

end Int.fract

theorem one_sub_fract_sqrt_two_mul_gt (k : ℕ) (kpos : 0 < k) : 1 / (2*(√2*k + 1)) < 1 - Int.fract (√2 * k) := by
  rw [div_lt_iff₀ (by positivity)]
  set x : ℝ := √2 * k
  let y := ⌊x⌋
  have fract_eq : Int.fract x = x - y := rfl
  have : x > 0 := by positivity
  have : 0 ≤ (y:ℝ) := by positivity

  have h_diff : ((y:ℝ) + 1 - x) * ((y:ℝ) + 1 + x) = (y + 1) ^ 2 - 2 * k ^ 2 := by
    rw [show 2 * k ^ 2 = x ^ 2 by unfold x; simp [mul_pow]]
    rw [mul_comm, sq_sub_sq]

  have h_diff_pos : (y + 1) ^ 2 - 2 * (k:ℤ) ^ 2 ≥ 1 := by
    apply Int.le_of_sub_one_lt
    rify
    rw [← h_diff]
    nlinarith [Int.fract_lt_one x, fract_eq]

  rify at h_diff_pos
  rw [fract_eq]
  nlinarith [Int.floor_le x]

theorem abs_fract_sqrt_two_mul_sub_fract_sqrt_two_mul (i j : ℕ) (hji : j < i) : 1 / (2*(√2*(i-j) + 1)) < |Int.fract (√2 * i) - Int.fract (√2 * j)| := by
  apply (Int.fract_sub_eq (√2 * i) (√2 * j)).elim
  rw [Fin.forall_fin_two]
  and_intros
  · intro h
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, add_zero] at h
    rw [← h, ← mul_sub, ← Nat.cast_sub (le_of_lt hji)]
    apply lt_of_lt_of_le (fract_sqrt_two_mul_gt _ _) (le_abs_self _)
    exact Nat.zero_lt_sub_of_lt hji
  · intro h
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one] at h
    rw [← sub_eq_iff_eq_add] at h
    rw [sub_eq_sub_iff_comm] at h
    rw [abs_sub_comm, ← h, ← mul_sub, ← Nat.cast_sub (le_of_lt hji), abs_of_nonneg]
    · apply one_sub_fract_sqrt_two_mul_gt
      exact Nat.zero_lt_sub_of_lt hji
    · simp [le_of_lt (Int.fract_lt_one _)]

noncomputable abbrev solution (a : ℝ) (ha : 1 < a) : ℕ → ℝ :=
  fun n => (2*√2 + 2) * Int.fract (√2 * n)

end Imo1991P6
