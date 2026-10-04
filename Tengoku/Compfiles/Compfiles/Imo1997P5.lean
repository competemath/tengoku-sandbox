/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, Ilmārs Cīrulis
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1997, Problem 5

Determine all pairs of integers 1 ≤ a,b that satisfy a ^ (b ^ 2) = b ^ a.
-/

namespace Imo1997P5

lemma ineq₁ {n b : ℕ} (hb : 2 ≤ b) (hn : 5 ≤ n) : n < b ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num; linarith [Nat.pow_le_pow_left hb 3]
  | succ n hn iH => rw [show n + 1 - 2 = n - 2 + 1 by lia, Nat.pow_succ]; nlinarith

lemma ineq₂ {n b : ℕ} (hb : 2 ≤ b) (hn : 5 ≤ n) : n * b ^ 2 < b ^ n := by
  nth_rw 2 [show n = n - 2 + 2 by lia]
  rw [Nat.pow_add]
  nlinarith [ineq₁ hb hn]

lemma ineq₃ {x y b : ℕ} (hb : 2 ≤ b) (hxy : x < y) : b + x < b ^ 2 * y := by
  induction b, hb using Nat.le_induction <;> nlinarith

lemma ineq₄ {b : ℕ} (n : ℕ) (hb : 2 ≤ b) : b * n < (b ^ n) ^ 2 := by
  induction n with
  | zero => simp
  | succ n iH => ring_nf at *; exact ineq₃ hb iH

lemma aux₁ {n b : ℕ} (h : n * b ^ 2 = b ^ n) : b ≤ 1 ∨ n ≤ 4 := by grind [ineq₂]

lemma aux₂ {n b : ℕ} (h : b * n = (b ^ n) ^ 2) : b ≤ 1 := by grind [ineq₄]

lemma aux₃ {n a b c d : ℕ} (hb : b ≠ 0) (h : c ^ b = d ^ b * n ^ a) : d ∣ c :=
  (Nat.pow_dvd_pow_iff hb).mp (Dvd.intro (n ^ a) h.symm)

abbrev solution_set : Set (ℕ × ℕ) := {(1, 1), (16, 2), (27, 3)}

end Imo1997P5
