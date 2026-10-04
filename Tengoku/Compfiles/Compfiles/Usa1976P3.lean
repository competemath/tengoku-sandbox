/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1976, Problem 3

Determine all integral solutions of a² + b² + c² = a²b².
-/

namespace Usa1976P3

abbrev solution_set : Set (ℤ × ℤ × ℤ) := { ⟨0, 0, 0⟩ }

lemma sq_emod_four (n : ℤ) : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; grind
  right; grind

lemma even_of_sum_sq_emod_four_eq_zero (a b c : ℤ) (h : (a^2 + b^2 + c^2) % 4 = 0) :
    Even a ∧ Even b ∧ Even c := by
  have even_of_sq_zero : ∀ n : ℤ, n^2 % 4 = 0 → Even n := by
    intro n hn
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, rfl⟩
    · have : (2 * k + 1) ^ 2 % 4 = 1 := by
        ring_nf; rw [Int.add_emod]; simp
      rw [this] at hn
      contradiction
  have ha := sq_emod_four a
  have hb := sq_emod_four b
  have hc := sq_emod_four c
  rw [Int.add_emod, Int.add_emod] at h
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact ⟨even_of_sq_zero a ha, even_of_sq_zero b hb, even_of_sq_zero c hc⟩
  all_goals grind

lemma even_of_sum_sq_eq_sq_mul_sq (a b c : ℤ) (h : a^2 + b^2 + c^2 = a^2 * b^2) :
    Even a ∧ Even b ∧ Even c := by
  have even_of_sq_zero : ∀ n : ℤ, n^2 % 4 = 0 → Even n := by
    intro n hn
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, rfl⟩
    · rw [show (2 * k + 1) ^ 2 % 4 = 1 by ring_nf; rw [Int.add_emod]; simp] at hn
      contradiction
  have h_mod : (a^2 + b^2 + c^2) % 4 = (a^2 * b^2) % 4 := congr_arg (· % 4) h
  rw [Int.add_emod, Int.add_emod, Int.mul_emod] at h_mod
  have ha := sq_emod_four a
  have hb := sq_emod_four b
  have hc := sq_emod_four c
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact ⟨even_of_sq_zero a ha, even_of_sq_zero b hb, even_of_sq_zero c hc⟩
  all_goals grind

lemma descent_step (a b c : ℤ) (k : ℕ) (h : a^2 + b^2 + c^2 = (4:ℤ)^k * a^2 * b^2) :
    ∃ a' b' c', a = 2 * a' ∧ b = 2 * b' ∧ c = 2 * c' ∧
    a'^2 + b'^2 + c'^2 = (4:ℤ)^(k + 1) * a'^2 * b'^2 := by
  have heven : Even a ∧ Even b ∧ Even c := by
    cases k with
    | zero =>
      simp only [pow_zero, one_mul] at h
      exact even_of_sum_sq_eq_sq_mul_sq a b c h
    | succ n =>
      apply even_of_sum_sq_emod_four_eq_zero
      rw [h]
      rw [pow_succ, mul_assoc]
      grind
  obtain ⟨a', rfl⟩ := heven.1
  obtain ⟨b', rfl⟩ := heven.2.1
  obtain ⟨c', rfl⟩ := heven.2.2
  grind

lemma eq_zero_of_forall_two_pow_dvd (a : ℤ) (h : ∀ n : ℕ, (2:ℤ)^n ∣ a) : a = 0 := by
  by_contra h_neq
  have h_pos : 0 < a.natAbs := Int.natAbs_pos.mpr h_neq
  let n := a.natAbs
  have h_lt : n < 2^n := Nat.lt_pow_self (by decide)
  have h_dvd : 2^n ∣ n := by
    have h_nat := Int.natAbs_dvd_natAbs.mpr (h n)
    rw [Int.natAbs_pow] at h_nat
    exact h_nat
  have h_le : 2^n ≤ n := Nat.le_of_dvd h_pos h_dvd
  linarith

lemma eq_zero_of_solution_aux (a : ℤ) :
    ∀ b c k, a^2 + b^2 + c^2 = (4:ℤ)^k * a^2 * b^2 → a = 0 := by
  intros b c k h
  apply eq_zero_of_forall_two_pow_dvd a
  intro n
  revert a b c k h
  induction n with
  | zero =>
    intros
    exact one_dvd _
  | succ n ih =>
    intros a b c k h
    obtain ⟨a', b', c', ha, _, _, h_new⟩ := descent_step a b c k h
    rw [ha]
    rw [pow_succ']
    apply Int.mul_dvd_mul_left
    exact ih a' b' c' (k + 1) h_new

end Usa1976P3
