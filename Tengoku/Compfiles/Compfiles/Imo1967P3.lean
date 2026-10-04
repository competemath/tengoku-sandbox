/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1967, Problem 3

Let $k, m, n$ be natural numbers such that m + k + 1 is a prime greater
than n + 1. Let c(s) = s * (s+1). Prove that the product
(c(m+1) - c(k)) * (c(m+2) - c(k)) * ... * (c(m+n) - c(k)) is divisible
by the product c(1) * c(2) * ... * c(n).
-/

namespace Imo1967P3

lemma aux_1
    (c : ℕ → ℕ)
    (h₁ : ∀ (s : ℕ), c s = s * (s + 1)) :
    ∀ (a b : ℕ), c a - c b = (a - b) * (a + b + 1) := by
  intro a b
  rw [h₁, h₁]
  have h_factor : a + a^2 - (b + b^2) = (a - b) * (a + b + 1) := by rw [tsub_mul]; grind
  grind

lemma aux_1_mono
    (c : ℕ → ℕ)
    (h₁ : ∀ (s : ℕ), c s = s * (s + 1)) :
    Monotone c := by
  intro a b h
  simp only [h₁]
  have h1 : a * (a + 1) ≤ b * (a + 1) := Nat.mul_le_mul_right _ h
  have h2 : b * (a + 1) ≤ b * (b + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ h)
  exact h1.trans h2

lemma aux_2 :
  ∀ (n m : ℕ), 0 < n → n.factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i) := by
  intro s t _
  -- Product equals ascending factorial: (t+1)(t+2)...(t+s) = (t+1).ascFactorial s
  have hprod : ∏ i ∈ Finset.Icc 1 s, (t + i) = (t + 1).ascFactorial s := by
    rw [Nat.ascFactorial_eq_prod_range, ← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hprod]
  exact Nat.factorial_dvd_ascFactorial (t + 1) s

lemma aux_3
  (k m n : ℕ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : Nat.Prime (k + m + 1))
  (h₂ : n + 1 < k + m + 1) :
  (n + 1).factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i + k + 1) := by
  have h₃: ∀ (n m : ℕ), 0 < n → n.factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i) := by
    exact fun (n m : ℕ) (a : 0 < n) ↦ aux_2 n m a
  have h₄: (n + (1 : ℕ)).factorial ∣ (k + m + 1) * (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) := by
    have hn₀ : 0 < n + 1 := Nat.zero_lt_succ n
    have h₈₁: ∀ i, m + i + k + (1 : ℕ) = m + k + (1 : ℕ) + i := by bound
    have h₈₂: (k + m + 1) * (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) = ∏ i ∈ Finset.Ico (0 : ℕ) (n + 1), (m + i + k + (1 : ℕ)) := by
      simp_rw [h₈₁]
      rw [Finset.prod_eq_prod_Ico_succ_bot hn₀ (fun i ↦ m + k + (1 : ℕ) + i)]
      rw [add_zero, add_comm k m]
      exact rfl
    simp_rw [h₈₂]
    have h₈₃: ∏ i ∈ Finset.Ico (0 : ℕ) (n + (1 : ℕ)), (m + i + k + (1 : ℕ)) = ∏ i ∈ Finset.Ico (1 : ℕ) (n + 2), (m + i + k) := by
      rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
      simp
      group
    have h₈₄: ∏ i ∈ Finset.Ico (1 : ℕ) (n + (2 : ℕ)), (m + i + k) = ∏ i ∈ Finset.Icc (1 : ℕ) (n + (1 : ℕ)), (m + i + k) := by rfl
    rw [h₈₃, h₈₄]
    have h₈₅: ∀ i, m + i + k = m + k + i := fun (i : ℕ) ↦ Nat.add_right_comm m i k
    simp_rw [h₈₅]
    exact h₃ (n + 1) (m + k) hn₀
  refine Nat.Coprime.dvd_of_dvd_mul_left ?_ h₄
  refine Nat.Coprime.symm ?_
  exact Nat.Prime.coprime_factorial_of_lt h₁ h₂

lemma aux_4
    (k m n : ℕ)
    (_ : n ≤ k - (m + 1)) :
    ∏ i ∈ Finset.Icc 1 n, (k - (m + i)) = (k - (m + 1)).descFactorial n := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl; intro i _; lia
