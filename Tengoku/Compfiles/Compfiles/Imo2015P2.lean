/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 2015, Problem 2

Determine all triples of positive integers a, b, c such that each of
ab - c, bc - a, ca - b is a power of two.
-/

namespace Imo2015P2

abbrev SolutionSet : Set (ℤ × ℤ × ℤ) := {
  (2, 2, 2),
  (2, 2, 3), (2, 3, 2), (3, 2, 2),
  (2, 6, 11), (6, 11, 2), (11, 2, 6),
  (11, 6, 2), (6, 2, 11), (2, 11, 6),
  (3, 5, 7), (5, 7, 3), (7, 3, 5),
  (7, 5, 3), (5, 3, 7), (3, 7, 5)
}

def is_power_of_two (n : ℤ) : Prop := ∃ m : ℕ, n = 2 ^ m

lemma pow_of_two_coprime_odd (m : ℕ) {a : ℤ} (ha : ¬2 ∣ a) :
    IsCoprime ((2 : ℤ) ^ m) a := by
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_pow, ← Int.ofNat_two]
  rw [Int.natAbs_natCast, Nat.coprime_comm]
  apply Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two
  rw [← Int.ofNat_dvd, Int.ofNat_two, Int.dvd_natAbs]
  exact ha

lemma pow_of_two_dvd_odd_mul_self_sub_1 {m : ℕ} {a : ℤ}
    (ha : ¬2 ∣ a) (ha' : 1 < a) (h : (2 : ℤ) ^ m ∣ a ^ 2 - 1) :
    (2 : ℤ) ^ m ≤ 2 * a + 2 := by
  rw [Int.two_dvd_ne_zero, ← Int.odd_iff, odd_iff_exists_bit1] at ha
  rcases ha with ⟨k, hk⟩
  rw [hk] at h ⊢
  by_cases! hk' : 2 ∣ k
  · rw [(by ring : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1))] at h
    have h' : 2 ^ m ∣4 * k := by
      apply IsCoprime.dvd_of_dvd_mul_right _ h
      apply pow_of_two_coprime_odd m
      rw [← even_iff_two_dvd] at hk' ⊢
      rw [Int.not_even_iff_odd]
      exact Even.add_one hk'
    calc 2 ^ m
        ≤ 4 * k := Int.le_of_dvd (by lia) h'
      _ ≤ 2 * (2 * k + 1) + 2 := by lia
  · rw [(by ring : (2 * k + 1) ^ 2 - 1 = (4 * k + 4) * k)] at h
    have h' : 2 ^ m ∣4 * k + 4 := by
      apply IsCoprime.dvd_of_dvd_mul_right _ h
      exact pow_of_two_coprime_odd m hk'
    calc 2 ^ m
        ≤ 4 * k + 4 := Int.le_of_dvd (by lia) h'
      _ ≤ 2 * (2 * k + 1) + 2 := by lia

lemma dvd_pow_of_two {m : ℕ} {a : ℤ}
    (ha' : 0 ≤ a) (h : a ∣ 2 ^ m) : ∃ k : ℕ, a = 2 ^ k := by
  lift a to ℕ using ha'
  norm_cast at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨k, by exact_mod_cast hk⟩

lemma odd_dvd_pow_of_two {m : ℕ} {a : ℤ}
    (ha : ¬2 ∣ a) (ha' : 0 ≤ a) (h : a ∣ 2 ^ m) : a = 1 := by
  rcases dvd_pow_of_two ha' h with ⟨k,  hk⟩
  rw [hk] at ha ⊢
  contrapose! ha
  apply dvd_pow_self
  contrapose! ha
  rw [ha]
  norm_num

lemma sq_pow_of_two_sub_two {m₁ m₂ : ℕ} {a : ℤ} (ha : 2 ≤ a)
    (h₁ : a ∣ 2 ^ m₁) (h₂ : a ^ 2 - 2 ∣ 2 ^ m₂)
    : a = 2 := by
  apply dvd_pow_of_two (by lia) at h₁
  have ha' : 0 ≤ a ^ 2 - 2 := by
    rw [sub_nonneg]
    calc 2
        ≤ 2 ^ 2 := by norm_num
      _ ≤ a ^ 2 := (pow_le_pow_iff_left₀ (by norm_num) (by lia) (by norm_num)).mpr ha
  apply dvd_pow_of_two ha' at h₂
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  rw [hk₁] at ha hk₂ ⊢
  have hk₁' : k₁ ≠ 0 := by
    contrapose! ha with h'
    rw [h']
    norm_num
  apply Nat.exists_eq_add_one_of_ne_zero at hk₁'
  rcases hk₁' with ⟨k, hk⟩
  rw [hk] at hk₂ ⊢
  rw [(by ring : ((2 : ℤ) ^ (k + 1)) ^ 2 - 2 = 2 * (2 * 2 ^ (2 * k) - 1))] at hk₂
  have h' : ¬(2 : ℤ) ∣ 2 * 2 ^ (2 * k) - 1 := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    exact Even.sub_odd (even_two_mul _) odd_one
  have h'' : (0 : ℤ) ≤ 2 * 2 ^ (2 * k) - 1 := by
    rw [sub_nonneg, ← zero_add 1, Int.add_one_le_iff]
    positivity
  have h''' := dvd_mul_left (2 * 2 ^ (2 * k) - 1) (2 : ℤ)
  rw [hk₂] at h'''
  apply odd_dvd_pow_of_two h' h'' at h'''
  have hk' : k = 0 := by
    contrapose! h'''
    apply ne_of_gt
    rw [lt_sub_iff_add_lt]
    norm_num
    calc (1 : ℤ)
      < 2 ^ (2 * 1) := by norm_num
    _ ≤ 2 ^ (2 * k) := by
      rw [pow_le_pow_iff_right₀ (by norm_num)]
      rw [mul_le_mul_iff_right₀ (by norm_num)]
      rw [Nat.one_le_iff_ne_zero]
      exact h'''
  rw [hk']
  norm_num

lemma swap_ab_solution (a b c : ℤ) : (a,b,c) ∈ SolutionSet ↔ (b,a,c) ∈ SolutionSet := by
  simp
  constructor <;> intro h <;> casesm* _ ∨ _
    <;> rcases h with ⟨ha, hb, hc⟩ <;> rw [ha, hb, hc] <;> norm_num

lemma swap_bc_solution (a b c : ℤ) : (a,b,c) ∈ SolutionSet ↔ (a,c,b) ∈ SolutionSet := by
  simp
  constructor <;> intro h <;> casesm* _ ∨ _
    <;> rcases h with ⟨ha, hb, hc⟩ <;> rw [ha, hb, hc] <;> norm_num

end Imo2015P2
