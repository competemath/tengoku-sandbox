/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P241

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
open Polynomial

/-- competemath.com problem 241. -/
lemma prime_1013 : Nat.Prime 1013 :=
  by
    norm_num

lemma pow_ne_2026 : ∀ {p : ℕ}, Nat.Prime p → ∀ k : ℕ, p ^ k ≠ 2026 :=
  by
    intro p hp k hk
    have h2 : (2:ℕ) ∣ p ^ k := by rw [hk]; norm_num
    have h1013 : (1013:ℕ) ∣ p ^ k := by rw [hk]; norm_num
    have e2 : (2:ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    have e1013 : (1013:ℕ) = p := (Nat.prime_dvd_prime_iff_eq prime_1013 hp).mp
      (Nat.Prime.dvd_of_dvd_pow prime_1013 h1013)
    omega

theorem cyclotomic_2026_eval_one : (Polynomial.cyclotomic 2026 ℤ).eval 1 = 1 :=
  by
    exact Polynomial.eval_one_cyclotomic_not_prime_pow pow_ne_2026

end Native.Competemath.P241

namespace Native.Competemath.P241_2

/-- competemath.com problem 241. -/
theorem cyclotomic_2026_eval_one : (Polynomial.cyclotomic 2026 ℤ).eval 1 = 1 := by
  apply Polynomial.eval_one_cyclotomic_not_prime_pow
  intro p hp k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  case inl => subst hk0; simp at hk
  have hdvd : p ∣ 2026 := hk ▸ dvd_pow_self p hk0.ne'
  have h2026 : (2026:ℕ) = 2 * 1013 := by norm_num
  rw [h2026] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h1013
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2
    subst hp2
    have hklt : k < 11 := by rw [← Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)]; omega
    interval_cases k <;> norm_num at hk
  · have hp1013 : p = 1013 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1013
    subst hp1013
    have hklt : k < 2 := by rw [← Nat.pow_lt_pow_iff_right (a := 1013) (by norm_num)]; omega
    interval_cases k
    norm_num at hk

end Native.Competemath.P241_2

namespace Native.Competemath.P169

/-- competemath.com problem 169. -/
theorem smallest_positive_P6 : IsLeast {n : ℤ | 0 < n ∧ ∃ P : Polynomial ℤ, P.eval 2 = 3 ∧ P.eval 10 = 2027 ∧ P.eval 6 = n} 7 := by
  have h1 : (7:ℤ) ∈ {n : ℤ | 0 < n ∧ ∃ P : Polynomial ℤ, P.eval 2 = 3 ∧ P.eval 10 = 2027 ∧ P.eval 6 = n} := by
    refine ⟨by norm_num, ⟨Polynomial.C 63 * Polynomial.X^2 - Polynomial.C 503 * Polynomial.X + Polynomial.C 757, ?_, ?_, ?_⟩⟩
    · simp
    · simp
    · simp
  have h2 : ∀ n : ℤ, n ∈ {n : ℤ | 0 < n ∧ ∃ P : Polynomial ℤ, P.eval 2 = 3 ∧ P.eval 10 = 2027 ∧ P.eval 6 = n} → (16:ℤ) ∣ (n - 7) := by
    intro n hn
    obtain ⟨hpos, P, hP2, hP10, hP6⟩ := hn
    have s1 : (32:ℤ) ∣ (P.eval 10 - 2 * P.eval 6 + P.eval 2) := by
      have key : ∀ i : ℕ, (32:ℤ) ∣ (10^i - 2*6^i + 2^i) := by
        intro i
        rcases lt_or_ge i 5 with h | h
        · interval_cases i <;> decide
        · have h2 : (2:ℤ)^5 ∣ 2^i := pow_dvd_pow 2 h
          have h10 : (32:ℤ) ∣ 10^i := by
            have : (2:ℤ)^i ∣ 10^i := pow_dvd_pow_of_dvd (by norm_num) i
            calc (32:ℤ) = 2^5 := by norm_num
              _ ∣ 2^i := h2
              _ ∣ 10^i := this
          have h6 : (32:ℤ) ∣ 6^i := by
            have : (2:ℤ)^i ∣ 6^i := pow_dvd_pow_of_dvd (by norm_num) i
            calc (32:ℤ) = 2^5 := by norm_num
              _ ∣ 2^i := h2
              _ ∣ 6^i := this
          have h2' : (32:ℤ) ∣ 2^i := by
            calc (32:ℤ) = 2^5 := by norm_num
              _ ∣ 2^i := h2
          exact dvd_add (dvd_sub h10 (Dvd.dvd.mul_left h6 2)) h2'
      have expand : P.eval 10 - 2 * P.eval 6 + P.eval 2 =
          ∑ i ∈ Finset.range (P.natDegree+1), P.coeff i * (10^i - 2*6^i + 2^i) := by
        rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [expand]
      apply Finset.dvd_sum
      intro i hi
      exact Dvd.dvd.mul_left (key i) _
    rw [hP2, hP10, hP6] at s1
    obtain ⟨k, hk⟩ := s1
    exact ⟨63 - k, by omega⟩
  constructor
  · exact h1
  · intro n hn
    have hpos : 0 < n := hn.1
    obtain ⟨k, hk⟩ := h2 n hn
    omega

end Native.Competemath.P169
