/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
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
# International Mathematical Olympiad 2016, Problem 4

A set of positive integers is called *fragrant* if it contains
at least two elements and each of its elements has a prime
factor in common with at least one of the other elements.
Let P(n) = n² + n + 1. What is the least possible value of
positive integer b such that there exists a non-negative integer
a for which the set

  { P(a + 1), P(a + 2), ..., P(a + b) }

is fragrant?
-/

namespace Imo2016P4

abbrev Fragrant (s : Set ℕ+) : Prop :=
  2 ≤ s.ncard ∧ ∀ m ∈ s, ∃ n ∈ s, n ≠ m ∧ ¬Nat.Coprime m n

abbrev P (n : ℕ) : ℕ := n^2 + n + 1

lemma P_inj : Function.Injective P :=
  StrictMono.injective <| strictMono_nat_of_lt_succ fun n ↦ by ring_nf; lia

lemma ncard_set {a : ℕ} {b : ℕ+} : {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)}.ncard = b := by
  have h : {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)} =
      (fun i : ℕ+ ↦ (⟨P (a + i), by positivity⟩ : ℕ+)) '' Set.Icc 1 b := by
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hib, hp⟩
      exact ⟨i, ⟨one_le, hib⟩, PNat.coe_injective hp.symm⟩
    · rintro ⟨i, ⟨-, hib⟩, rfl⟩
      exact ⟨i, hib, rfl⟩
  have hinj : Function.Injective (fun i : ℕ+ ↦ (⟨P (a + i), by positivity⟩ : ℕ+)) := by
    intro i j hij
    have h2 := P_inj (Subtype.mk_eq_mk.mp hij)
    exact PNat.coe_injective (by lia)
  calc {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)}.ncard
      = ((fun i : ℕ+ ↦ (⟨P (a + i), by positivity⟩ : ℕ+)) '' Set.Icc 1 b).ncard :=
        congrArg Set.ncard h
    _ = (Set.Icc 1 b).ncard := Set.ncard_image_of_injective _ hinj
    _ = (Finset.Icc 1 b).card := by rw [← Finset.coe_Icc, Set.ncard_coe_finset]
    _ = b := by rw [PNat.card_Icc]; simp

lemma two_not_dvd_P (n : ℕ) : ¬ 2 ∣ P n := by
  have h : 2 ∣ n * (n + 1) := Even.two_dvd (Nat.even_mul_succ_self n)
  lia

lemma nine_not_dvd_P (n : ℕ) : ¬ 9 ∣ P n := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, n = 3 * m ∨ n = 3 * m + 1 ∨ n = 3 * m + 2 := ⟨n / 3, by lia⟩
  rcases hm with rfl | rfl | rfl <;> lia

lemma dvd_of_dvd_two_mul {g x : ℕ} (hg : ¬ 2 ∣ g) (h : g ∣ 2 * x) : g ∣ x :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hg).symm.dvd_of_dvd_mul_left h

/-- A common divisor of `P (b + k)` and `P b` divides `c` whenever
`P (b + k) - P b = 2 * c`, since values of `P` are odd. -/
lemma gcd_P_dvd_of_eq {b k c : ℕ} (h : P b + 2 * c = P (b + k)) :
    (P (b + k)).gcd (P b) ∣ c := by
  have hodd : ¬ 2 ∣ (P (b + k)).gcd (P b) :=
    fun h' ↦ two_not_dvd_P b (h'.trans (Nat.gcd_dvd_right _ _))
  refine dvd_of_dvd_two_mul hodd ((Nat.dvd_add_right (Nat.gcd_dvd_right _ _)).mp ?_)
  rw [h]
  exact Nat.gcd_dvd_left _ _

/-- Adjacent values of `P` are coprime: a common divisor divides
`(P (b+1) - P b) / 2 = b + 1`, hence divides `P b - b*(b+1) = 1`. -/
lemma coprime_P_succ (b : ℕ) : Nat.Coprime (P (b + 1)) (P b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have h1 : (P (b + 1)).gcd (P b) ∣ b + 1 := gcd_P_dvd_of_eq (by ring)
  refine Nat.dvd_one.mp ((Nat.dvd_add_right (h1.mul_left b)).mp ?_)
  rw [show b * (b + 1) + 1 = P b by ring]
  exact Nat.gcd_dvd_right _ _

/-- The gcd of values of `P` at distance two divides 7. -/
lemma gcd_P_add_two_dvd (b : ℕ) : (P (b + 2)).gcd (P b) ∣ 7 := by
  set g := (P (b + 2)).gcd (P b) with hg
  have hg2 : g ∣ P b := Nat.gcd_dvd_right _ _
  have h1 : g ∣ 2 * b + 3 := gcd_P_dvd_of_eq (by ring)
  have h2 : g ∣ 8 * b + 5 := by
    have h := h1.mul_left (2 * b + 3)
    rw [show (2 * b + 3) * (2 * b + 3) = 4 * P b + (8 * b + 5) by ring] at h
    exact (Nat.dvd_add_right (hg2.mul_left 4)).mp h
  have h3 := h1.mul_left 4
  rw [show 4 * (2 * b + 3) = (8 * b + 5) + 7 by ring] at h3
  exact (Nat.dvd_add_right h2).mp h3

/-- The gcd of values of `P` at distance three divides 3. -/
lemma gcd_P_add_three_dvd (b : ℕ) : (P (b + 3)).gcd (P b) ∣ 3 := by
  set g := (P (b + 3)).gcd (P b) with hg
  have hg2 : g ∣ P b := Nat.gcd_dvd_right _ _
  have h1 : g ∣ 3 * b + 6 := gcd_P_dvd_of_eq (by ring)
  have h2 : g ∣ 27 * b + 27 := by
    have h := h1.mul_left (3 * b + 6)
    rw [show (3 * b + 6) * (3 * b + 6) = 9 * P b + (27 * b + 27) by ring] at h
    exact (Nat.dvd_add_right (hg2.mul_left 9)).mp h
  have h27 : g ∣ 27 := by
    have h := h1.mul_left 9
    rw [show 9 * (3 * b + 6) = (27 * b + 27) + 27 by ring] at h
    exact (Nat.dvd_add_right h2).mp h
  -- since 9 never divides a value of P, the gcd must divide 3
  have h9 : ¬ 9 ∣ g := fun h ↦ nine_not_dvd_P b (h.trans hg2)
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
    (show g ∣ 3 ^ 3 by norm_num; exact h27)
  rw [hgi] at h9 ⊢
  interval_cases i
  · norm_num
  · norm_num
  · exact absurd (by norm_num) h9
  · exact absurd (by norm_num) h9

/-- If values of `P` at distance two have a common factor, that factor is 7. -/
lemma seven_dvd_P_of_not_coprime {b : ℕ} (h : ¬Nat.Coprime (P (b + 2)) (P b)) :
    7 ∣ P (b + 2) ∧ 7 ∣ P b := by
  rw [Nat.coprime_iff_gcd_eq_one] at h
  have h7 : (P (b + 2)).gcd (P b) = 7 :=
    ((Nat.dvd_prime (by norm_num)).mp (gcd_P_add_two_dvd b)).resolve_left h
  exact ⟨h7 ▸ Nat.gcd_dvd_left _ _, h7 ▸ Nat.gcd_dvd_right _ _⟩

/-- If values of `P` at distance three have a common factor, that factor is 3. -/
lemma three_dvd_P_of_not_coprime {b : ℕ} (h : ¬Nat.Coprime (P (b + 3)) (P b)) :
    3 ∣ P (b + 3) ∧ 3 ∣ P b := by
  rw [Nat.coprime_iff_gcd_eq_one] at h
  have h3 : (P (b + 3)).gcd (P b) = 3 :=
    ((Nat.dvd_prime (by norm_num)).mp (gcd_P_add_three_dvd b)).resolve_left h
  have hl := Nat.gcd_dvd_left (P (b + 3)) (P b)
  have hr := Nat.gcd_dvd_right (P (b + 3)) (P b)
  rw [h3] at hl hr
  exact ⟨hl, hr⟩

abbrev Solution : ℕ+ := 6

end Imo2016P4
