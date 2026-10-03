/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 2006, Problem 4

Find all positive integers n for which there exist an integer k ≥ 2 and
positive rational numbers a₁, a₂, ..., aₖ satisfying
a₁ + a₂ + ... + aₖ = a₁ · a₂ · ... · aₖ = n.
-/

namespace Usa2006P4

abbrev SolutionSet : Set ℕ := { n | n = 4 ∨ 6 ≤ n }

/-!
We follow the solution from Evan Chen's notes
(<https://web.evanchen.cc/exams/USAMO-2006-notes.pdf>, problem USAMO 2006/4):

* If `k = 2`, then `(a₁ - a₂)² = n² - 4n` must be the square of a rational
  number; for `n ∈ {1, 2, 3, 5}` this is impossible.
* If `k ≥ 3`, the AM–GM inequality gives `n ^ (k - 1) ≥ k ^ k > 5 ^ (k - 1)`,
  forcing `n ≥ 6`.
* Constructions: `n = 4`: `(2, 2)`; even `n ≥ 6`: `(n/2, 2, 1, …, 1)`;
  `n = 7`: `(4/3, 7/6, 9/2)`; odd `n ≥ 9`: `(n/2, 1/2, 4, 1, …, 1)`.
-/

/-- `5` is not the square of a natural number. -/
lemma not_isSquare_five_nat : ¬ IsSquare (5 : ℕ) := by
  rintro ⟨m, hm⟩
  have hm2 : m ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ m := by lia
    have h9 : 3 * 3 ≤ m * m := Nat.mul_le_mul h3 h3
    lia
  interval_cases m <;> norm_num at hm

/-- `5` is not the square of a rational number. -/
lemma rat_mul_self_ne_five (q : ℚ) : q * q ≠ 5 := by
  intro hq
  have hI : Irrational (Real.sqrt (5 : ℝ)) := by
    have h := Nat.Prime.irrational_sqrt (p := 5) (by norm_num)
    simpa using h
  apply hI
  refine ⟨|q|, ?_⟩
  have hq2 : (q : ℝ) ^ 2 = (5 : ℝ) := by
    have h : (q : ℝ) * q = (5 : ℝ) := by exact_mod_cast hq
    rw [← h]; ring
  rw [Rat.cast_abs, ← hq2, Real.sqrt_sq_eq_abs]

/-- Summing the entries of a list of rationals via `Fin`-indexed access. -/
lemma sum_eq_sum_get (l : List ℚ) : ∑ i : Fin l.length, l.get i = l.sum := by
  rw [← Fin.sum_ofFn, List.ofFn_get]

/-- Multiplying the entries of a list of rationals via `Fin`-indexed access. -/
lemma prod_eq_prod_get (l : List ℚ) : ∏ i : Fin l.length, l.get i = l.prod := by
  rw [← Fin.prod_ofFn, List.ofFn_get]

/-- AM–GM, raised to the `k`-th power, for positive rationals indexed by `Fin k`:
the product is at most the `k`-th power of the arithmetic mean. -/
lemma prod_le_sum_div_pow {k : ℕ} (hk : 0 < k) (z : Fin k → ℚ) (hz : ∀ i, 0 < z i) :
    ((∏ i, z i : ℚ) : ℝ) ≤ (((∑ i, z i : ℚ) : ℝ) / k) ^ k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hzR : ∀ i : Fin k, (0 : ℝ) ≤ (z i : ℝ) := fun i ↦ Rat.cast_nonneg.mpr (hz i).le
  -- weighted AM–GM with uniform weights `1/k`
  have hW := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun (_ : Fin k) ↦ (k : ℝ)⁻¹) (fun (i : Fin k) ↦ (z i : ℝ))
      (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_inv_cancel₀ hkR])
      (fun i _ ↦ hzR i)
  -- raise both sides to the power `k`
  have h1 := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hzR i) _) hW k
  -- simplify the left-hand side: `(∏ zᵢ ^ (1/k)) ^ k = ∏ zᵢ`
  have hL : (∏ i : Fin k, ((z i : ℚ) : ℝ) ^ (k : ℝ)⁻¹) ^ k = ((∏ i, z i : ℚ) : ℝ) := by
    rw [← Finset.prod_pow]
    simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (hzR _), inv_mul_cancel₀ hkR, Real.rpow_one]
    exact (Rat.cast_prod Finset.univ z).symm
  -- simplify the right-hand side: `∑ (1/k) * zᵢ = (∑ zᵢ) / k`
  have hR : (∑ i : Fin k, (k : ℝ)⁻¹ * ((z i : ℚ) : ℝ)) = ((∑ i, z i : ℚ) : ℝ) / k := by
    rw [← Finset.mul_sum, ← Rat.cast_sum, div_eq_mul_inv, mul_comm]
  rwa [hL, hR] at h1

end Usa2006P4
