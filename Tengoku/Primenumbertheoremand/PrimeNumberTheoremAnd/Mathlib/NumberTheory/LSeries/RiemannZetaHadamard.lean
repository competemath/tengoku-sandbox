/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaValues

/-!
# Hadamard factorization for the completed Riemann zeta function

This file specializes Tao's finite-order Hadamard factorization theorem
([tao246bComplexAnalysis], Thm. 22)
to the entire completed zeta function `completedRiemannZeta₀` (Λ₀) and to Riemann's entire
`riemannXi`. The analytic input is the order-one bound `completedRiemannZeta₀_order_one` from
`ZetaFiniteOrder`; the product is the divisor-indexed canonical Weierstrass product at genus
`⌊ρ⌋ = 1`, with multiplicities from `MeromorphicOn.divisor`.

Note: `completedRiemannZeta` (Λ with simple poles at `0` and `1`) is a different object; Hadamard
applies to Λ₀.  The negative even integers are the trivial zeros of `riemannZeta`, not zeros of
Λ₀.  Accordingly, the divisor indices in this file remain generic zeros of Λ₀ rather than a
separate enumeration of the trivial zeros of ζ.

`RiemannZetaValues` proves `completedRiemannZeta₀_zero_ne_zero`, using the Euler-Mascheroni
formula for `Λ₀(1)` together with explicit numerical bounds.  Therefore the origin monomial in the
Λ₀ Hadamard product is also removable.

## Main results

* `completedRiemannZeta₀_entireOfOrderAtMost_one` : Λ₀ has order at most one
* `riemannXi_entireOfOrderAtMost_one` : Riemann's entire `ξ` has order at most one
* `analyticOrderNatAt_riemannXi_zero` : the origin monomial in `ξ`'s Hadamard product is absent
* `analyticOrderNatAt_completedRiemannZeta₀_zero` : the origin monomial in Λ₀'s Hadamard product
  is absent
* `completedRiemannZeta₀_hadamard_factorization` : canonical product form over divisor indices
* `completedRiemannZeta₀_hadamard_factorization_no_monomial` : Λ₀ product with the origin monomial
  removed
* `riemannXi_hadamard_factorization` : canonical product form for Riemann's entire `ξ`
* `riemannXi_hadamard_factorization_no_monomial`, `_reindex_no_monomial`,
  `_sequence_no_monomial` : xi products with the origin monomial removed
* `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq` : genus-one summability of xi's nonzero
  zero divisor
* `logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum` and
  `logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` : xi-specialized zero-sum identities
* `riemannXi_hadamard_polynomial_derivative_eval_zero_eq` and
  `existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero` : theorem-level uniqueness
  of the xi Hadamard derivative constant
* `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum` : logarithmic derivative formula
  obtained from the xi no-monomial factorization
* `completedRiemannZeta₀_hadamard_factorization_reindex`, `_sequence` : reindexed enumerations

The order-one estimate from `ZetaFiniteOrder` is the finite-order input to
`hadamard_factorization_of_order`.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function background
* [boas1954] and [levin1980] for the general finite-order Hadamard product theorem
* [kadiri2005] for the explicit zero-free-region use of the xi logarithmic derivative

## Tags

Riemann zeta function, Hadamard factorization, canonical product, entire function of finite order
-/

@[expose] public section

noncomputable section

open Complex Set

open scoped BigOperators

/-- The completed zeta function `Λ₀` has order at most one. -/
theorem completedRiemannZeta₀_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) completedRiemannZeta₀ := by
  refine ⟨differentiable_completedZeta₀, ?_⟩
  intro ε hε
  simpa [add_comm, add_left_comm, add_assoc] using
    (Complex.completedRiemannZeta₀_order_one ε hε)

/-- The Riemann xi function `ξ` has order at most one. -/
theorem riemannXi_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) riemannXi := by
  refine ⟨differentiable_riemannXi, ?_⟩
  intro ε hε
  rcases completedRiemannZeta₀_entireOfOrderAtMost_one.exists_bound hε with
    ⟨C, hCpos, hΛ⟩
  let b : ℝ := 1 + ε
  let D : ℝ := 4 / b
  let C' : ℝ := C + D + 1
  have hbpos : 0 < b := by dsimp [b]; linarith
  refine ⟨C', by positivity, ?_⟩
  intro z
  let R : ℝ := 1 + ‖z‖
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have hRpow1 : 1 ≤ R ^ b :=
    Real.one_le_rpow hR1 hbpos.le
  have hpoly : ‖z * (z - 1)‖ ≤ R ^ 2 := by
    have hz : ‖z‖ ≤ R := by dsimp [R]; linarith [norm_nonneg z]
    have hz1 : ‖z - 1‖ ≤ R := by
      simpa [R] using Complex.norm_sub_one_le_one_add_norm z
    calc
      ‖z * (z - 1)‖ ≤ ‖z‖ * ‖z - 1‖ := norm_mul_le z (z - 1)
      _ ≤ R * R := mul_le_mul hz hz1 (norm_nonneg _) (by positivity)
      _ = R ^ 2 := by ring
  have hquad : R ^ 2 ≤ Real.exp (D * R ^ b) := by
    simpa [D] using Real.sq_le_exp_const_mul_rpow (b := b) (r := R) hbpos hR1
  have hΛz : ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C * R ^ b) := by
    simpa [R, b, add_assoc] using hΛ z
  have hterm :
      ‖z * (z - 1) * completedRiemannZeta₀ z‖ ≤
        Real.exp ((C + D) * R ^ b) := by
    calc
      ‖z * (z - 1) * completedRiemannZeta₀ z‖
          ≤ ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ := norm_mul_le _ _
      _ ≤ (R ^ 2) * Real.exp (C * R ^ b) :=
          mul_le_mul hpoly hΛz (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (D * R ^ b) * Real.exp (C * R ^ b) :=
          mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = Real.exp ((C + D) * R ^ b) := by
          rw [← Real.exp_add]
          ring_nf
  have hA_nonneg : 0 ≤ (C + D) * R ^ b := by positivity
  have hone_le : (1 : ℝ) ≤ Real.exp ((C + D) * R ^ b) :=
    Real.one_le_exp_iff.mpr hA_nonneg
  have htwo_exp :
      2 * Real.exp ((C + D) * R ^ b) ≤
        Real.exp (((C + D) * R ^ b) + 1) := by
    calc
      2 * Real.exp ((C + D) * R ^ b)
          = Real.exp (Real.log 2) * Real.exp ((C + D) * R ^ b) := by
              have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
                exact Real.exp_log (by norm_num)
              rw [htwo]
      _ = Real.exp (Real.log 2 + (C + D) * R ^ b) := by
          rw [Real.exp_add]
      _ ≤ Real.exp (((C + D) * R ^ b) + 1) := by
          refine Real.exp_le_exp.2 ?_
          have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            have h := Real.add_one_le_exp (1 : ℝ)
            norm_num at h
            exact h
          linarith
  have hxi :
      ‖riemannXi z‖ ≤ Real.exp (((C + D) * R ^ b) + 1) := by
    calc
      ‖riemannXi z‖
          = ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖ / 2 := by
              simp [riemannXi]
      _ ≤ (‖z * (z - 1) * completedRiemannZeta₀ z‖ + 1) / 2 := by
          gcongr
          simpa using norm_add_le (z * (z - 1) * completedRiemannZeta₀ z) (1 : ℂ)
      _ ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + 1 := by
          nlinarith [norm_nonneg (z * (z - 1) * completedRiemannZeta₀ z)]
      _ ≤ Real.exp ((C + D) * R ^ b) + 1 := by
          gcongr
      _ ≤ 2 * Real.exp ((C + D) * R ^ b) := by
          linarith
      _ ≤ Real.exp (((C + D) * R ^ b) + 1) := htwo_exp
  exact hxi.trans (Real.exp_le_exp.2 (by
    calc
      ((C + D) * R ^ b) + 1 ≤ ((C + D) * R ^ b) + R ^ b := by
          gcongr
      _ = C' * R ^ b := by
          ring))

/-! ### Logarithmic-derivative identities -/

/-- Since `ξ(0) = 1 / 2`, the monomial exponent in the origin-centered Hadamard product is zero. -/
theorem analyticOrderNatAt_riemannXi_zero : analyticOrderNatAt riemannXi 0 = 0 := by
  by_contra h
  have hzero : riemannXi 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := riemannXi) (z₀ := 0) h
  rw [riemannXi_zero] at hzero
  norm_num at hzero

/-- Since `Λ₀(0) ≠ 0`, the monomial exponent in the origin-centered Hadamard product for Λ₀ is
zero. -/
theorem analyticOrderNatAt_completedRiemannZeta₀_zero :
    analyticOrderNatAt completedRiemannZeta₀ 0 = 0 := by
  by_contra h
  have hzero : completedRiemannZeta₀ 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := completedRiemannZeta₀) (z₀ := 0) h
  exact completedRiemannZeta₀_zero_ne_zero hzero
