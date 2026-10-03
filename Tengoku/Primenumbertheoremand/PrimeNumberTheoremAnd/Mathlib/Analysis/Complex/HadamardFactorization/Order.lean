/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Tengoku.Primenumbertheoremand.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Growth

/-!
# Hadamard factorization for finite-order entire functions

Upgrades `hadamard_factorization_of_growth` to the finite-order formulation via
`EntireOfOrderAtMost` and sequence- or divisor-indexed canonical products.

The growth input is routed through a midpoint exponent `τ` with `⌊τ⌋ = ⌊ρ⌋` so genus
`⌊ρ⌋` matches Tao's Weierstrass factor degree.

This file proves the finite-order Hadamard factorization theorem, corresponding to
[tao246bComplexAnalysis], Theorem 22.  The sequence-indexed theorem below packages the same
factorization after choosing an enumeration of the nonzero divisor indices.

## Main results

* `hadamard_factorization_of_order` : `f = exp(P) · z^k · ∏' E_m(z/a)`
* `hadamard_factorization_of_order_sequence` : sequence-indexed reindexing of the zero divisor
* `hadamard_factorization_of_order_centered` : arbitrary-center form, derived by translation
* `EntireOfOrderAtMost` : order at most `ρ` in the `ε`-family sense

## References

* [tao246bComplexAnalysis], Theorem 22
* [boas1954] and [levin1980] for the classical finite-order Hadamard product theorem, including
  genus `⌊ρ⌋` for functions of order at most `ρ`
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

/-- Translating the input moves the origin order to the order at the translation center. -/
lemma analyticOrderNatAt_comp_add_const (f : ℂ → ℂ) (c : ℂ) :
    analyticOrderNatAt (fun w : ℂ => f (w + c)) 0 = analyticOrderNatAt f c := by
  let g : ℂ → ℂ := fun w => w + c
  have hg : AnalyticAt ℂ g 0 := by fun_prop
  have hg' : deriv g 0 ≠ 0 := by
    simp [g]
  have h :=
    analyticOrderAt_comp_of_deriv_ne_zero (f := f) (g := g) (z₀ := (0 : ℂ)) hg hg'
  have h' :
      analyticOrderAt ((fun x : ℂ => f x) ∘ g) 0 = analyticOrderAt f c := by
    simpa [g] using h
  simpa [analyticOrderNatAt, g] using! congrArg ENat.toNat h'

/-- Subtracting a constant is the corresponding special case of translation for the origin order. -/
lemma analyticOrderNatAt_comp_sub_const (f : ℂ → ℂ) (c : ℂ) :
    analyticOrderNatAt (fun w : ℂ => f (w - c)) 0 = analyticOrderNatAt f (-c) := by
  simpa [sub_eq_add_neg] using analyticOrderNatAt_comp_add_const f (-c)

/-- The centered Hadamard denominator is the ordinary denominator for the translated function. -/
theorem centeredHadamardDenom_eq_hadamardDenom_translate
    (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    centeredHadamardDenom m c f z =
      hadamardDenom m (fun w : ℂ => f (w + c)) (z - c) := by
  simp [centeredHadamardDenom, hadamardDenom, analyticOrderNatAt_comp_add_const]

/-- An entire function has order at most `ρ` if it satisfies the `ε`-family growth bound used in
this formalization.

For every `ε > 0`, the norm is bounded by an exponential of order `ρ + ε`. This formulation is
the convenient finite-order input for the Jensen/counting estimates used in the Hadamard
factorization pipeline. -/
def EntireOfOrderAtMost (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
    Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))

namespace EntireOfOrderAtMost

theorem differentiable {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f) :
    Differentiable ℂ f :=
  h.1

theorem exists_bound {ρ ε : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
  h.2 ε hε

/-- A single exponential bound of order `ρ` implies the `ε`-family bound defining
`EntireOfOrderAtMost`. -/
theorem of_norm_le_exp {ρ : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hbound : ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)) :
    EntireOfOrderAtMost ρ f := by
  refine ⟨hf, ?_⟩
  rintro ε hε
  rcases hbound with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  exact Real.norm_le_exp_mul_rpow_of_exponent_le (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hC.le
    (fun z => by linarith [norm_nonneg z]) (by linarith : ρ ≤ ρ + ε) hCbound

/-- A finite-order bound gives a logarithmic growth bound at any larger exponent. -/
theorem exists_log_growth {ρ τ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hτ : ρ < τ) (hτ_nonneg : 0 ≤ τ) :
    ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
  rcases h.exists_bound (sub_pos.2 hτ) with ⟨C, hCpos, hC⟩
  have hnorm : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
    intro z
    simpa [sub_add_cancel] using (hC z)
  exact Real.log_growth_of_norm_le_exp_mul_rpow (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ_nonneg
    (fun z => by linarith [norm_nonneg z]) hnorm

/-- Finite order is invariant under translation of the input. -/
theorem comp_add_const {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hρ : 0 ≤ ρ) (c : ℂ) :
    EntireOfOrderAtMost ρ (fun z : ℂ => f (z + c)) := by
  refine ⟨h.differentiable.comp (differentiable_id.add (differentiable_const c)), ?_⟩
  intro ε hε
  rcases h.exists_bound hε with ⟨C, hC, hCbound⟩
  let A : ℝ := 1 + ‖c‖
  let C' : ℝ := C * A ^ (ρ + ε)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hτnonneg : 0 ≤ ρ + ε := by linarith
  refine ⟨C', mul_pos hC (Real.rpow_pos_of_pos hApos _), ?_⟩
  intro z
  have hbase :
      1 + ‖z + c‖ ≤ A * (1 + ‖z‖) := by
    dsimp [A]
    have hnorm : ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le z c
    nlinarith [norm_nonneg z, norm_nonneg c]
  have hpow :
      (1 + ‖z + c‖) ^ (ρ + ε) ≤ (A * (1 + ‖z‖)) ^ (ρ + ε) := by
    exact Real.rpow_le_rpow (by positivity) hbase hτnonneg
  calc
    ‖f (z + c)‖ ≤ Real.exp (C * (1 + ‖z + c‖) ^ (ρ + ε)) := hCbound (z + c)
    _ ≤ Real.exp (C' * (1 + ‖z‖) ^ (ρ + ε)) := by
      refine Real.exp_le_exp.2 ?_
      calc
        C * (1 + ‖z + c‖) ^ (ρ + ε) ≤ C * (A * (1 + ‖z‖)) ^ (ρ + ε) := by
          exact mul_le_mul_of_nonneg_left hpow hC.le
        _ = C' * (1 + ‖z‖) ^ (ρ + ε) := by
          rw [Real.mul_rpow (le_of_lt hApos) (by positivity : 0 ≤ 1 + ‖z‖)]
          ring

/-- Finite order is invariant under subtracting a constant from the input. -/
theorem comp_sub_const {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hρ : 0 ≤ ρ) (c : ℂ) :
    EntireOfOrderAtMost ρ (fun z : ℂ => f (z - c)) := by
  simpa [sub_eq_add_neg] using h.comp_add_const hρ (-c)

end EntireOfOrderAtMost

end Complex.Hadamard
