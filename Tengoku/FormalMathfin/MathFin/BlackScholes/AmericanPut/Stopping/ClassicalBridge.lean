/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.BrownianModel
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.DividendContact
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.StockConclusion

/-!
# Identification of the financial threshold reduces to identification of price

Once a classical price equals the stopping value, their contact thresholds
agree; no independent identification of boundaries is assumed. The final
curvature transfer still has an explicit price-identification hypothesis.
That hypothesis and classical-solution existence are not proved here.

## Result

Public entry points include `threshold_eq_of_price_identification`, `brownian_boundary_curvature_of_price_identification`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set Boundary
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0} {t : ℝ}

theorem threshold_eq_of_price_identification (hp : DividendPutSolution k h p b)
    (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 < K) (hr : 0 ≤ r) (ht : 0 < t)
    (hprice : ∀ S, 0 < S → americanPutValue P 𝓕 W K r q σ S T = K*p (Real.log (S/K)) t) :
    exerciseThreshold P 𝓕 W K r q σ T = K*Real.exp (b t) := by
  let B := K*Real.exp (b t)
  have hBpos : 0 < B := mul_pos hK (Real.exp_pos _)
  have hBK : B ≤ K := by
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (hp.boundary_nonpos ht)) hK.le
    simpa only [mul_one] using hh
  have hmem : B ∈ exerciseSet P 𝓕 W K r q σ T := by
    refine ⟨hBpos.le,hBK,?_⟩
    rw [hprice B hBpos]
    have hh := (hp.contact_in_stock_units hK hBpos ht).mpr le_rfl
    simpa only [max_eq_left (sub_nonneg.mpr hBK)] using hh
  apply le_antisymm _ (le_csSup exerciseSet_bddAbove hmem)
  apply csSup_le ⟨0,zero_mem_exerciseSet hW hzero hK.le hr⟩
  intro S hS
  by_cases hSpos : 0 < S
  · apply (hp.contact_in_stock_units hK hSpos ht).mp
    rw [← hprice S hSpos,hS.2.2,max_eq_left (sub_nonneg.mpr hS.2.1)]
  · exact (le_of_not_gt hSpos).trans hBpos.le

end MathFin.BlackScholes.AmericanPut.Stopping

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set Boundary ProbabilityTheory Filter
open scoped NNReal Topology

end MathFin.BlackScholes.AmericanPut.Stopping
