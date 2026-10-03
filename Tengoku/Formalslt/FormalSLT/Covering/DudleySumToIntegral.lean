import Tengoku.Formalslt.FormalSLT.Covering.DudleyChainingSum
import Tengoku.Formalslt.FormalSLT.Covering.TotalBoundedDudley

/-!
# Finite Dudley sum-to-integral comparison

This module closes the finite G3 Dudley lane: q086 gives the centered
finite-net chaining sum, and this file compares the dyadic entropy sum with a
truncated entropy integral.

All statements stay finite-scale. The terminal theorem is stated for finite
outcome spaces, finite index sets, and an abstract finite covering-number
profile supplied by the caller.
-/

namespace FormalSLT.Covering.DudleySumToIntegral

open Finset
open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.DudleyChainingSum

noncomputable section

variable {Ω T : Type*}

/-- Entropy from a positive antitone covering-number profile is antitone. -/
theorem coveringNumber_entropy_antitone
    (coveringNumberAtRadius : ℝ → ℕ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε) :
    Antitone
      (fun ε : ℝ => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  intro ε δ hεδ
  apply Real.sqrt_le_sqrt
  have hpos : 0 < (coveringNumberAtRadius δ : ℝ) := by
    exact_mod_cast hcover_pos δ
  have hle :
      (coveringNumberAtRadius δ : ℝ) ≤ (coveringNumberAtRadius ε : ℝ) := by
    exact_mod_cast hcover_antitone hεδ
  exact Real.log_le_log hpos hle

/--
Interval integrability of the finite covering-number entropy profile from
antitonicity and positivity.
-/
theorem coveringNumber_entropy_integrable_of_antitone
    (coveringNumberAtRadius : ℝ → ℕ) (a b : ℝ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε) :
    IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
      MeasureTheory.volume a b := by
  exact (coveringNumber_entropy_antitone
    coveringNumberAtRadius hcover_antitone hcover_pos).intervalIntegrable

/--
Interval-integrability compatibility wrapper for callers that still carry a
finite boundedness receipt on the interval.
-/
theorem coveringNumber_entropy_integrable
    (coveringNumberAtRadius : ℝ → ℕ) (a b : ℝ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (_hcover_bound : ∃ M : ℕ,
      ∀ ε ∈ Set.uIcc a b, coveringNumberAtRadius ε ≤ M)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε) :
    IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
      MeasureTheory.volume a b := by
  exact coveringNumber_entropy_integrable_of_antitone
    coveringNumberAtRadius a b hcover_antitone hcover_pos

/--
Dyadic upper-sum comparison for an abstract antitone entropy profile. The
factor is `2` for the finite truncated interval
`[radiusScale / 2^(m+1), radiusScale / 2]`; the later Dudley theorem pays one
more factor `2` when rewriting geometric radii as dyadic annulus widths.
-/
theorem dyadic_sum_le_entropy_integral
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m entropyAtRadius ≤
      2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
        entropyAtRadius ε := by
  exact
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral
      (m := m) (entropyAtRadius := entropyAtRadius)
      hradiusScale_nonneg hentropy_antitone hintervalIntegrable

end

end FormalSLT.Covering.DudleySumToIntegral
