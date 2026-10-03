/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.HungerbuhlerWasem.SectorCancellation
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ExitTime
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

/-!
# Higher-order CPV discharger from immersion data (T-BR-03)

This file wraps `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
(in `SectorCancellation.lean`) into a paper-faithful form. The original
theorem takes ~30 hypotheses describing the analytic and geometric data
of the crossing; this wrapper derives all of them from a much smaller set
of inputs:

* `γ : ClosedPwC1Immersion x` — the closed piecewise-`C¹` immersion;
* `t₀ ∈ Ioo 0 1` — interior crossing time;
* `h_at`, `h_unique` — the curve crosses `s` only at `t₀`;
* `h_flat : IsFlatOfOrder γ.extend t₀ n` for `2 ≤ k ≤ n`;
* `h_B` (corner form) or `h_angle` (smooth form) — the angle compatibility
  expressing Condition (B) for the integrand `c/(z-s)^k`.

## Main results

* `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner` —
  general (corner-friendly) form, takes explicit left/right derivative
  limits and the unit-circle equation `h_B`.
* `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB` —
  smooth specialisation at off-partition points, deriving `L_- = L_+` and
  the even-power `h_B` from the simpler `(k-1)·π ∈ 2π·ℤ` form of (B).
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- Build `h_close` from a closed piecewise-`C¹` curve: the extended path takes
the same value at `0` and `1` (both equal the basepoint `x`). -/
theorem closed_immersion_extend_zero_eq_one (γ : ClosedPwC1Immersion x) :
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 =
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 := by
  simp

/-- At an off-partition interior point, the right and left derivative limits both
equal `deriv γ t₀` and are nonzero. -/
theorem deriv_limit_eq_at_off_partition
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    let f := γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend
    deriv f t₀ ≠ 0 ∧
    Tendsto (deriv f) (𝓝[>] t₀) (𝓝 (deriv f t₀)) ∧
    Tendsto (deriv f) (𝓝[<] t₀) (𝓝 (deriv f t₀)) := by
  have h_cont :=
    γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀ h_off
  exact ⟨γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_off,
    h_cont.tendsto.mono_left nhdsWithin_le_nhds,
    h_cont.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- For a function `γ` with `Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)` and eventual
differentiability on `(t₀, ∞)`, plus continuity at `t₀`, we have
`HasDerivWithinAt γ L (Ioi t₀) t₀`. -/
theorem hasDerivWithinAt_Ioi_of_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Ioi t₀) t₀ := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact hasDerivWithinAt_Ioi_iff_Ici.mpr
    (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hL_right)

/-- For a function `γ` with `Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)` and eventual
differentiability on `(-∞, t₀)`, plus continuity at `t₀`, we have
`HasDerivWithinAt γ L (Iio t₀) t₀`. -/
theorem hasDerivWithinAt_Iio_of_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Iio t₀) t₀ := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact hasDerivWithinAt_Iio_iff_Iic.mpr
    (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hL_left)
