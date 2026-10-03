/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.FlatChordBound
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.FlatnessConditions

/-!
# F-diff asymptotic chain (T-SC-00a)

For a curve `γ` flat of order `n` at `t₀` with `γ(t₀) = s`, the antiderivative
`F(z) = -1/[(k-1)(z-s)^{k-1}]` of the higher-order pole integrand satisfies
`F(γ(t)) - F(tangent target) → 0` as `t → t₀` from either side, provided
`n ≥ k ≥ 2`. Combined with FTC on each smooth piece, this gives the
parameter-excised CPV `→ 0` result needed by the sector cancellation argument
of T-SC-01.

This file restores the F-diff asymptotic subset of the deleted
`HigherOrderCancel.lean` (git ref `79bcaa5^`, lines 477-1300+) into
`namespace HungerbuhlerWasem`. Only the asymptotic / FTC chain leading to the
five headline theorems is restored; the upstream `HasCauchyPVOn`-based
cancellation API (which depended on the also-deleted `HigherOrderAssembly.lean`)
is intentionally omitted as it isn't needed for T-SC-01.

## Headline theorems

* `integral_pow_inv_eq_FTC` — FTC for `γ'/(γ-s)^k` on a smooth piece.
* `closed_excised_integral_eq_antideriv_diff` — closed-form excised integral
  via antiderivative differences.
* `F_diff_at_tangent_target_tendsto_zero_right` — F-diff vs tangent target → 0
  from the right, under flatness and `n ≥ k`.
* `F_diff_at_tangent_target_tendsto_zero_left` — mirror form on the left.
* `cpv_excised_tendsto_zero_of_F_diff_zero` — combined excised-integral form
  of the F-diff Tendsto hypothesis.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

namespace HungerbuhlerWasem

/-- When `γ` has right-derivative `L ≠ 0` at `t₀` and `γ(t₀) = s`, for `t` close to
`t₀` from the right, `γ(t) − s` lies in the `+L` hemisphere
(`Re((γ(t) − s) · conj L) ≥ 0`). -/
theorem eventually_re_pos_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[>] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ L).re := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hLsq_pos : 0 < ‖L‖ ^ 2 := by positivity
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_pos : 0 < t - t₀ := sub_pos.mpr ht
  rw [Real.norm_eq_abs, abs_of_pos h_pos] at h_b
  rw [show (γ t - s) = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) by rw [h_s]; ring,
    add_mul, Complex.add_re]
  have h1 : ((((t - t₀) : ℝ) • L) * starRingEnd ℂ L).re = (t - t₀) * ‖L‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  have h2 : -(‖L‖ / 2 * (t - t₀)) * ‖L‖ ≤
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L).re := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L)
    rw [norm_mul, Complex.norm_conj] at habs
    nlinarith [abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right h_b (norm_nonneg L)))]
  nlinarith [hLsq_pos]

/-- Symmetric counterpart of `eventually_re_pos_right`: `Re((γ(t) − s) · conj L) ≤ 0`
for `t` close to `t₀` from the left. -/
theorem eventually_re_neg_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[<] t₀, ((γ t - s) * starRingEnd ℂ L).re ≤ 0 := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hLsq_pos : 0 < ‖L‖ ^ 2 := by positivity
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_neg : t - t₀ < 0 := sub_neg.mpr ht
  rw [Real.norm_eq_abs, abs_of_neg h_neg] at h_b
  rw [show (γ t - s) = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) by rw [h_s]; ring,
    add_mul, Complex.add_re]
  have h1 : ((((t - t₀) : ℝ) • L) * starRingEnd ℂ L).re = (t - t₀) * ‖L‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  have h2 : ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L).re ≤
      ‖L‖ / 2 * -(t - t₀) * ‖L‖ := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L)
    rw [norm_mul, Complex.norm_conj] at habs
    nlinarith [abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right h_b (norm_nonneg L)))]
  nlinarith [hLsq_pos]

/-- With right-derivative `L ≠ 0`, the curve cannot stay at `s` past `t₀`. -/
theorem eventually_ne_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[>] t₀, γ t ≠ s := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_pos : 0 < t - t₀ := sub_pos.mpr ht
  intro h_eq
  have h_diff_zero : γ t - γ t₀ = 0 := h_s ▸ sub_eq_zero.mpr h_eq
  simp only [h_diff_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos h_pos] at h_b
  nlinarith

/-- Left-side counterpart of `eventually_ne_right`. -/
theorem eventually_ne_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[<] t₀, γ t ≠ s := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_neg : t - t₀ < 0 := sub_neg.mpr ht
  intro h_eq
  have h_diff_zero : γ t - γ t₀ = 0 := h_s ▸ sub_eq_zero.mpr h_eq
  simp only [h_diff_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_neg h_neg] at h_b
  nlinarith

/-- If `z₁, z₂` are equidistant from `s` (distance `d`), then any point `z` on the
segment from `z₁` to `z₂` satisfies `‖z − s‖² ≥ d² − ‖z₁ − z₂‖²/4`. -/
theorem norm_sq_segment_to_pole_lower_bound
    {z₁ z₂ s : ℂ} {d : ℝ}
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d ^ 2 - ‖z₁ - z₂‖ ^ 2 / 4 ≤ ‖z - s‖ ^ 2 := by
  obtain ⟨α, β, hα, hβ, h_sum, rfl⟩ := hz
  rw [show α • z₁ + β • z₂ - s = α • (z₁ - s) + β • (z₂ - s) by
    rw [show β = 1 - α by linarith]; module]
  have h_expand : ‖α • (z₁ - s) + β • (z₂ - s)‖ ^ 2 =
      α ^ 2 * ‖z₁ - s‖ ^ 2 +
        2 * α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re +
        β ^ 2 * ‖z₂ - s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.real_smul]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal,
      show (((α : ℂ) * (z₁ - s)) * starRingEnd ℂ ((β : ℂ) * (z₂ - s))) =
          ((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s)) by
        rw [map_mul, Complex.conj_ofReal]; push_cast; ring,
      show (((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s))).re =
          α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re by
        rw [Complex.mul_re]; simp]
    ring
  have h_cross : ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re =
      (‖z₁ - s‖ ^ 2 + ‖z₂ - s‖ ^ 2 - ‖z₁ - z₂‖ ^ 2) / 2 := by
    have h_ns := Complex.normSq_sub (z₁ - s) (z₂ - s)
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm,
      show (z₁ - s) - (z₂ - s) = z₁ - z₂ by ring] at h_ns
    linarith
  rw [h_expand, h_cross, h₁, h₂]
  have h_ab_le : α * β ≤ 1 / 4 := by nlinarith [sq_nonneg (α - β)]
  have h_quad : α ^ 2 + 2 * α * β + β ^ 2 = 1 := by nlinarith [h_sum]
  nlinarith [h_quad, h_ab_le, sq_nonneg (‖z₁ - z₂‖)]

/-- When the chord between two equidistant points is at most `d`, the segment from
`z₁` to `z₂` stays at distance `≥ d/2` from `s`. -/
theorem norm_segment_to_pole_lower_bound_half
    {z₁ z₂ s : ℂ} {d : ℝ} (_hd_pos : 0 < d)
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) (h_chord : ‖z₁ - z₂‖ ≤ d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d / 2 ≤ ‖z - s‖ := by
  have h_le_sq : (d / 2) ^ 2 ≤ ‖z - s‖ ^ 2 := by
    nlinarith [norm_sq_segment_to_pole_lower_bound h₁ h₂ hz,
      mul_self_le_mul_self (norm_nonneg _) h_chord]
  have := abs_le_of_sq_le_sq' h_le_sq (norm_nonneg _)
  linarith [this.2, abs_of_pos (by linarith : 0 < d / 2)]

end HungerbuhlerWasem

end
