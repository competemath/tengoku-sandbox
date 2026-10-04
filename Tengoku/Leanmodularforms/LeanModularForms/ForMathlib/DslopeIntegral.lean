/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku

/-!
# `dslope` as a parameter integral

For `f : ℂ → ℂ` differentiable on an open convex set `U` and `c, w ∈ U`, we have
the integral representation:

  `dslope f c w = ∫₀¹ deriv f (c + t • (w - c)) ∂t`

This is the fundamental theorem of calculus applied to `f` on the segment `[c, w] ⊆ U`.
The representation unifies the two cases in `dslope` (`c = w` giving `deriv f c`, and
`c ≠ w` giving the usual slope formula).

From this integral representation we deduce:

* Joint continuity of `(c, w) ↦ dslope f c w` on convex open sets

## Main results

* `dslope_eq_integral_deriv` — `dslope f c w = ∫₀¹ deriv f (c + t•(w-c))` on convex `U`
-/

open Set MeasureTheory Filter Topology intervalIntegral

noncomputable section

namespace Complex

variable {f : ℂ → ℂ}

set_option backward.isDefEq.respectTransparency false in
/-- The `dslope` integral representation on a convex open set: when `f` is
differentiable on `U` and both `c, w ∈ U` (so the segment `[c, w] ⊆ U`), then
`dslope f c w` equals the integral of the derivative of `f` along the segment. -/
theorem dslope_eq_integral_deriv {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c w : ℂ} (hc : c ∈ U) (hw : w ∈ U) :
    dslope f c w = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) := by
  have h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ U := fun t ht => by
    rw [show c + t • (w - c) = (1 - t) • c + t • w from by module]
    exact hU hc hw (by linarith [ht.2]) ht.1 (by linarith)
  have h_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (deriv f (c + t • (w - c))) (c + t • (w - c)) := fun t ht =>
    ((hf (c + t • (w - c)) (h_seg t ht)).differentiableAt
      (hU_open.mem_nhds (h_seg t ht))).hasDerivAt
  have h_deriv_contU : ContinuousOn (deriv f) U :=
    (hf.analyticOnNhd hU_open).deriv.continuousOn
  have h_cont : ContinuousOn (fun t : ℝ => deriv f (c + t • (w - c))) (Icc (0 : ℝ) 1) :=
    h_deriv_contU.comp (by continuity : Continuous _).continuousOn h_seg
  have h_int := integral_unitInterval_deriv_eq_sub h_cont h_deriv
  rw [show c + (w - c) = w from by ring] at h_int
  by_cases hwc : w = c
  · subst hwc; simp
  · have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
    have h_mul : (w - c) * ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) = f w - f c := by
      rwa [← smul_eq_mul]
    rw [dslope_of_ne f hwc, slope_def_module, smul_eq_mul]
    rw [show (w - c)⁻¹ * (f w - f c) = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) from ?_]
    rw [← h_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

set_option backward.isDefEq.respectTransparency false in
private lemma exists_compact_tube_prod {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) :
    ∃ ε > 0, ∃ K ⊆ U, IsCompact K ∧
      ∀ c ∈ Metric.ball c₀ ε, ∀ w ∈ Metric.ball w₀ ε,
        ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ K := by
  obtain ⟨ρ_c, hρ_c_pos, hρ_c_sub⟩ := Metric.isOpen_iff.mp hU_open c₀ hc₀
  obtain ⟨ρ_w, hρ_w_pos, hρ_w_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  set ρ := min ρ_c ρ_w / 2
  have hρ_pos : 0 < ρ := by positivity
  refine ⟨ρ, hρ_pos,
    (fun p : ℂ × ℂ × ℝ => (1 - p.2.2) • p.1 + p.2.2 • p.2.1) ''
      (Metric.closedBall c₀ ρ ×ˢ Metric.closedBall w₀ ρ ×ˢ Icc (0 : ℝ) 1),
    ?_, ?_, ?_⟩
  · rintro z ⟨⟨c, w, t⟩, ⟨hc, hw, ht⟩, rfl⟩
    rw [Metric.mem_closedBall] at hc hw
    simp only [ρ] at hc hw
    exact hU
      (hρ_c_sub (Metric.mem_ball.mpr (by linarith [min_le_left ρ_c ρ_w])))
      (hρ_w_sub (Metric.mem_ball.mpr (by linarith [min_le_right ρ_c ρ_w])))
      (by linarith [ht.2]) ht.1 (by linarith)
  · exact IsCompact.image_of_continuousOn ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod isCompact_Icc))
      (((continuous_const.sub continuous_snd.snd).smul continuous_fst).add
        (continuous_snd.snd.smul continuous_snd.fst)).continuousOn
  · intro c hc w hw t ht
    rw [Metric.mem_ball] at hc hw
    refine ⟨(c, w, t), ⟨?_, ?_, ht⟩, ?_⟩
    · rw [Metric.mem_closedBall]; linarith
    · rw [Metric.mem_closedBall]; linarith
    · change (1 - t) • c + t • w = c + t • (w - c)
      module

end Complex

end
