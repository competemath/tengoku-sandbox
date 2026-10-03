/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistenceMulti

/-!
# Localized exit-time cutoffs for multi-crossing CPV existence (T-BR-Y6c)

This file adapts the exit-time cutoff infrastructure in
`CrossingDataBuilder.lean` from **global** uniqueness on `Icc 0 1` to
**local** uniqueness on a window `Icc (t₀ - r) (t₀ + r)`. This is the
infrastructure required by the multi-crossing CPV discharge programme:
each crossing parameter `t_i ∈ M.crossings` is equipped with its own
local cutoffs `δ_left^i, δ_right^i : ℝ → ℝ`, threshold `θ_i`, and
asymmetric far/near bounds. These per-crossing bundles, when combined,
discharge the `h_multi_cpv` oracle in
`residueTheorem_crossing_asymmetric_multiPole`.

## Setup

Throughout this file we fix a closed piecewise-`C¹` immersion `γ` (with
range avoidance `x : ℂ`), a pole `s : ℂ`, and a crossing parameter
`t₀ : ℝ`. The local window is `Icc (t₀ - r) (t₀ + r)` for some `r > 0`
with `Icc (t₀ - r) (t₀ + r) ⊆ Icc 0 1`. We assume:
* `h_at` — `γ(t₀) = s`;
* `h_off` — `t₀` is off the legacy partition;
* `h_local_unique` — `t₀` is the unique crossing on the window.

These local-uniqueness assumptions come from `multi_pole_local_uniqueness`
in `CPVExistenceMulti.lean` (applied with the common radius `r` from
`multi_pole_common_radius`).

## Main results

* `exists_right_cutoff_local` — right exit-time cutoff `δ_right : ℝ → ℝ`
  with threshold above which `δ_right(ε) < r` and the far-bound holds on
  `(t₀ + δ_right(ε), t₀ + r]`.
* `exists_left_cutoff_local` — symmetric on the left.
* `LocalDerivedCutoffs` — bundle structure containing both cutoffs and
  all asymmetric far/near bounds.
* `localDerivedCutoffs` — noncomputable builder from local geometric data.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

private theorem strict_mono_inverse_exists_local
    (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hf₀ : f 0 = 0)
    (hf_strict : StrictMonoOn f (Set.Icc 0 r))
    (hf_cont : ContinuousOn f (Set.Icc 0 r)) :
    ∀ ε ∈ Set.Ioo (0 : ℝ) (f r),
      ∃! τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) r ∧ f τ = ε := by
  intro ε hε
  have hε_in : ε ∈ Set.Ioo (f 0) (f r) := by rwa [hf₀]
  obtain ⟨τ, hτ_mem, hfτ⟩ := intermediate_value_Ioo hr.le hf_cont hε_in
  refine ⟨τ, ⟨hτ_mem, hfτ⟩, fun τ' ⟨hτ'_mem, hfτ'⟩ =>
    hf_strict.injOn (Set.Ioo_subset_Icc_self hτ'_mem)
      (Set.Ioo_subset_Icc_self hτ_mem) (hfτ'.trans hfτ.symm)⟩

/-- **Abstract exit-time cutoff from a strictly-monotone exit profile.** This is
the directionless core shared by `exists_right_cutoff_local` and
`exists_left_cutoff_local`. Given a profile `f : ℝ → ℝ` (the distance
`‖γ(t₀ ± τ) - s‖` reparametrised by signed offset `τ`) that vanishes at `0`, is
strictly monotone and continuous on `[0, R]`, together with a far-bound `m` on
`(R, r]`, it produces the inverse cutoff `δ` and threshold with the near/far
estimates stated on the profile. The two callers add only the thin
`f τ = ‖γ(t₀ ± τ) - s‖` rewrite. -/
private theorem cutoff_inverse_of_exitProfile
    (f : ℝ → ℝ) {R r m : ℝ} (hR_pos : 0 < R) (hm_pos : 0 < m)
    (hf₀ : f 0 = 0) (hf_strict : StrictMonoOn f (Set.Icc 0 R))
    (hf_cont : ContinuousOn f (Set.Icc 0 R))
    (h_far : ∀ τ, R < τ → τ ≤ r → m ≤ f τ) :
    ∃ (δ : ℝ → ℝ) (threshold : ℝ), 0 < threshold ∧ threshold ≤ m ∧
      (∀ ε, 0 < ε → ε < threshold → δ ε ∈ Set.Ioo (0 : ℝ) R ∧ f (δ ε) = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ τ, δ ε < τ → τ ≤ r → ε < f τ) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ τ, 0 ≤ τ → τ ≤ δ ε → f τ ≤ ε) := by
  classical
  have hf_r_pos : 0 < f R := by
    rw [show (0 : ℝ) = f 0 from hf₀.symm]
    exact hf_strict (Set.left_mem_Icc.mpr hR_pos.le)
      (Set.right_mem_Icc.mpr hR_pos.le) hR_pos
  set threshold : ℝ := min (f R) m with hthr_def
  refine ⟨fun ε =>
    if h : ε ∈ Set.Ioo (0 : ℝ) (f R) then
      (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε h).choose
    else R / 2, threshold, lt_min hf_r_pos hm_pos, min_le_right _ _, ?_, ?_, ?_⟩
  · intro ε hε_pos hε_lt
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f R) := ⟨hε_pos, hε_lt.trans_le (min_le_left _ _)⟩
    simp only [dite_eq_left hε_in]
    exact (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
  · intro ε hε_pos hε_lt τ hτ_gt hτ_le
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f R) := ⟨hε_pos, hε_lt.trans_le (min_le_left _ _)⟩
    obtain ⟨hδ_in, hfδ⟩ :=
      (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
    simp only [dite_eq_left hε_in] at hτ_gt ⊢
    by_cases hτ_R : τ ≤ R
    · have := hf_strict ⟨hδ_in.1.le, hδ_in.2.le⟩ ⟨hδ_in.1.le.trans hτ_gt.le, hτ_R⟩ hτ_gt
      rwa [hfδ] at this
    · linarith [h_far τ (lt_of_not_ge hτ_R) hτ_le, hε_lt.trans_le (min_le_right _ _)]
  · intro ε hε_pos hε_lt τ hτ_ge hτ_le
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f R) := ⟨hε_pos, hε_lt.trans_le (min_le_left _ _)⟩
    obtain ⟨hδ_in, hfδ⟩ :=
      (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
    simp only [dite_eq_left hε_in] at hτ_le ⊢
    have := hf_strict.monotoneOn ⟨hτ_ge, hτ_le.trans hδ_in.2.le⟩ ⟨hδ_in.1.le, hδ_in.2.le⟩ hτ_le
    rwa [hfδ] at this

/-- **Localized right cutoff existence (corner-friendly).** Given a closed
pw-`C¹` immersion `γ` crossing `s` at an **interior** parameter `t₀`
(smooth OR corner — no off-partition assumption), with local uniqueness on
the window `[t₀ - r, t₀ + r] ⊆ [0, 1]`, produce a right cutoff
`δ_right : ℝ → ℝ` and threshold satisfying the asymmetric far/near bounds. -/
private theorem exists_right_cutoff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_right : ℝ → ℝ) (threshold : ℝ),
      0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_right ε < r) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_right ε) - s‖ = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ + δ_right ε < t → t ≤ t₀ + r →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ ≤ t → t - t₀ ≤ δ_right ε →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have h_t₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [(h_window_Icc ⟨le_rfl, by linarith⟩ :
        (t₀ - r) ∈ Set.Icc (0 : ℝ) 1).1],
     by linarith [(h_window_Icc ⟨by linarith, le_rfl⟩ :
        (t₀ + r) ∈ Set.Icc (0 : ℝ) 1).2]⟩
  obtain ⟨L, hL_ne, hL_right⟩ := exists_right_deriv_limit γ h_t₀_Ioo
  have hγ_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  obtain ⟨r₀, hr₀_pos, hmono⟩ :=
    norm_sub_strictMonoOn_right h_at hL_ne hL_right hγ_cont_all.continuousAt
      (eventually_differentiable_right γ h_t₀_Ioo)
  set r_eff_mono : ℝ := min r₀ (r / 2)
  have hr_eff_pos : 0 < r_eff_mono := lt_min hr₀_pos (by linarith)
  have hr_eff_lt_r : r_eff_mono < r := (min_le_right _ _).trans_lt (by linarith)
  have hmono_r : StrictMonoOn (fun t => ‖γf t - s‖) (Set.Icc t₀ (t₀ + r_eff_mono)) :=
    hmono.mono (Set.Icc_subset_Icc le_rfl (by linarith [min_le_left r₀ (r/2)]))
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ + τ) - s‖ with hf_def
  have hf₀ : f 0 = 0 := by
    show ‖γf (t₀ + 0) - s‖ = 0
    rw [add_zero, show γf t₀ = s from h_at, sub_self, norm_zero]
  have hf_cont : ContinuousOn f (Set.Icc 0 r_eff_mono) :=
    (((hγ_cont_all.comp (continuous_const.add continuous_id)).sub
      continuous_const).norm).continuousOn
  have hf_strict : StrictMonoOn f (Set.Icc 0 r_eff_mono) := fun a ha b hb hab =>
    hmono_r ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
  obtain ⟨m, hm_pos, _h_far_left, h_far_right⟩ :=
    multi_pole_local_far_bound γ h_window_pos h_local_unique hr_eff_pos
      hr_eff_lt_r.le
  obtain ⟨δ_right, threshold, hthresh_pos, _, hδ_spec, h_far, h_near⟩ :=
    cutoff_inverse_of_exitProfile (r := r) f hr_eff_pos hm_pos hf₀ hf_strict hf_cont
      (fun τ hτ_gt hτ_le => by
        rw [hf_def]; exact h_far_right (t₀ + τ) ⟨by linarith, by linarith⟩)
  have h_eq_t : ∀ t, f (t - t₀) = ‖γf t - s‖ := fun t => by
    show ‖γf (t₀ + (t - t₀)) - s‖ = ‖γf t - s‖
    rw [show t₀ + (t - t₀) = t by ring]
  refine ⟨δ_right, threshold, hthresh_pos, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.1
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.2.trans hr_eff_lt_r
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).2
  · intro ε hε_pos hε_lt t ht_gt ht_le
    have := h_far ε hε_pos hε_lt (t - t₀) (by linarith) (by linarith)
    rwa [h_eq_t] at this
  · intro ε hε_pos hε_lt t ht_ge hgap
    have := h_near ε hε_pos hε_lt (t - t₀) (by linarith) (by linarith)
    rwa [h_eq_t] at this

/-- **Localized left cutoff existence (corner-friendly).** Symmetric
counterpart of `exists_right_cutoff_local`. -/
private theorem exists_left_cutoff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_left : ℝ → ℝ) (threshold : ℝ),
      0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_left ε < r) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_left ε) - s‖ = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ - r ≤ t → t < t₀ - δ_left ε →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ - δ_left ε ≤ t → t ≤ t₀ →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have h_t₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [(h_window_Icc ⟨le_rfl, by linarith⟩ :
        (t₀ - r) ∈ Set.Icc (0 : ℝ) 1).1],
     by linarith [(h_window_Icc ⟨by linarith, le_rfl⟩ :
        (t₀ + r) ∈ Set.Icc (0 : ℝ) 1).2]⟩
  obtain ⟨L, hL_ne, hL_left⟩ := exists_left_deriv_limit γ h_t₀_Ioo
  have hγ_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  obtain ⟨r₀, hr₀_pos, hanti⟩ :=
    norm_sub_strictAntiOn_left h_at hL_ne hL_left hγ_cont_all.continuousAt
      (eventually_differentiable_left γ h_t₀_Ioo)
  set r_eff_mono : ℝ := min r₀ (r / 2)
  have hr_eff_pos : 0 < r_eff_mono := lt_min hr₀_pos (by linarith)
  have hr_eff_lt_r : r_eff_mono < r := (min_le_right _ _).trans_lt (by linarith)
  have hanti_r : StrictAntiOn (fun t => ‖γf t - s‖) (Set.Icc (t₀ - r_eff_mono) t₀) :=
    hanti.mono (Set.Icc_subset_Icc (by linarith [min_le_left r₀ (r/2)]) le_rfl)
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ - τ) - s‖ with hf_def
  have hf₀ : f 0 = 0 := by
    show ‖γf (t₀ - 0) - s‖ = 0
    rw [sub_zero, show γf t₀ = s from h_at, sub_self, norm_zero]
  have hf_cont : ContinuousOn f (Set.Icc 0 r_eff_mono) :=
    (((hγ_cont_all.comp (continuous_const.sub continuous_id)).sub
      continuous_const).norm).continuousOn
  have hf_strict : StrictMonoOn f (Set.Icc 0 r_eff_mono) := fun a ha b hb hab =>
    hanti_r ⟨by linarith [hb.2], by linarith [hb.1]⟩
      ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
  obtain ⟨m, hm_pos, h_far_left, _h_far_right⟩ :=
    multi_pole_local_far_bound γ h_window_pos h_local_unique hr_eff_pos
      hr_eff_lt_r.le
  obtain ⟨δ_left, threshold, hthresh_pos, _, hδ_spec, h_far, h_near⟩ :=
    cutoff_inverse_of_exitProfile (r := r) f hr_eff_pos hm_pos hf₀ hf_strict hf_cont
      (fun τ hτ_gt hτ_le => by
        rw [hf_def]; exact h_far_left (t₀ - τ) ⟨by linarith, by linarith⟩)
  have h_eq_t : ∀ t, f (t₀ - t) = ‖γf t - s‖ := fun t => by
    show ‖γf (t₀ - (t₀ - t)) - s‖ = ‖γf t - s‖
    rw [show t₀ - (t₀ - t) = t by ring]
  refine ⟨δ_left, threshold, hthresh_pos, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.1
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.2.trans hr_eff_lt_r
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).2
  · intro ε hε_pos hε_lt t ht_ge ht_lt
    have := h_far ε hε_pos hε_lt (t₀ - t) (by linarith) (by linarith)
    rwa [h_eq_t] at this
  · intro ε hε_pos hε_lt t ht_ge ht_le
    have := h_near ε hε_pos hε_lt (t₀ - t) (by linarith) (by linarith)
    rwa [h_eq_t] at this

/-- **Per-crossing local cutoffs** for a multi-crossing scenario. Each
crossing parameter `t₀` is equipped with its own asymmetric cutoffs
`δ_left, δ_right : ℝ → ℝ`, threshold, and far/near bounds on the local
window `[t₀ - r, t₀ + r]`. -/
structure LocalDerivedCutoffs (γ : ClosedPwC1Immersion x) (s : ℂ) (t₀ r : ℝ) where
  /-- Left cutoff function. -/
  δ_left : ℝ → ℝ
  /-- Right cutoff function. -/
  δ_right : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  hδ_left_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε
  hδ_right_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε
  hδ_left_lt : ∀ ε, 0 < ε → ε < threshold → δ_left ε < r
  hδ_right_lt : ∀ ε, 0 < ε → ε < threshold → δ_right ε < r
  h_exit_left : ∀ ε, 0 < ε → ε < threshold →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_left ε) - s‖ = ε
  h_exit_right : ∀ ε, 0 < ε → ε < threshold →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_right ε) - s‖ = ε
  h_far_left : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ - r ≤ t → t < t₀ - δ_left ε →
    ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_far_right : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ + δ_right ε < t → t ≤ t₀ + r →
    ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_near_left : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ - δ_left ε ≤ t → t ≤ t₀ →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
  h_near_right : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ ≤ t → t - t₀ ≤ δ_right ε →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε

/-- **Builder for `LocalDerivedCutoffs`** from a single-crossing local
geometric data: window radius `r > 0`, window-in-unit-interval, off-partition,
local uniqueness on the window. The far-bound information is derived
internally from `multi_pole_local_far_bound`.

(The `h_flat` hypothesis is recorded but not used in the proof body: the
flatness is implicit in the strict-monotonicity result, which uses only
the nonzero one-sided derivative limits provided by the immersion.) -/
noncomputable def localDerivedCutoffs
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    LocalDerivedCutoffs γ s t₀ r :=
  let dR := exists_right_cutoff_local γ h_window_pos h_window_Icc h_at
    h_local_unique
  let dL := exists_left_cutoff_local γ h_window_pos h_window_Icc h_at
    h_local_unique
  let dR_props := dR.choose_spec.choose_spec
  let dL_props := dL.choose_spec.choose_spec
  { δ_left := dL.choose
    δ_right := dR.choose
    threshold := min dR.choose_spec.choose dL.choose_spec.choose
    hthresh := lt_min dR_props.1 dL_props.1
    hδ_left_pos := fun ε hε hεt =>
      dL_props.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    hδ_right_pos := fun ε hε hεt =>
      dR_props.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    hδ_left_lt := fun ε hε hεt =>
      dL_props.2.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    hδ_right_lt := fun ε hε hεt =>
      dR_props.2.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    h_exit_left := fun ε hε hεt =>
      dL_props.2.2.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    h_exit_right := fun ε hε hεt =>
      dR_props.2.2.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    h_far_left := fun ε hε hεt =>
      dL_props.2.2.2.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    h_far_right := fun ε hε hεt =>
      dR_props.2.2.2.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    h_near_left := fun ε hε hεt =>
      dL_props.2.2.2.2.2 ε hε (hεt.trans_le (min_le_right _ _))
    h_near_right := fun ε hε hεt =>
      dR_props.2.2.2.2.2 ε hε (hεt.trans_le (min_le_left _ _)) }

/-- **Right-side chord-quotient radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane` for all `t₀ < a ≤ b ≤ t₀ + r`.

Pure repackaging of `exists_slitPlane_chord_quotient_right`. Provided as a
companion to the exact-radius API so that callers can derive their per-crossing
threshold radius before invoking `cpvFullSetup_local_exact`. -/
theorem exists_chord_slitPlane_radius_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane :=
  exists_slitPlane_chord_quotient_right h_deriv h_at hL

/-- **Left-side chord-quotient radius existence (forward direction)**: given a
left one-sided derivative limit `L ≠ 0`, there exists `r > 0` such that the
chord quotient `(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane` for all
`t₀ - r ≤ a ≤ b < t₀`.

Pure repackaging of `exists_slitPlane_chord_quotient_left_forward`. -/
theorem exists_chord_slitPlane_radius_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane :=
  exists_slitPlane_chord_quotient_left_forward h_deriv h_at hL

/-- **Right boundary slit-plane radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r`, the boundary chord-to-tangent quotient
`(γ(t₀ + r') - s) / L ∈ Complex.slitPlane`.

The proof uses the normalized chord bound
`‖(γ(t₀ + r') - s) / (L · r') - 1‖ ≤ 1/4`, which yields
`Re((γ(t₀ + r') - s) / (L · r')) ≥ 3/4`. Multiplying by the positive real
`r'` (which preserves slit-plane membership) gives the desired result. -/
theorem exists_chord_div_endpoint_slitPlane_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (γ (t₀ + r') - s) / L ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le => ?_⟩
  have h_in : (t₀ + r') ∈ Set.Ioc t₀ (t₀ + r) := ⟨by linarith, by linarith⟩
  have h_simp : (((t₀ + r') - t₀ : ℝ) : ℂ) = ((r' : ℝ) : ℂ) := by push_cast; ring
  have h_close : ‖(γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp]; exact hr_close (t₀ + r') h_in
  have h_re_close : (3 / 4 : ℝ) ≤
      ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    have h_abs_le :
        |((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re| ≤ 1 / 4 :=
      (Complex.abs_re_le_norm _).trans h_close
    have h_re_eq : ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re =
        ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re - 1 := by simp
    rw [h_re_eq] at h_abs_le
    linarith [(abs_le.mp h_abs_le).1]
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_div_eq : (γ (t₀ + r') - s) / L =
      ((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))) := by
    field_simp
  rw [h_div_eq, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      (((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)))).re =
        r' * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < r' * (3 / 4))
    (mul_le_mul_of_nonneg_left h_re_close hr'_pos.le)

/-- **Left boundary slit-plane radius existence**: given a left one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r` with `γ(t₀ - r') ≠ s`, the negated boundary quotient
`-L / (γ(t₀ - r') - s) ∈ Complex.slitPlane`.

The `γ(t₀ - r') ≠ s` hypothesis is supplied by the caller (typically via
local uniqueness on the window). The proof uses `‖−q − 1‖ ≤ 1/4` where
`q = (γ(t₀ - r') - s) / (L · r')`, then deduces `‖q‖ ≥ 3/4`, then
`‖−1/q − 1‖ ≤ 1/3`, then `Re(−1/q) ≥ 2/3`, and finally multiplies by `1/r' > 0`. -/
theorem exists_chord_div_endpoint_slitPlane_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → γ (t₀ - r') ≠ s →
      (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le h_γ_ne => ?_⟩
  have h_in : (t₀ - r') ∈ Set.Ico (t₀ - r) t₀ :=
    ⟨by linarith, by linarith⟩
  have h_simp_in : (((t₀ - r') - t₀ : ℝ) : ℂ) = -((r' : ℝ) : ℂ) := by
    push_cast; ring
  have h_close : ‖(γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp_in]; exact hr_close (t₀ - r') h_in
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_γMinus_ne : γ (t₀ - r') - s ≠ 0 := sub_ne_zero.mpr h_γ_ne
  set q : ℂ := (γ (t₀ - r') - s) / (L * ((r' : ℝ) : ℂ)) with hq_def
  have hq_close : ‖-q - 1‖ ≤ 1 / 4 := by
    have h_eq : (γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) = -q := by
      rw [hq_def, mul_neg, div_neg]
    rwa [h_eq] at h_close
  have hq_norm : 3 / 4 ≤ ‖q‖ := by
    have h_rev : ‖(-1 : ℂ)‖ - ‖q‖ ≤ ‖-1 - q‖ := norm_sub_norm_le _ _
    rw [norm_neg, norm_one, show (-1 : ℂ) - q = -(q + 1) from by ring,
      norm_neg, show q + 1 = -(-q - 1) from by ring, norm_neg] at h_rev
    linarith
  have hq_ne : q ≠ 0 := fun h_eq => by
    rw [h_eq, norm_zero] at hq_norm; linarith
  have h_neg_inv_q_close : ‖(-1 / q) - 1‖ ≤ 1 / 3 := by
    have h_eq : ((-1 : ℂ) / q) - 1 = -((1 + q) / q) := by field_simp; ring
    rw [h_eq, norm_neg, norm_div,
      show ‖(1 : ℂ) + q‖ = ‖-q - 1‖ from by
        rw [show (1 : ℂ) + q = -(-q - 1) from by ring, norm_neg],
      div_le_iff₀ (norm_pos_iff.mpr hq_ne)]
    calc ‖-q - 1‖ ≤ 1 / 4 := hq_close
      _ ≤ (1 / 3) * (3 / 4) := by norm_num
      _ ≤ (1 / 3) * ‖q‖ := mul_le_mul_of_nonneg_left hq_norm (by norm_num)
  have h_eq_target : (-L) / (γ (t₀ - r') - s) =
      (((1 / r' : ℝ)) : ℂ) * (-1 / q) := by
    rw [hq_def]; push_cast; field_simp
  rw [h_eq_target, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      ((((1 / r' : ℝ)) : ℂ) * (-1 / q)).re = (1 / r') * (-1 / q).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  have h_abs_re_le : |(-1 / q - 1).re| ≤ 1 / 3 :=
    (Complex.abs_re_le_norm _).trans h_neg_inv_q_close
  have h_re_eq : (-1 / q - 1).re = (-1 / q).re - 1 := by simp
  rw [h_re_eq] at h_abs_re_le
  have h_inv_r_pos : 0 < 1 / r' := by positivity
  linarith [mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ (-1 / q).re by linarith [(abs_le.mp h_abs_re_le).1])
    h_inv_r_pos.le,
    show 0 < (1 / r') * (2 / 3 : ℝ) by positivity]

/-- **One-sided derivative limit setup at an interior crossing.** Extracts the
nonzero one-sided derivatives `L_R, L_L` and the corresponding
`HasDerivWithinAt` witnesses on `Ioi t₀, Iio t₀` from the immersion
infrastructure. This is the radius-independent substrate of
`cpvFullSetup_local`. -/
theorem oneSided_deriv_setup
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (L_R L_L : ℂ),
      L_R ≠ 0 ∧ L_L ≠ 0 ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  obtain ⟨L_R, hL_R_ne, hL_R_tendsto⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_L_tendsto⟩ := exists_left_deriv_limit γ ht₀
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  obtain ⟨S_R, hS_R_mem, hS_R_diff⟩ :=
    (eventually_differentiable_right γ ht₀).exists_mem
  obtain ⟨S_L, hS_L_mem, hS_L_diff⟩ :=
    (eventually_differentiable_left γ ht₀).exists_mem
  refine ⟨L_R, L_L, hL_R_ne, hL_L_ne,
    hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hS_R_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_R_mem hL_R_tendsto),
    hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hS_L_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_L_mem hL_L_tendsto)⟩

/-- **Smooth complement positive bound** for a multi-crossing setup.

Given a finite set of crossings `crossings : Finset ℝ` (each in `Icc 0 1`,
with `γ(t) = s` only when `t ∈ crossings`), and a common radius function
`r_at : crossings → ℝ` with each `r_at t_i > 0`, the function `t ↦ ‖γ(t) - s‖`
has a positive minimum on the **closed complement** `[0, 1] \ ⋃_i (t_i - r_at t_i,
t_i + r_at t_i)`. -/
theorem multi_pole_smooth_complement_far_bound
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {crossings : Finset ℝ}
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    (r_at : ℝ → ℝ) (hr_at_pos : ∀ t ∈ crossings, 0 < r_at t) :
    ∃ m : ℝ, 0 < m ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)) →
        m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  set C : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 |
    ∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} with hC_def
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ht.1
  have hC_closed : IsClosed C := by
    have h2 : IsClosed ({t : ℝ | ∀ t_i ∈ crossings,
        t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)}) := by
      have h_eq : {t : ℝ | ∀ t_i ∈ crossings,
            t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} =
          ⋂ t_i ∈ crossings, (Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i))ᶜ := by
        ext t; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
      rw [h_eq]
      exact isClosed_biInter fun _ _ => isOpen_Ioo.isClosed_compl
    have hC_eq : C = Set.Icc (0 : ℝ) 1 ∩
        {t : ℝ | ∀ t_i ∈ crossings,
          t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} := by
      ext t; simp only [hC_def, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [hC_eq]
    exact isClosed_Icc.inter h2
  have hC_compact : IsCompact C :=
    isCompact_Icc.of_isClosed_subset hC_closed hC_subset
  by_cases hC_empty : C = ∅
  · exact ⟨1, one_pos, fun t ht h_avoid => by
      have : t ∈ C := ⟨ht, h_avoid⟩
      rw [hC_empty] at this; exact absurd this (Set.notMem_empty t)⟩
  · have h_norm_cont : ContinuousOn (fun t => ‖γf t - s‖) C :=
      (hγ_cont.continuousOn.sub continuousOn_const).norm
    obtain ⟨t_min, ht_min_mem, ht_min⟩ := hC_compact.exists_isMinOn
      (Set.nonempty_iff_ne_empty.mpr hC_empty) h_norm_cont
    refine ⟨‖γf t_min - s‖, ?_, fun t ht h_avoid => ht_min ⟨ht, h_avoid⟩⟩
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_t_min_in_crossings : t_min ∈ crossings :=
      h_complete t_min (hC_subset ht_min_mem) h_eq
    exact ht_min_mem.2 t_min h_t_min_in_crossings
      ⟨by linarith [hr_at_pos t_min h_t_min_in_crossings],
       by linarith [hr_at_pos t_min h_t_min_in_crossings]⟩

end HungerbuhlerWasem

end
