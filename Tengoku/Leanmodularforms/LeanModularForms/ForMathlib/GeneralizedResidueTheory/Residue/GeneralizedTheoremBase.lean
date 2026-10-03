/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV.DominatedConvergence
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

/-!
# Generalized Residue Theorem -- Base Infrastructure

Multi-point PV existence, helper lemmas, and the core generalized residue theorem
for piecewise C1 immersions passing through poles. This file provides the
infrastructure used by both the convex and null-homologous versions.

## Main Results

* `cauchyPrincipalValueOn_singular_sum` -- multi-point PV exists when
  each singular term has PV
* `generalizedResidueTheorem'` -- CPV equals `2 pi i . Sigma winding . residue`
  (convex domain, with explicit PV hypothesis)
* `residueAt` -- residue via contour integral
* `generalizedResidueTheorem_higher_order_tendsto` -- higher-order Tendsto formulation
  (no convexity needed)
* Helper lemmas: `hasSimplePoleAt_sum_div_sub`, `differentiableOn_sum_div_sub`,
  `residueSimplePole_sum_div_sub`, `continuousAt_sum_remainder`

The convex-domain theorems `generalizedResidueTheorem`,
`generalizedResidueTheorem_higher_order`, and
`generalizedResidueTheorem_higher_order_simple` are in `GeneralizedTheorem.lean`,
where they are proved as corollaries of the null-homologous versions.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

private lemma cpv_crossing_null (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) :
    volume {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0 := by
  have h_eq : {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} =
      ⋃ s ∈ (↑S0 : Set ℂ), {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t = s} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨fun ⟨hin, hmem⟩ => ⟨γ.toFun t, hmem, hin, rfl⟩,
      fun ⟨_, hs, hin, heq⟩ => ⟨hin, heq ▸ hs⟩⟩
  rw [h_eq, measure_biUnion_null_iff S0.finite_toSet.countable]
  exact fun s _ => preimage_singleton_measure_zero_of_deriv_ne_zero
    (P := γ.partition) s γ.continuous_toFun γ.smooth_off_partition γ.deriv_ne_zero

private lemma finset_min_sep (S0 : Finset ℂ) (hS0_nonempty : S0.Nonempty) :
    ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖ := by
  by_cases h_card_one : S0.card = 1
  · refine ⟨1, one_pos, fun s hs s' hs' hne => ?_⟩
    obtain ⟨s₀, rfl⟩ := Finset.card_eq_one.mp h_card_one
    simp only [Finset.mem_singleton] at hs hs'
    exact (hne (hs.trans hs'.symm)).elim
  · have h_pos : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → (0 : ℝ) < ‖s' - s‖ :=
      fun _ _ _ _ hne => norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have h_exists_pair : ∃ s ∈ S0, ∃ s' ∈ S0, s ≠ s' := by
      obtain ⟨s, hs⟩ := hS0_nonempty
      by_contra h_all_eq
      push Not at h_all_eq
      have h0 : 0 < S0.card := Finset.card_pos.mpr ⟨s, hs⟩
      have := Finset.card_le_card (fun x hx => Finset.mem_singleton.mpr (h_all_eq x hx s hs))
      simp only [Finset.card_singleton] at this
      omega
    obtain ⟨s₁, hs₁, s₂, hs₂, hne₁₂⟩ := h_exists_pair
    have h_finite : ((S0 ×ˢ S0).filter (fun p => p.1 ≠ p.2) |>.image
        (fun p => ‖p.2 - p.1‖)).Nonempty :=
      ⟨_, Finset.mem_image.mpr ⟨(s₁, s₂), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs₁, hs₂⟩, hne₁₂⟩, rfl⟩⟩
    obtain ⟨δ, hδ_mem, hδ_min⟩ := Finset.exists_min_image _ id h_finite
    simp only [id] at hδ_min
    obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := Finset.mem_image.mp hδ_mem
    simp only [Finset.mem_filter, Finset.mem_product] at hab_mem
    refine ⟨δ, hab_eq ▸ h_pos a hab_mem.1.1 b hab_mem.1.2 hab_mem.2, fun s hs s' hs' hne =>
      hδ_min ‖s' - s‖ (Finset.mem_image.mpr ⟨(s, s'),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, hs'⟩, hne⟩, rfl⟩)⟩

/-- The Cauchy filter argument: if the sum of PV terms converges and the regular part
tends to its integral, then the full CPV filter is Cauchy (hence converges). -/
private lemma cpv_cauchy_of_sum_and_regular (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hS0_nonempty : S0.Nonempty)
    (hPV_each : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s)
    (hg_reg_cont : ContinuousOn
      (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b)) :
    Cauchy (map (fun ε =>
      ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t) (𝓝[>] 0)) := by
  choose L_fn hL_fn using hPV_each
  set M := fun ε => ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t
  set S' := fun ε => ∑ s ∈ S0.attach, ∫ t in γ.a..γ.b,
    if ‖γ.toFun t - s.val‖ > ε then
      (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t
    else 0
  set g_reg := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)
  have h_sum_tendsto : Tendsto S' (𝓝[>] 0) (𝓝 (∑ s ∈ S0.attach, L_fn s.val s.property)) :=
    tendsto_finsetSum _ fun ⟨s, hs⟩ _ => hL_fn s hs
  have h_A_tendsto : Tendsto (fun ε => M ε - S' ε) (𝓝[>] 0)
      (𝓝 (∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t)) :=
    multipointPV_diff_tendsto S0 f γ (cpv_crossing_null S0 γ) g_reg
      (fun _ _ => by simp only [g_reg]; ring) hg_reg_cont (finset_min_sep S0 hS0_nonempty)
  have h_M_tendsto :
      Tendsto M (𝓝[>] 0) (𝓝 ((∑ s ∈ S0.attach, L_fn s.val s.property) +
        ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t)) := by
    have : M = fun ε => S' ε + (M ε - S' ε) := by ext; ring
    rw [this]; exact h_sum_tendsto.add h_A_tendsto
  exact h_M_tendsto.cauchy_map

/-- Multi-point PV exists when each singular term has PV. -/
lemma cauchyPrincipalValueOn_singular_sum (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hPV_each : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s)
    (hg_reg_cont : ContinuousOn
      (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b)) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b := by
  by_cases hS0_empty : S0 = ∅
  · subst hS0_empty
    exact ⟨_, hasCauchyPVOn'_empty f γ.toFun γ.a γ.b⟩
  · exact CompleteSpace.complete (cpv_cauchy_of_sum_and_regular S0 f γ
      (Finset.nonempty_iff_ne_empty.mpr hS0_empty) hPV_each hg_reg_cont)

/-- If PV of f exists, then PV of c * f exists (scaling by constant). -/
lemma CauchyPrincipalValueExists'.const_mul
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} (c : ℂ)
    (h : CauchyPrincipalValueExists' f γ a b z₀) :
    CauchyPrincipalValueExists' (fun z => c * f z) γ a b z₀ :=
  let ⟨_, hL⟩ := h; ⟨_, hL.const_mul c⟩

end
