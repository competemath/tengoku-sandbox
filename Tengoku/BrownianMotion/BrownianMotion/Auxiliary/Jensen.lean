/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.Analysis
public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.ENNReal
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Jensen's inequality for conditional expectations
-/

@[expose] public section

open MeasureTheory Filter ENNReal
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {s : Set E} {f : Ω → E} {φ : E → ℝ}

variable [IsFiniteMeasure μ]

lemma norm_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ μ[fun ω ↦ ‖f ω‖|m] ω := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm]
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  by_cases hf : Integrable f μ
  swap; · filter_upwards [this]; simp [condExp_of_not_integrable, hf]
  exact convexOn_univ_norm.map_condExp_le_univ hm continuous_norm.lowerSemicontinuous hf hf.norm

lemma enorm_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ≤ .ofReal (μ[fun ω ↦ ‖f ω‖|m] ω) := by
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  filter_upwards [norm_condExp_le f, this] with ω hω1 hω2
  rwa [le_ofReal_iff_toReal_le (by simp) hω2, toReal_enorm]

lemma norm_rpow_condExp_le {p : ℝ≥0∞} (one_le_p : 1 ≤ p) (p_ne_top : p ≠ ∞) (hf : MemLp f p μ) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ^ p.toReal ≤ μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm, (toReal_pos_of_one_le one_le_p p_ne_top).ne']
  have hf' : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := by
    rwa [integrable_norm_rpow_iff hf.aestronglyMeasurable (by positivity) p_ne_top]
  have hc : Continuous (fun x : E ↦ ‖x‖ ^ p.toReal) := by fun_prop (disch := positivity)
  filter_upwards [ConvexOn.map_condExp_le_univ hm
    (convexOn_rpow_norm (one_le_toReal one_le_p p_ne_top))
    hc.lowerSemicontinuous (hf.integrable one_le_p) hf'] with _ h using h

lemma enorm_rpow_condExp_le {p : ℝ≥0∞} (one_le_p : 1 ≤ p) (p_ne_top : p ≠ ∞) (hf : MemLp f p μ) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ^ p.toReal ≤ .ofReal (μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω) := by
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  filter_upwards [norm_rpow_condExp_le one_le_p p_ne_top hf, this] with ω hω1 hω2
  rwa [le_ofReal_iff_toReal_le (by simp) hω2, ← toReal_rpow, toReal_enorm]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma ofReal_condExp_norm_ae_le_eLpNormEssSup (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ ω ∂μ, .ofReal (μ[(‖f ·‖)|m] ω) ≤ eLpNormEssSup f μ := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le hm]
  by_cases h : eLpNormEssSup f μ = ∞
  · simp [h]
  have hf' : MemLp f ∞ μ := ⟨hf, Ne.lt_top h⟩
  have : (‖f ·‖) ≤ᵐ[μ] fun _ ↦ (eLpNormEssSup f μ).toReal := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with ω hω
    exact (ofReal_le_iff_le_toReal h).1 (by simpa)
  filter_upwards [condExp_mono (m := m) (hf'.integrable (by simp)).norm
    (integrable_const _) this] with ω hω
  exact ofReal_le_of_le_toReal (by simpa [condExp_const hm] using hω)

omit [IsFiniteMeasure μ] in
lemma MemLp.condExp' {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    MemLp μ[f|m] p μ :=
  ⟨integrable_condExp.aestronglyMeasurable, (eLpNorm_condExp_le_eLpNorm f hp).trans_lt hf.2⟩

/-- If a function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
lemma ae_bdd_condExp_of_ae_bdd' {R : ℝ} {f : Ω → E} (hbdd : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R) :
    ∀ᵐ x ∂μ, ‖(μ[f|m]) x‖ ≤ R := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  have hR : 0 ≤ R := by
    have := ae_neBot.2 hμ
    obtain ⟨ω, hω⟩ := hbdd.exists
    exact (norm_nonneg _).trans hω
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le hm, hR]
  by_cases hf : Integrable f μ
  swap; · simp [condExp_of_not_integrable hf, hR]
  filter_upwards [norm_condExp_le (m := m) f, condExp_mono (m := m) hf.norm
    (integrable_const _) hbdd] with ω hω1 hω2
  grw [hω1, hω2, condExp_const hm]

end MeasureTheory
