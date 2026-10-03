/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.NullHomologous
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.DixonTheorem
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.PaperPwC1Immersion
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.SimplePoleIntegral
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.MultipointPV
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ResidueCircleIntegral
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.CurveMeasureZero
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MeasureHelpers

-- NOTE on imports / Central B:
-- The project currently maintains two parallel residue libraries with overlapping
-- root-namespace identifiers (e.g. both `LeanModularForms.ForMathlib.Residue` and
-- `LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue` define
-- `HasSimplePoleAt`; both `MultipointPV` files define `disjoint_balls_of_small_epsilon`).
-- This file commits to the legacy chain (`Residue`, `SimplePoleIntegral`,
-- `MultipointPV`, `MeromorphicCauchy`). Central theorem B
-- (`residueTheorem_simplePoles_convex`) and corollary 4
-- (`residueTheorem_simplePoles_convex_transverse`) wrap the existing
-- `generalizedResidueTheorem'` in `GeneralizedResidueTheory.Residue.GeneralizedTheoremBase`,
-- which uses the GRT chain.

/-!
# Hungerbühler–Wasem residue theorem

The generalized residue theorem of Hungerbühler and Wasem
(arXiv:1808.00997v2, Theorem 3.3): the Cauchy principal value of `∮f` along a
closed piecewise-`C¹` immersion `γ` null-homologous in an open domain `U`
equals `2πi · Σ winding(γ, s) · residue(f, s)` over the singular set `S ⊆ U`.

## Main results

* `HungerbuhlerWasem.PolarPartDecomposition` — the data of an explicit
  Laurent polar-part decomposition of a meromorphic function.
* `HungerbuhlerWasem.residueTheorem_avoidance` — central theorem A:
  decomposition-as-data form. γ avoids every pole.
* `HungerbuhlerWasem.residueTheorem_simplePoles_convex` — central theorem B:
  simple poles only on a convex domain. γ may cross poles, but two CPV
  oracles must be supplied.
* Four corollaries specializing one or the other central theorem:
  `residueTheorem_simplePoles_avoidance`, `residueTheorem_convex_avoidance`,
  `residueTheorem_simplePoles_convex_avoidance`,
  `residueTheorem_simplePoles_convex_transverse`.
* `HungerbuhlerWasem.residueTheorem_crossing` — unifying form (higher-order
  + crossings); lives in
  `LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Interval

noncomputable section

namespace HungerbuhlerWasem

/-- A **polar-part decomposition** of a meromorphic function `f` on a domain
`U \ S`: for each pole `s ∈ S`, an explicit polar part `polarPart s z =
∑ k, a_{s,k} / (z - s)^(k+1)` such that `f` minus the total polar part extends
analytically to all of `U`.

This bundles the data the residue formula needs without requiring access to
mathlib's Laurent-extraction API. Each polar part is a finite Laurent
combination at its pole; the residue at `s` is the `k = 0` coefficient. -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  /-- The polar part at each pole, viewed as a function of `z`. -/
  polarPart : ℂ → ℂ → ℂ
  /-- Order of the polar part at each pole. -/
  order : ℂ → ℕ
  /-- Laurent coefficients of the polar part at each pole. -/
  coeff : (s : ℂ) → Fin (order s) → ℂ
  /-- The polar part at `s` is the explicit Laurent sum
  `∑ k, coeff s k / (z - s)^(k+1)`. -/
  polarPart_eq : ∀ s ∈ S, ∀ z, z ≠ s →
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - s) ^ (k.val + 1)
  /-- The residue at `s ∈ S` equals the `k = 0` Laurent coefficient (for non-empty
  polar parts) or zero (for empty). -/
  residue_eq : ∀ s ∈ S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0
  /-- After subtracting the total polar part, `f` extends to a function
  differentiable on all of `U`. -/
  analyticRemainder : ℂ → ℂ
  analyticRemainder_diff : DifferentiableOn ℂ analyticRemainder U
  decomp : ∀ z ∈ U \ (↑S : Set ℂ),
    f z = analyticRemainder z + ∑ s ∈ S, polarPart s z

variable {x : ℂ}

/-- The derivative of a Lipschitz extended piecewise-`C¹` path is interval-integrable
on `[0, 1]`: derivatives of Lipschitz functions are bounded by the Lipschitz constant. -/
theorem deriv_intervalIntegrable_of_lipschitz (γP : PiecewiseC1Path x x) {K : NNReal}
    (hLip : LipschitzWith K γP.toPath.extend) :
    IntervalIntegrable (deriv γP.toPath.extend) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
  refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (stronglyMeasurable_deriv _).aestronglyMeasurable
    (ae_restrict_of_ae (Filter.Eventually.of_forall
      (fun _ => norm_deriv_le_of_lipschitz hLip)))

/-- The bad set `γ⁻¹(S) ∩ Icc 0 1` for a piecewise-`C¹` immersion `γ` and a
finite set `S` has Lebesgue measure zero. -/
theorem volume_preimage_finset_in_Icc01_zero
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) :
    volume {t ∈ Icc (0 : ℝ) 1 |
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set ℂ)} = 0 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set P : Finset ℝ := insert 0 (insert 1 γP.partition)
  have h_in_Ioo : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht htP
    have h0 : t ≠ 0 := fun h => htP (h ▸ Finset.mem_insert_self _ _)
    have h1 : t ≠ 1 := fun h => htP (h ▸
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have h_not_part : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → t ∉ γP.partition := fun t _ htP h_part =>
    htP (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_part))
  exact preimage_finset_measure_zero_of_deriv_ne_zero S
    γP.toPath.continuous_extend.continuousOn
    (fun t ht htP => γP.differentiable_off_extend t (h_in_Ioo t ht htP)
      (h_not_part t ht htP))
    (fun t ht htP => γ.toPwC1Immersion.deriv_ne_zero t (h_in_Ioo t ht htP)
      (h_not_part t ht htP))

/-- For a function `g` differentiable on `U` and a closed piecewise-`C¹`
immersion `γ` with image in `U`, the contour integrand `g(γ(t)) · γ'(t)` is
interval-integrable on `[0, 1]`. -/
private theorem contourIntegrand_diff_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {g : ℂ → ℂ}
    (h_diff : DifferentiableOn ℂ g U)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) :
    IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g
        γ.toPwC1Immersion.toPiecewiseC1Path) MeasureTheory.volume 0 1 := by
  obtain ⟨_, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  refine (deriv_intervalIntegrable_of_lipschitz γP hLip).continuousOn_mul ?_
  rw [uIcc_of_le (zero_le_one' ℝ)]
  exact h_diff.continuousOn.comp γP.toPath.continuous_extend.continuousOn hγ_in_U

/-- The "bad set" of times where γ comes within ε of some pole. -/
def cpv_badSet (γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) :
    Set ℝ := {t : ℝ | ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε}

private theorem cpv_badSet_measurableSet (γP : PiecewiseC1Path x x) (S : Finset ℂ)
    (ε : ℝ) : MeasurableSet (cpv_badSet γP S ε) := by
  classical
  have h_eq : cpv_badSet γP S ε = ⋃ s ∈ S, {t : ℝ | ‖γP.toPath.extend t - s‖ ≤ ε} := by
    ext t; simp [cpv_badSet]
  rw [h_eq]
  exact (isClosed_biUnion_finset fun s _ => isClosed_le
    ((γP.toPath.continuous_extend.sub continuous_const).norm) continuous_const).measurableSet

/-- Express `cpvIntegrandOn S g γ.extend ε` as an indicator of the contour
integrand on the complement of the bad set. -/
theorem cpvIntegrandOn_eq_indicator_compl
    (γP : PiecewiseC1Path x x) (S : Finset ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S g γP.toPath.extend ε t =
      (cpv_badSet γP S ε)ᶜ.indicator
        (PiecewiseC1Path.contourIntegrand g γP) t := by
  classical
  unfold cpvIntegrandOn cpv_badSet
  by_cases h : ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε
  · rw [ite_eq_left h, Set.indicator_of_notMem (by simpa using h)]
  · rw [ite_eq_right h, Set.indicator_of_mem (by simpa using h)]; rfl

/-- The cutoff integrand `cpvIntegrandOn S g γ.extend ε` is interval-integrable
on `[0, 1]` for any `ε`, when `g` is differentiable on `U` and γ has image in
`U`. The proof realizes the cutoff as an indicator of the (interval-integrable)
contour integrand on a measurable set. -/
theorem cpvIntegrandOn_diff_intervalIntegrable
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) {U : Set ℂ} {g : ℂ → ℂ}
    (h_diff : DifferentiableOn ℂ g U)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) (ε : ℝ) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S g
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_full := contourIntegrand_diff_intervalIntegrable γ h_diff hγ_in_U
  rw [show (fun t => cpvIntegrandOn S g γP.toPath.extend ε t) =
    (cpv_badSet γP S ε)ᶜ.indicator (PiecewiseC1Path.contourIntegrand g γP) from
    funext fun t => cpvIntegrandOn_eq_indicator_compl γP S g ε t]
  rw [intervalIntegrable_iff] at h_full ⊢
  exact h_full.indicator (cpv_badSet_measurableSet γP S ε).compl

/-- Almost every `t ∈ Icc 0 1` satisfies `γ(t) ∉ S` — a consequence of the
immersion property (the bad set has measure zero). -/
private theorem cpv_ae_not_mem_S (γ : ClosedPwC1Immersion x) (S : Finset ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc (0 : ℝ) 1)),
      γ.toPwC1Immersion.toPiecewiseC1Path t ∉ (↑S : Set ℂ) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (volume_preimage_finset_in_Icc01_zero γ S)
  intro t ht
  push Not at ht
  exact ht

/-- For a function `g` differentiable on `U` and γ ⊆ U, the cutoff integrands
converge pointwise a.e. on `Icc 0 1` to the contour integrand as `ε → 0⁺`. -/
theorem cpvIntegrandOn_tendsto_contourIntegrand_ae
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) (g : ℂ → ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)),
      Tendsto
        (fun ε => cpvIntegrandOn S g
          γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
        (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand g
          γ.toPwC1Immersion.toPiecewiseC1Path t)) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_ae := cpv_ae_not_mem_S γ S
  rw [Set.uIoc_of_le zero_le_one, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_ae
  filter_upwards [h_ae] with t h_not_mem ht
  have h_not_mem' : γP t ∉ (↑S : Set ℂ) := h_not_mem ⟨le_of_lt ht.1, ht.2⟩
  have h_far : ∀ s ∈ S, 0 < ‖γP.toPath.extend t - s‖ := fun s hs =>
    norm_pos_iff.mpr <| sub_ne_zero.mpr <| fun heq =>
      h_not_mem' (heq ▸ Finset.mem_coe.mpr hs : γP.toPath.extend t ∈ (↑S : Set ℂ))
  suffices h_lim_const :
      (fun ε => cpvIntegrandOn S g γP.toPath.extend ε t) =ᶠ[𝓝[>] 0]
        (fun _ => PiecewiseC1Path.contourIntegrand g γP t) from
    Tendsto.congr' h_lim_const.symm tendsto_const_nhds
  by_cases hS : S.Nonempty
  · obtain ⟨δ, hδ_mem, hδ_min⟩ := Finset.exists_min_image S
      (fun s => ‖γP.toPath.extend t - s‖) hS
    filter_upwards [Ioo_mem_nhdsGT (h_far δ hδ_mem)] with ε hε
    rw [cpvIntegrandOn_of_forall_gt fun s hs => lt_of_lt_of_le hε.2 (hδ_min s hs)]
    rfl
  · have h_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    filter_upwards [self_mem_nhdsWithin] with ε _
    subst h_empty
    rfl

end HungerbuhlerWasem

end
