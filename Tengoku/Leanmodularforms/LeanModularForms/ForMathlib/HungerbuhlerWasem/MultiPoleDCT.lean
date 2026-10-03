/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.HungerbuhlerWasem

/-!
# Multi-pole DCT lift for the polar-part Cauchy principal value (T-BR-Y5)

When `γ` crosses **multiple** poles in `S`, a singleton-CPV
`HasCauchyPV (decomp.polarPart s) γ s L` at one pole `s ∈ S` can be lifted to
the multi-point form `HasCauchyPVOn S (decomp.polarPart s) γ L`
**without** requiring `γ` to avoid the other poles in `S \ {s}`.

This eliminates the `h_avoid_others_per_pole` restriction in
`residueTheorem_crossing_*`.

## Strategy

The integrand `cpvIntegrandOn S f γ ε t` differs from the singleton-form
`cpvIntegrand f γ s ε t` exactly on the set

  `D(ε) := { t : (∃ s' ∈ S \ {s}, ‖γ(t) - s'‖ ≤ ε) ∧ ε < ‖γ(t) - s‖ }`

For `f = decomp.polarPart s`:
- the Laurent expression of `f` is bounded uniformly by some `M_polar` on
  `D(ε)` (when ε is small enough);
- `‖γ'(t)‖ ≤ K` (the Lipschitz constant);
- `vol(D(ε)) ≤ vol(badSet for S \ {s})(ε) → 0` as ε → 0+ (immersion → preimage
  of finite set has measure zero).

## Main results

* `MultiPoleDCT.badSet_volume_tendsto_zero` — `vol(badSet γ T ε) → 0` as
  `ε → 0+` when `γ` is an immersion and `T` is finite.
* `MultiPoleDCT.cpvIntegrand_polarPart_intervalIntegrable` — singleton
  cutoff integrand for the polar part is interval-integrable.
* `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole` — the
  singleton-to-multipole CPV lift (the headline T-BR-Y5 result).

-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

namespace MultiPoleDCT

variable {x : ℂ}

/-- The "bad set" for a finite set `T` of pole candidates: parameters `t ∈ [0,1]`
where `γ(t)` is within `ε` of some `s' ∈ T`. As `ε → 0+`, the bad sets shrink
to `γ⁻¹(T) ∩ [0,1]`. -/
def badSetIcc (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) : Set ℝ :=
  {t ∈ Icc (0 : ℝ) 1 | ∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε}

theorem badSetIcc_measurableSet (γP : PiecewiseC1Path x x) (T : Finset ℂ)
    (ε : ℝ) : MeasurableSet (badSetIcc γP T ε) := by
  classical
  have h_eq : badSetIcc γP T ε =
      Icc (0 : ℝ) 1 ∩ ⋃ s' ∈ T, {t : ℝ | ‖γP.toPath.extend t - s'‖ ≤ ε} := by
    ext t; simp only [badSetIcc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]; tauto
  rw [h_eq]
  refine measurableSet_Icc.inter (MeasurableSet.biUnion T.countable_toSet fun s' _ => ?_)
  exact (isClosed_le ((γP.toPath.continuous_extend.sub continuous_const).norm)
    continuous_const).measurableSet

theorem badSetIcc_mono (γP : PiecewiseC1Path x x) (T : Finset ℂ) :
    Monotone (badSetIcc γP T) :=
  fun _ _ hε _ ⟨ht_Icc, s', hs'T, h_le⟩ => ⟨ht_Icc, s', hs'T, h_le.trans hε⟩

theorem badSetIcc_subset_Icc (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) :
    badSetIcc γP T ε ⊆ Icc (0 : ℝ) 1 := fun _ ht => ht.1

theorem badSetIcc_volume_ne_top (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) :
    volume (badSetIcc γP T ε) ≠ ⊤ :=
  ((measure_mono (badSetIcc_subset_Icc γP T ε)).trans_lt measure_Icc_lt_top).ne

/-- Intersection of all bad sets (over ε > 0) equals the preimage of `T` in `[0,1]`. -/
theorem badSetIcc_iInter_pos (γP : PiecewiseC1Path x x) (T : Finset ℂ) :
    (⋂ ε ∈ Set.Ioi (0 : ℝ), badSetIcc γP T ε) =
      {t ∈ Icc (0 : ℝ) 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)} := by
  classical
  ext t
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Ioi]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨(h 1 zero_lt_one).1, ?_⟩
    by_contra h_notin
    by_cases hT_ne : T.Nonempty
    · have h_pos : ∀ s' ∈ T, 0 < ‖γP.toPath.extend t - s'‖ := fun s' hs' =>
        norm_pos_iff.mpr (sub_ne_zero.mpr fun heq =>
          h_notin (heq ▸ Finset.mem_coe.mpr hs'))
      obtain ⟨s_min, hs_min_mem, hs_min⟩ := Finset.exists_min_image T
        (fun s' => ‖γP.toPath.extend t - s'‖) hT_ne
      have h_min_pos := h_pos s_min hs_min_mem
      obtain ⟨_, s', hs'T, h_close⟩ :=
        h (‖γP.toPath.extend t - s_min‖ / 2) (by linarith)
      linarith [hs_min s' hs'T, h_close]
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hT_ne
      exact absurd (h 1 zero_lt_one).2.choose_spec.1 (Finset.notMem_empty _)
  · intro ⟨ht_Icc, ht_in_T⟩ ε hε_pos
    refine ⟨ht_Icc, _, Finset.mem_coe.mp ht_in_T, ?_⟩
    rw [sub_self, norm_zero]
    exact hε_pos.le

/-- The volume of the bad set tends to zero as `ε → 0+` for a closed piecewise-`C¹`
immersion `γ`. -/
theorem badSet_volume_tendsto_zero (γ : ClosedPwC1Immersion x) (T : Finset ℂ) :
    Tendsto (fun ε : ℝ => volume (badSetIcc γ.toPwC1Immersion.toPiecewiseC1Path T ε))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_lim := MeasureTheory.tendsto_measure_biInter_gt
    (μ := MeasureTheory.volume) (s := badSetIcc γP T) (a := (0 : ℝ))
    (fun r _ => (badSetIcc_measurableSet γP T r).nullMeasurableSet)
    (fun _ _ _ hij => badSetIcc_mono γP T hij)
    ⟨1, zero_lt_one, badSetIcc_volume_ne_top γP T 1⟩
  have h_iInter_eq : volume (⋂ r, ⋂ (_ : r > (0 : ℝ)), badSetIcc γP T r) = 0 := by
    rw [show (⋂ r, ⋂ (_ : r > (0 : ℝ)), badSetIcc γP T r) =
        {t ∈ Icc (0 : ℝ) 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)}
      from badSetIcc_iInter_pos γP T]
    exact volume_preimage_finset_in_Icc01_zero γ T
  rwa [h_iInter_eq] at h_lim

/-- The singleton-CPV cutoff integrand for the polar part `decomp.polarPart s`
is interval-integrable on `[0, 1]` for every `ε > 0`. Mirrors
`cpvIntegrandOn_polarPart_intervalIntegrable` but for the singleton form. -/
theorem cpvIntegrand_polarPart_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ}
    {f : ℂ → ℂ} (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrand (decomp.polarPart s)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  set laurentSum : ℂ → ℂ := fun z => ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
  set h_curve : ℝ → ℂ := fun t =>
    laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
  have h_indicator_eq :
      (fun t => cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t) =
      {t : ℝ | ε < ‖γP.toPath.extend t - s‖}.indicator h_curve := by
    funext t
    unfold cpvIntegrand
    by_cases h : ε < ‖γP.toPath.extend t - s‖
    · have h_ne : γP.toPath.extend t ≠ s := fun heq => by
        rw [heq, sub_self, norm_zero] at h; linarith
      rw [ite_eq_left h, Set.indicator_of_mem (a := t) h]
      change decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t =
        laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
      rw [decomp.polarPart_eq s hs _ h_ne]
    · rw [ite_eq_right h, Set.indicator_of_notMem (a := t) h]
  have h_meas_set : MeasurableSet {t : ℝ | ε < ‖γP.toPath.extend t - s‖} :=
    (isOpen_lt continuous_const
      (γP.toPath.continuous_extend.sub continuous_const).norm).measurableSet
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / ε ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hε.le _)
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg K.coe_nonneg
  have h_bound_on_set : ∀ t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖},
      ‖h_curve t‖ ≤ M := fun t h_far_s => by
    rw [show ‖h_curve t‖ = ‖laurentSum (γP.toPath.extend t)‖ * ‖deriv γP.toPath.extend t‖
      from norm_mul _ _]
    exact mul_le_mul ((norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ => by
        rw [norm_div, norm_pow]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε _)
          (pow_le_pow_left₀ hε.le h_far_s.le _))
      (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _) h_M_polar_nonneg
  have h_curve_meas : Measurable h_curve :=
    (Finset.measurable_sum _ fun k _ =>
      (((γP.toPath.continuous_extend.measurable.sub_const s).pow_const _).const_div _)).mul
      (measurable_deriv _)
  rw [intervalIntegrable_iff, h_indicator_eq]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    (h_curve_meas.aestronglyMeasurable.indicator h_meas_set) M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  by_cases ht_in : t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖}
  · rw [Set.indicator_of_mem ht_in]; exact h_bound_on_set t ht_in
  · rw [Set.indicator_of_notMem ht_in, norm_zero]; exact h_M_nonneg

variable {U : Set ℂ}

end MultiPoleDCT

end HungerbuhlerWasem

end
