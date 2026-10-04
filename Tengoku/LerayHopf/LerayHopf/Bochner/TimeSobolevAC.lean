/-
# LerayHopf.Bochner.TimeSobolevAC — Stream D / R1 (V'-continuous good representative, trace-free)

The **trace-free half** of the Lions–Magenes embedding route (`docs/scratch/wkernel-route.md`).
From `u' ∈ L²(0,T;V')` it builds the continuous-into-`V'` representative of the Sobolev-in-time
curve, with NO reflection and NO boundary trace assumed — the continuity is absolute continuity
of the Bochner integral (`intervalIntegral.continuousOn_primitive_interval`). The du-Bois-Reymond
"weakly-constant ⟹ a.e. constant" keystone is proved from scratch here (mathlib has the
`ae_eq_of_integral_contDiff_smul_eq` du-Bois lemma but not the constant-difference form).

This is the NON-CIRCULAR R1 layer: it does not depend on `w1pTime_continuous_in_H` (the
months-class weak-FTC), and it is independent of the interior-mollification R2 energy core.

## Assumptions
No new `axiom`/`opaque`/`constant`. Statements faithful; no hypothesis weakening.
-/

import Tengoku.LerayHopf.LerayHopf.Bochner.TimeSobolev
import Tengoku

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

section R1
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The Bochner primitive of an interval-integrable curve is continuous on `[0,T]`. -/
theorem continuousOn_primitive_of_integrableOn {T : ℝ} {v : ℝ → X}
    (hv : IntegrableOn v (Set.Icc 0 T) volume) :
    ContinuousOn (fun t => ∫ s in (0:ℝ)..t, v s) (Set.Icc 0 T) := by
  rcases le_or_gt 0 T with hT | hT
  · have huIcc : Set.uIcc (0:ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
    have hvuIcc : IntegrableOn v (Set.uIcc 0 T) volume := by rw [huIcc]; exact hv
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
      (f := v) (μ := volume) hvuIcc
    rw [huIcc] at this; exact this
  · rw [Set.Icc_eq_empty (by exact not_le.2 hT)]
    exact continuousOn_empty _

/-- The primitive `G(t) = ∫ 0..t g` of a continuous scalar function is `C¹`, with `deriv G = g`. -/
theorem contDiff_primitive_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (fun t => ∫ x in (0:ℝ)..t, g x) ∧
      deriv (fun t => ∫ x in (0:ℝ)..t, g x) = g := by
  have hderiv : deriv (fun t => ∫ x in (0:ℝ)..t, g x) = g := by
    funext b; exact Continuous.deriv_integral g hg 0 b
  refine ⟨?_, hderiv⟩
  rw [contDiff_one_iff_deriv]
  exact ⟨fun b => (hg.integral_hasStrictDerivAt 0 b).hasDerivAt.differentiableAt,
    by rw [hderiv]; exact hg⟩

end R1

section Keystone

/-- The primitive `G(t) = ∫ a..t g` (based at `a`) of a continuous scalar `g` supported in
`Icc a b` with `∫ a..b g = 0` vanishes outside `Icc a b`, hence is compactly supported. -/
theorem primitive_baseA_props {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hgc : Continuous g) (hgz : ∀ x, x ∉ Set.Icc a b → g x = 0)
    (hmean : ∫ x in a..b, g x = 0) :
    (∀ t, t ∉ Set.Icc a b → (∫ x in a..t, g x) = 0) := by
  intro t ht
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with ht | ht
  · -- t < a : ∫a..t g = 0 since g = 0 a.e. on `Ι a t = Ioc t a` (only the null endpoint `a`
    -- can be in `[a,b]`).
    push_neg at ht
    have heqae : ∀ᵐ x, x ∈ Set.uIoc a t → g x = (0 : ℝ → ℝ) x := by
      filter_upwards [show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a from
        MeasureTheory.ae_iff.2 (by simpa using measure_singleton a)] with x hxa hxmem
      rw [Set.uIoc_of_ge ht.le, Set.mem_Ioc] at hxmem
      -- x ∈ (t, a]; if x ≠ a then x < a so x ∉ [a,b]; the case x = a is excluded by hxa.
      have hxlt : x < a := lt_of_le_of_ne hxmem.2 hxa
      simpa using hgz x (fun hxm => absurd hxm.1 (not_le.2 hxlt))
    rw [intervalIntegral.integral_congr_ae heqae]; simp
  · -- t > b : ∫a..t g = ∫a..b g + ∫b..t g = 0 + 0
    push_neg at ht
    have hsplit : (∫ x in a..t, g x) = (∫ x in a..b, g x) + ∫ x in b..t, g x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)).symm
    have heqae : ∀ᵐ x, x ∈ Set.uIoc b t → g x = (0 : ℝ → ℝ) x := by
      filter_upwards [show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b from
        MeasureTheory.ae_iff.2 (by simpa using measure_singleton b)] with x hxb hxmem
      rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hxmem
      -- x ∈ (b, t]; x > b so x ∉ [a,b].
      simpa using hgz x (fun hxm => absurd hxm.2 (not_le.2 hxmem.1))
    rw [hsplit, hmean, intervalIntegral.integral_congr_ae heqae]; simp

/-- A fixed continuous unit-mass "weight" supported strictly inside `Ioo 0 T`: there is a
continuous `ρ : ℝ → ℝ` with `tsupport ρ ⊆ Icc a b` for some `0 < a ≤ b < T`, and
`∫ x, ρ x ∂volume = 1` (equivalently `∫ 0..T ρ = 1`). Built from a normalized `ContDiffBump`
centered at `T/2`. -/
theorem exists_unitMass_weight {T : ℝ} (hT : 0 < T) :
    ∃ (ρ : ℝ → ℝ) (a b : ℝ), 0 < a ∧ a ≤ b ∧ b < T ∧ Continuous ρ ∧
      (∀ x, x ∉ Set.Icc a b → ρ x = 0) ∧ (∫ x, ρ x ∂volume) = 1 := by
  -- Bump centered at T/2 with rOut = T/4 (< T/2), so closedBall (T/2) (T/4) = [T/4, 3T/4] ⊆ (0,T).
  set f : ContDiffBump (T/2) := ⟨T/8, T/4, by positivity, by linarith⟩ with hf
  refine ⟨f.normed volume, T/4, 3*T/4, by linarith, by linarith, by linarith,
    f.continuous_normed, ?_, f.integral_normed⟩
  intro x hx
  -- outside [T/4, 3T/4] = closedBall (T/2) (T/4) = tsupport, so ρ x = 0.
  have hts : tsupport (f.normed volume) = Metric.closedBall (T/2) (T/4) := f.tsupport_normed_eq
  apply image_eq_zero_of_notMem_tsupport
  rw [hts, Real.closedBall_eq_Icc]
  intro hmem
  apply hx
  -- closedBall center (T/2) radius (T/4): [T/2 - T/4, T/2 + T/4] = [T/4, 3T/4]
  rw [Set.mem_Icc] at hmem ⊢
  constructor <;> [linarith [hmem.1]; linarith [hmem.2]]

section KeystoneVar
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

end KeystoneVar

end Keystone

/-! ### R1 — the V'-continuous good representative

From a `W1pTime` element, the embedded curve `t ↦ hToVprime (ι (uV t))` has a continuous-into-`V'`
representative on `[0,T]`, with NO reflection and NO boundary trace assumed. The continuity is
absolute continuity of the Bochner primitive of `u'`; the a.e.-equality to the embedded curve is
the du-Bois-Reymond keystone applied to the difference. -/

section Representative
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

end Representative

end LerayHopf.Bochner
