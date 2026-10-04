import Tengoku

/-!
# Bounds on li(2) using LeanCert numerical integration

This file provides bounds on the logarithmic integral li(2) ≈ 1.0451
using the symmetric form which makes the principal value integral
absolutely convergent.

This file imports only the lightweight `LeanCert.CertifiedBounds.Li2`
interface, which compiles in seconds. The separate machine-checked numerical
verification target is built by LeanCert's CI and is not on PNT+'s build path.

See: https://github.com/alerad/leancert
-/

open Real MeasureTheory Set
open scoped Interval

open Topology

namespace Li2Bounds

/-! ### Local definition of li (principal value integral)

This matches the definition in SecondaryDefinitions.lean but is defined
here to keep Li2Bounds.lean self-contained and avoid circular imports.
-/

/-- The logarithmic integral li(x) = ∫₀ˣ dt/log(t) (principal value).
    This is the local copy matching SecondaryDefinitions.li -/
noncomputable def li (x : ℝ) : ℝ :=
  Filter.lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))

/-! ### Symmetric Form Definition -/

/-! ### Integrability Lemmas -/

/-- 1/log(1-u) is integrable on [ε, 1) for ε > 0. -/
theorem log_one_minus_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun u => 1 / log (1 - u)) volume ε 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε1.le]
  refine Measure.integrableOn_of_bounded (M := 1 / ε) measure_Ioc_lt_top.ne
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [self_mem_ae_restrict (by measurability), Measure.ae_ne _ 1]
    with u ⟨hε_lt_u, hu_le_one⟩ hu_ne_one
  have h1mu_pos : 0 < 1 - u := by grind
  have h1mu_lt1 : 1 - u < 1 := by linarith
  have hlog_neg : log (1 - u) < 0 := log_neg h1mu_pos h1mu_lt1
  rw [Real.norm_eq_abs, abs_one_div, abs_of_neg hlog_neg]
  gcongr
  have hlog_ub : log (1 - u) ≤ -u := by
    have h := log_le_sub_one_of_pos h1mu_pos
    linarith
  linarith

/-- 1/log(1+u) is integrable on [ε, 1] for ε > 0. -/
theorem log_one_plus_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun u => 1 / log (1 + u)) volume ε 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc hε1.le fun u hu ↦
    ContinuousAt.continuousWithinAt ?_
  have : 1 + u ≠ 0 := by grind
  have : log (1 + u) ≠ 0 := by simp; grind
  fun_prop (disch := assumption)

/-! ### Integrability of g on [0, 1] -/

/-! ### Certified Bounds on li(2) -/

/-! ### Substitution Lemmas for Principal Value Connection -/

/-- For ε > 0, ∫₀^{1-ε} dt/log(t) = ∫_ε^1 du/log(1-u) via t ↦ 1 - u. -/
theorem integral_sub_left (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (0 : ℝ)..(1 - ε), 1 / log t = ∫ u in ε..1, 1 / log (1 - u) := by
  simpa using (intervalIntegral.integral_comp_sub_left (fun x => 1 / log x) 1
    (a := ε) (b := 1)).symm

/-- For ε > 0, ∫_{1+ε}^2 dt/log(t) = ∫_ε^1 du/log(1+u) via t ↦ 1 + u. -/
theorem integral_sub_right (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (1 + ε)..(2 : ℝ), 1 / log t = ∫ u in ε..1, 1 / log (1 + u) := by
  have h := intervalIntegral.integral_comp_add_right (fun x => 1 / log x) 1
    (a := ε) (b := 1)
  simp only [show ε + (1 : ℝ) = 1 + ε from by ring, show (1 : ℝ) + 1 = 2 from by ring]
    at h
  simpa [show ∀ u : ℝ, 1 / log (u + 1) = 1 / log (1 + u) from fun u ↦ by ring_nf]
    using h.symm

/-! ### Connection to Principal Value li(2)

The symmetric integral li2_symmetric equals the principal value
li(2). This follows from the substitutions u = 1-t and u = t-1
which transform the principal value integral into the absolutely
convergent symmetric form.
-/

/-- The set difference Ioc 0 x \ Ioo (1-ε) (1+ε) for small ε > 0. -/
theorem setDiff_decompose (ε x : ℝ) (hε : 0 < ε) (hx : 2 ≤ x) :
    Set.Ioc 0 x \ Set.Ioo (1 - ε) (1 + ε) = Set.Ioc 0 (1 - ε) ∪ Set.Icc (1 + ε) x := by
  grind

/-- The Set.diff integral equals the split interval integrals. -/
theorem setDiff_integral_eq_split (ε x : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 0 x \ Set.Ioo (1 - ε) (1 + ε), 1 / log t =
      (∫ t in (0 : ℝ)..(1 - ε), 1 / log t) + ∫ t in (1 + ε)..x, 1 / log t := by
  rw [setDiff_decompose ε x hε hx, setIntegral_union (by grind) measurableSet_Icc,
    intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]
  · have hlog_neg : log (1 - ε) < 0 := Real.log_neg (by linarith) (by linarith)
    have hcont : ContinuousOn (fun t => 1 / log t) (Set.Ioc 0 (1 - ε)) :=
      ContinuousOn.div continuousOn_const
        (Real.continuousOn_log.mono fun x hx => ne_of_gt hx.1)
        fun x hx => Real.log_ne_zero_of_pos_of_ne_one hx.1 (by linarith [hx.2])
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (hcont.aestronglyMeasurable measurableSet_Ioc) (-1 / log (1 - ε)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Set.mem_Ioc] at ht
    rw [norm_div, norm_one, Real.norm_eq_abs,
      abs_of_neg (Real.log_neg ht.1 (by linarith [ht.2])),
      show (-1 : ℝ) / log (1 - ε) = 1 / (-log (1 - ε)) from by ring]
    exact one_div_le_one_div_of_le (neg_pos.mpr hlog_neg)
      (by linarith [Real.log_le_log ht.1 ht.2])
  · exact ContinuousOn.integrableOn_compact isCompact_Icc
      (ContinuousOn.div continuousOn_const
        (Real.continuousOn_log.mono fun x hx => ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x))
        fun x hx => Real.log_ne_zero_of_pos_of_ne_one (by linarith [hx.1] : 0 < x)
          (by linarith [hx.1]))

end Li2Bounds
