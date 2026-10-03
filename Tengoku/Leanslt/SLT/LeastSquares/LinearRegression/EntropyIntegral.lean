/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Tengoku.Leanslt.SLT.LeastSquares.LinearRegression.EuclideanReduction
import Tengoku.Leanslt.SLT.LeastSquares.LinearRegression.IntegralBounds
import Tengoku.Leanslt.SLT.MetricEntropy

/-!
# Entropy Integral Bounds for Linear Regression

This file proves the entropy integral bound for linear regression.

## Main Definitions

* `linearEntropyIntegral`: The entropy integral for the linear regression localized ball

## Main Results

* `linearLocalizedBallImage_totallyBounded`: The localized ball image is totally bounded
* `metricEntropy_linearLocalizedBall_le`: Metric entropy is bounded by d * log(1 + 2δ/ε)
* `linearEntropyIntegral_le`: The entropy integral is bounded by 4δ√d
* `linearEntropyIntegralENNReal_ne_top`: The ENNReal entropy integral is finite

-/

open MeasureTheory Finset BigOperators Real ProbabilityTheory Metric Set
open scoped NNReal ENNReal

namespace LeastSquares

variable {n d : ℕ}

/-! ## Linear Entropy Integral Bound

The entropy integral for linear regression:
∫₀^D √(log N(ε, B_n(δ), ‖·‖_n)) dε ≤ 2δ√(d/n)

This bound is key for applying Dudley's theorem to get Rademacher complexity bounds.
-/

/-- The entropy integral for the linear regression localized ball.
    This is ∫₀^D √(log N(ε, linearLocalizedBallImage)) dε -/
noncomputable def linearEntropyIntegral (n d : ℕ) (δ D : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  entropyIntegral (linearLocalizedBallImage n d δ x) D

/-- The linearLocalizedBallImage is totally bounded (as a finite-dimensional compact set image). -/
lemma linearLocalizedBallImage_totallyBounded (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    TotallyBounded (linearLocalizedBallImage n d δ x) := by
  -- The image under empiricalToEuclidean is the euclideanLocalizedBall, which is totally bounded
  -- (since it's a closed and bounded set in finite dimension)
  -- Then pull back via the uniformly continuous map empiricalToEuclidean
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  -- Show that empiricalToEuclidean '' linearLocalizedBallImage is totally bounded
  have himage_eq := empiricalToEuclidean_image_eq hn x δ
  have htb_euc : TotallyBounded (euclideanLocalizedBall n d δ x) := by
    -- euclideanLocalizedBall is contained in a ball of radius δ√n
    apply TotallyBounded.subset (s₂ := Metric.closedBall 0 (δ * Real.sqrt n))
    · intro v hv
      unfold euclideanLocalizedBall euclideanBallOrigin at hv
      simp only [Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right] at hv ⊢
      exact hv.1
    · exact (ProperSpace.isCompact_closedBall 0 _).totallyBounded
  rw [← himage_eq] at htb_euc
  -- Use that the inverse map euclideanToEmpirical is Lipschitz
  -- Pull back totally bounded via the bijection
  -- The map empiricalToEuclidean scales distances by √n, so euclideanToEmpirical divides by √n
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  -- Get a finite cover for the image
  have hε_scaled : 0 < ε * Real.sqrt n := mul_pos hε hsqrt_pos
  obtain ⟨t, ht_finite, ht_cover⟩ := Metric.totallyBounded_iff.mp htb_euc (ε * Real.sqrt n) hε_scaled
  -- Map back to EmpiricalSpace
  use t.image (euclideanToEmpirical n)
  constructor
  · exact ht_finite.image _
  · intro y hy
    -- y is in linearLocalizedBallImage
    -- empiricalToEuclidean y is in the image, so covered by some ball
    have hy_euc : empiricalToEuclidean n y ∈ empiricalToEuclidean n '' linearLocalizedBallImage n d δ x :=
      Set.mem_image_of_mem _ hy
    have hy_cover := ht_cover hy_euc
    rw [Set.mem_iUnion₂] at hy_cover
    obtain ⟨z, hz_mem, hz_ball⟩ := hy_cover
    rw [Set.mem_iUnion₂]
    refine ⟨euclideanToEmpirical n z, Set.mem_image_of_mem _ hz_mem, ?_⟩
    rw [Metric.mem_ball]
    -- dist y (euclideanToEmpirical z) = dist(empiricalToEuclidean y, z) / √n
    have hdist := dist_euclidean_eq_sqrt_n_mul_dist_empirical hn y (euclideanToEmpirical n z)
    simp only [empiricalToEuclidean_euclideanToEmpirical] at hdist
    have hdist' : dist y (euclideanToEmpirical n z) = dist (empiricalToEuclidean n y) z / Real.sqrt n := by
      have hne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
      field_simp at hdist ⊢
      linarith
    rw [hdist']
    rw [Metric.mem_ball] at hz_ball
    calc dist (empiricalToEuclidean n y) z / Real.sqrt n
        < (ε * Real.sqrt n) / Real.sqrt n := by
          apply div_lt_div_of_pos_right hz_ball hsqrt_pos
      _ = ε := by field_simp

/-- Helper: metricEntropyOfNat n ≤ log N when n ≤ N as reals. -/
lemma metricEntropyOfNat_le_log {m : ℕ} {N : ℝ} (hN_pos : 1 < N) (hm_le : (m : ℝ) ≤ N) :
    metricEntropyOfNat m ≤ Real.log N := by
  unfold metricEntropyOfNat
  split_ifs with h
  · exact Real.log_nonneg (le_of_lt hN_pos)
  · push Not at h
    apply Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < m)) hm_le

/-- The linearLocalizedBallImage equals the empiricalMetricImage of the localizedBall
    for the linear predictor class. This is the key lemma connecting the two formulations. -/
lemma linearLocalizedBallImage_eq_empiricalImage (x : Fin n → EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    linearLocalizedBallImage n d δ x =
    empiricalMetricImage n x '' localizedBall (linearPredictorClass d) δ x := by
  unfold linearLocalizedBallImage linearLocalizedBall
  rfl

/-- Integrability of the explicit entropy bound function. -/
lemma linearEntropyIntegral_integrableOn {δ D : ℝ} (hδ : 0 < δ) (hDδ : D ≤ 2 * δ) :
    MeasureTheory.IntegrableOn
      (fun ε => Real.sqrt (d * Real.log (1 + 2 * δ / ε))) (Set.Ioc 0 D) := by
  -- Handle degenerate case D ≤ 0
  by_cases hD_pos : 0 < D
  case neg =>
    push Not at hD_pos
    have hempty : Set.Ioc 0 D = ∅ := Set.Ioc_eq_empty (not_lt.mpr hD_pos)
    rw [hempty]
    exact MeasureTheory.integrableOn_empty
  case pos =>
    -- Split into cases based on whether D ≤ 1
    by_cases hD_le_one : D ≤ 1
    · -- Case D ≤ 1: bound by √d * (√(log(1+2δ)) + √(-log u)), which is integrable
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      -- The constant part and √(-log u) part are both integrable on (0, D]
      have hlog_1_2d_nonneg : 0 ≤ Real.log (1 + 2 * δ) := Real.log_nonneg (by linarith)
      have hfin : volume (Set.Ioo 0 D) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      have hint_const : MeasureTheory.IntegrableOn
          (fun _ : ℝ => Real.sqrt d * Real.sqrt (Real.log (1 + 2 * δ)))
          (Set.Ioo 0 D) volume :=
        MeasureTheory.integrableOn_const hfin
      have hint_sqrt : MeasureTheory.IntegrableOn
          (fun u => Real.sqrt d * Real.sqrt (-Real.log u)) (Set.Ioo 0 D) volume := by
        apply MeasureTheory.IntegrableOn.mono_set _ (Set.Ioo_subset_Ioo_right hD_le_one)
        exact (MeasureTheory.Integrable.const_mul integrableOn_sqrt_neg_log (Real.sqrt d))
      have hint_sum : MeasureTheory.IntegrableOn
          (fun u => Real.sqrt d * (Real.sqrt (Real.log (1 + 2 * δ)) + Real.sqrt (-Real.log u)))
          (Set.Ioo 0 D) volume := by
        simp_rw [mul_add]
        exact MeasureTheory.Integrable.add hint_const hint_sqrt
      apply MeasureTheory.Integrable.mono' hint_sum
      · exact (measurable_sqrt_d_log_one_plus_c_div d (2 * δ)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
            Real.sqrt_mul (Nat.cast_nonneg d)]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg d)
        have hu_pos : 0 < u := hu.1
        have hu_lt : u < D := hu.2
        have hu_lt_one : u < 1 := lt_of_lt_of_le hu_lt hD_le_one
        have h_term_pos : 0 < 1 + 2 * δ / u := by
          have : 0 < 2 * δ / u := div_pos (by linarith) hu_pos
          linarith
        have hlog_bound : Real.log (1 + 2 * δ / u) ≤ Real.log (1 + 2 * δ) + (-Real.log u) := by
          have h1 : Real.log (1 + 2 * δ / u) ≤ Real.log ((1 + 2 * δ) / u) := by
            apply Real.log_le_log h_term_pos
            rw [add_div]
            have h_one_le : 1 ≤ 1 / u := one_le_one_div hu_pos (le_of_lt hu_lt_one)
            linarith
          rw [Real.log_div (by linarith : (1 : ℝ) + 2 * δ ≠ 0) (ne_of_gt hu_pos)] at h1
          linarith
        have hneg_log_nonneg : 0 ≤ -Real.log u := by
          rw [neg_nonneg]; exact Real.log_nonpos (le_of_lt hu_pos) (le_of_lt hu_lt_one)
        calc Real.sqrt (Real.log (1 + 2 * δ / u))
            ≤ Real.sqrt (Real.log (1 + 2 * δ) + (-Real.log u)) := Real.sqrt_le_sqrt hlog_bound
          _ ≤ Real.sqrt (Real.log (1 + 2 * δ)) + Real.sqrt (-Real.log u) :=
              sqrt_add_le hlog_1_2d_nonneg hneg_log_nonneg
    · -- Case D > 1: Split into (0, 1] and (1, D]
      push Not at hD_le_one
      rw [← Set.Ioc_union_Ioc_eq_Ioc (by linarith : (0 : ℝ) ≤ 1) (le_of_lt hD_le_one)]
      apply MeasureTheory.IntegrableOn.union
      · -- (0, 1]: same bound as D ≤ 1 case
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        have hlog_1_2d_nonneg : 0 ≤ Real.log (1 + 2 * δ) := Real.log_nonneg (by linarith)
        have hfin : volume (Set.Ioo (0:ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
        have hint_const : MeasureTheory.IntegrableOn
            (fun _ : ℝ => Real.sqrt d * Real.sqrt (Real.log (1 + 2 * δ)))
            (Set.Ioo 0 1) volume :=
          MeasureTheory.integrableOn_const hfin
        have hint_sqrt : MeasureTheory.IntegrableOn
            (fun u => Real.sqrt d * Real.sqrt (-Real.log u)) (Set.Ioo 0 1) volume :=
          (MeasureTheory.Integrable.const_mul integrableOn_sqrt_neg_log (Real.sqrt d))
        have hint_sum : MeasureTheory.IntegrableOn
            (fun u => Real.sqrt d * (Real.sqrt (Real.log (1 + 2 * δ)) + Real.sqrt (-Real.log u)))
            (Set.Ioo 0 1) volume := by
          simp_rw [mul_add]
          exact MeasureTheory.Integrable.add hint_const hint_sqrt
        apply MeasureTheory.Integrable.mono' hint_sum
        · exact (measurable_sqrt_d_log_one_plus_c_div d (2 * δ)).aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
              Real.sqrt_mul (Nat.cast_nonneg d)]
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg d)
          have hu_pos : 0 < u := hu.1
          have hu_lt : u < 1 := hu.2
          have h_term_pos : 0 < 1 + 2 * δ / u := by
            have : 0 < 2 * δ / u := div_pos (by linarith) hu_pos
            linarith
          have hlog_bound : Real.log (1 + 2 * δ / u) ≤ Real.log (1 + 2 * δ) + (-Real.log u) := by
            have h1 : Real.log (1 + 2 * δ / u) ≤ Real.log ((1 + 2 * δ) / u) := by
              apply Real.log_le_log h_term_pos
              rw [add_div]
              have h_one_le : 1 ≤ 1 / u := one_le_one_div hu_pos (le_of_lt hu_lt)
              linarith
            rw [Real.log_div (by linarith : (1 : ℝ) + 2 * δ ≠ 0) (ne_of_gt hu_pos)] at h1
            linarith
          have hneg_log_nonneg : 0 ≤ -Real.log u := by
            rw [neg_nonneg]; exact Real.log_nonpos (le_of_lt hu_pos) (le_of_lt hu_lt)
          calc Real.sqrt (Real.log (1 + 2 * δ / u))
              ≤ Real.sqrt (Real.log (1 + 2 * δ) + (-Real.log u)) := Real.sqrt_le_sqrt hlog_bound
            _ ≤ Real.sqrt (Real.log (1 + 2 * δ)) + Real.sqrt (-Real.log u) :=
                sqrt_add_le hlog_1_2d_nonneg hneg_log_nonneg
      · -- (1, D]: bounded by constant √(d * log(1 + 2δ))
        have hD_finite : volume (Set.Ioc 1 D) ≠ ⊤ := by
          rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
        have hint_const : MeasureTheory.IntegrableOn
            (fun _ : ℝ => Real.sqrt (d * Real.log (1 + 2 * δ)))
            (Set.Ioc 1 D) volume :=
          MeasureTheory.integrableOn_const hD_finite
        apply MeasureTheory.Integrable.mono' hint_const
        · exact (measurable_sqrt_d_log_one_plus_c_div d (2 * δ)).aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hu_ge : 1 ≤ u := le_of_lt hu.1
          have h_term_pos : 0 < 1 + 2 * δ / u := by
            have : 0 < 2 * δ / u := div_pos (by linarith) (lt_of_lt_of_le (by linarith : (0:ℝ) < 1) hu_ge)
            linarith
          apply Real.sqrt_le_sqrt
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
          apply Real.log_le_log h_term_pos
          have : 2 * δ / u ≤ 2 * δ := div_le_self (by linarith) hu_ge
          linarith

/-! ### Rank-based Entropy Bounds

These lemmas generalize the entropy bounds from requiring full rank (hinj) to only requiring
that the design matrix has positive rank. The bounds use `designMatrixRank x` instead of `d`. -/

end LeastSquares
