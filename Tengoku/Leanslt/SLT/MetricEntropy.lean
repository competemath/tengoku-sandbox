/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Tengoku.Leanslt.SLT.CoveringNumber
import Tengoku.Leanslt.SLT.MeasureInfrastructure
import Tengoku

/-!
# Metric Entropy

Metric entropy (logarithm of covering number) and the entropy integral for Dudley's bound.

## Design Note
Two-level design: ENNReal `entropyIntegralENNReal` (canonical) with real wrapper `entropyIntegral`.

## Main definitions

* `metricEntropy` / `metricEntropyENNReal`: log N(ε, s)
* `dudleyIntegrand`: √log N(ε, s) as ENNReal
* `entropyIntegralENNReal`: ∫₀^D √log N(ε, s) dε (canonical)
* `entropyIntegral`: Real-valued wrapper via `.toReal`

## Main results

* Monotonicity lemmas for entropy and entropy integral
* Dyadic sum approximation: `dyadicRHS_le_four_times_entropyIntegral`

-/

open Set Metric Real MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {A : Type*} [PseudoMetricSpace A]

/-!
## Metric Entropy (Real-valued)
-/

/-- Helper to compute metric entropy given a natural number. -/
def metricEntropyOfNat (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else Real.log n

lemma metricEntropyOfNat_nonneg (n : ℕ) : 0 ≤ metricEntropyOfNat n := by
  unfold metricEntropyOfNat
  split_ifs with hn
  · exact le_rfl
  · push Not at hn
    exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.one_le_of_lt hn))

lemma metricEntropyOfNat_mono {n m : ℕ} (h : n ≤ m) : metricEntropyOfNat n ≤ metricEntropyOfNat m := by
  unfold metricEntropyOfNat
  split_ifs with hn hm hm
  · exact le_rfl
  · push Not at hm
    exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.one_le_of_lt hm))
  · push Not at hn
    omega
  · push Not at hn
    exact Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < n)) (Nat.cast_le.mpr h)

/-- Metric entropy: log of the covering number.
    Returns 0 if the covering number is infinite or ≤ 1 (to avoid log issues). -/
def metricEntropy (eps : ℝ) (s : Set A) : ℝ :=
  match _h : coveringNumber eps s with
  | ⊤ => 0
  | (n : ℕ) => metricEntropyOfNat n

/-- Metric entropy is non-negative. -/
lemma metricEntropy_nonneg (eps : ℝ) (s : Set A) : 0 ≤ metricEntropy eps s := by
  unfold metricEntropy
  split
  · exact le_rfl
  · exact metricEntropyOfNat_nonneg _

/-!
## Square Root of Entropy (Real-valued)
-/

/-- Square root of metric entropy: √log N(ε, s). -/
def sqrtEntropy (eps : ℝ) (s : Set A) : ℝ :=
  Real.sqrt (metricEntropy eps s)

/-- Square root entropy is non-negative. -/
lemma sqrtEntropy_nonneg (eps : ℝ) (s : Set A) : 0 ≤ sqrtEntropy eps s :=
  Real.sqrt_nonneg _

/-- Helper: √(log (a * b)) ≤ √(log a) + √(log b) for a, b ≥ 1.
    Used for bounding edge cardinalities in the Dudley chaining argument. -/
lemma sqrt_log_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.sqrt (Real.log (a * b)) ≤ Real.sqrt (Real.log a) + Real.sqrt (Real.log b) := by
  by_cases ha2 : a ≤ 1
  · have ha1 : a = 1 := le_antisymm ha2 ha
    simp [ha1]
  by_cases hb2 : b ≤ 1
  · have hb1 : b = 1 := le_antisymm hb2 hb
    simp [hb1]
  push Not at ha2 hb2
  -- log(a*b) = log a + log b
  have hlog_mul : Real.log ((a : ℝ) * (b : ℝ)) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
    apply Real.log_mul
    · exact Nat.cast_ne_zero.mpr (by omega : a ≠ 0)
    · exact Nat.cast_ne_zero.mpr (by omega : b ≠ 0)
  rw [hlog_mul]
  -- √(x + y) ≤ √x + √y for x, y ≥ 0 (this follows from squaring both sides)
  have hlog_a_nonneg : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by norm_cast)
  have hlog_b_nonneg : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by norm_cast)
  -- Use √(x + y) ≤ √x + √y which holds when x, y ≥ 0
  -- Proof: √(x + y)² = x + y ≤ x + 2√(xy) + y = (√x + √y)²
  have key : Real.log (a : ℝ) + Real.log (b : ℝ) ≤
      (Real.sqrt (Real.log a) + Real.sqrt (Real.log b))^2 := by
    have hsq_a : Real.sqrt (Real.log (a : ℝ))^2 = Real.log (a : ℝ) := Real.sq_sqrt hlog_a_nonneg
    have hsq_b : Real.sqrt (Real.log (b : ℝ))^2 = Real.log (b : ℝ) := Real.sq_sqrt hlog_b_nonneg
    have hsq : (Real.sqrt (Real.log (a : ℝ)) + Real.sqrt (Real.log (b : ℝ)))^2 =
        Real.log (a : ℝ) + 2 * Real.sqrt (Real.log (a : ℝ)) * Real.sqrt (Real.log (b : ℝ)) + Real.log (b : ℝ) := by
      ring_nf
      rw [hsq_a, hsq_b]
    rw [hsq]
    have h_cross_nonneg : 0 ≤ 2 * Real.sqrt (Real.log (a : ℝ)) * Real.sqrt (Real.log (b : ℝ)) := by positivity
    linarith
  calc Real.sqrt (Real.log (a : ℝ) + Real.log (b : ℝ))
    _ ≤ Real.sqrt ((Real.sqrt (Real.log a) + Real.sqrt (Real.log b))^2) := Real.sqrt_le_sqrt key
    _ = |Real.sqrt (Real.log a) + Real.sqrt (Real.log b)| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt (Real.log a) + Real.sqrt (Real.log b) := abs_of_nonneg (by positivity)

/-- Each f(j) for j ∈ [1, K+1] appears at most twice when summing f(k+1) + f(k+2). -/
lemma sum_shifted_le_two_sum {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (K : ℕ) :
    ∑ k ∈ Finset.range K, (f (k + 1) + f (k + 2)) ≤
    2 * ∑ k ∈ Finset.range (K + 2), f k := by
  -- Split the sum: Σ (f(k+1) + f(k+2)) = Σ f(k+1) + Σ f(k+2)
  have hsplit : ∑ k ∈ Finset.range K, (f (k + 1) + f (k + 2)) =
      ∑ k ∈ Finset.range K, f (k + 1) + ∑ k ∈ Finset.range K, f (k + 2) :=
    Finset.sum_add_distrib
  rw [hsplit]
  -- Each shifted sum is a subset of the full range [0, K+2)
  have h1 : ∑ k ∈ Finset.range K, f (k + 1) ≤ ∑ k ∈ Finset.range (K + 2), f k := by
    -- Σ_{k<K} f(k+1) sums over f(1), f(2), ..., f(K)
    -- which is a subset of f(0), f(1), ..., f(K+1) = range (K+2)
    -- Reindex: the shifted range maps to {1, ..., K} ⊆ {0, ..., K+1}
    set s : Finset ℕ := Finset.map ⟨(· + 1), add_left_injective 1⟩ (Finset.range K) with hs_def
    have hbij : ∑ k ∈ Finset.range K, f (k + 1) = ∑ j ∈ s, f j := by
      rw [hs_def, Finset.sum_map]; rfl
    rw [hbij]
    have hsub : s ⊆ Finset.range (K + 2) := by
      intro x hx
      rw [hs_def] at hx
      simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [Finset.mem_range]; omega
    -- sum over subset ≤ sum over superset when extra terms are nonnegative
    have hdiff : ∑ j ∈ s, f j = ∑ j ∈ Finset.range (K + 2), f j -
        ∑ j ∈ (Finset.range (K + 2) \ s), f j := by
      rw [← Finset.sum_sdiff hsub]; ring
    rw [hdiff]
    have hnn : 0 ≤ ∑ j ∈ (Finset.range (K + 2) \ s), f j := Finset.sum_nonneg (fun i _ => hf i)
    linarith
  have h2 : ∑ k ∈ Finset.range K, f (k + 2) ≤ ∑ k ∈ Finset.range (K + 2), f k := by
    -- Σ_{k<K} f(k+2) sums over f(2), f(3), ..., f(K+1)
    -- which is a subset of f(0), f(1), ..., f(K+1) = range (K+2)
    set s : Finset ℕ := Finset.map ⟨(· + 2), add_left_injective 2⟩ (Finset.range K) with hs_def
    have hbij : ∑ k ∈ Finset.range K, f (k + 2) = ∑ j ∈ s, f j := by
      rw [hs_def, Finset.sum_map]; rfl
    rw [hbij]
    have hsub : s ⊆ Finset.range (K + 2) := by
      intro x hx
      rw [hs_def] at hx
      simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [Finset.mem_range]; omega
    have hdiff : ∑ j ∈ s, f j = ∑ j ∈ Finset.range (K + 2), f j -
        ∑ j ∈ (Finset.range (K + 2) \ s), f j := by
      rw [← Finset.sum_sdiff hsub]; ring
    rw [hdiff]
    have hnn : 0 ≤ ∑ j ∈ (Finset.range (K + 2) \ s), f j := Finset.sum_nonneg (fun i _ => hf i)
    linarith
  calc ∑ k ∈ Finset.range K, f (k + 1) + ∑ k ∈ Finset.range K, f (k + 2)
    _ ≤ ∑ k ∈ Finset.range (K + 2), f k + ∑ k ∈ Finset.range (K + 2), f k := add_le_add h1 h2
    _ = 2 * ∑ k ∈ Finset.range (K + 2), f k := by ring

/-!
## ENNReal Metric Entropy and Dudley Integrand
-/

/-- Metric entropy as ENNReal: max(0, log N(ε, s)).
    This is the non-negative part of the logarithm of the covering number. -/
def metricEntropyENNReal (eps : ℝ) (s : Set A) : ℝ≥0∞ :=
  ENNReal.ofReal (metricEntropy eps s)

/-- Dudley integrand: √(log N(ε, s)), as ENNReal.
    This is the integrand for Dudley's entropy integral. -/
def dudleyIntegrand (eps : ℝ) (s : Set A) : ℝ≥0∞ :=
  ENNReal.ofReal (sqrtEntropy eps s)

lemma dudleyIntegrand_eq_sqrt_metricEntropyENNReal (eps : ℝ) (s : Set A) :
    dudleyIntegrand eps s = ENNReal.ofReal (Real.sqrt (metricEntropy eps s)) := rfl

/-!
## Entropy Integral (ENNReal - Canonical)
-/

/-- Dudley's entropy integral as ENNReal:
    ∫_{(0,D]} √(log N(ε, s)) dε.
    This is the canonical definition; the real version is obtained via `.toReal`. -/
def entropyIntegralENNReal (s : Set A) (D : ℝ) : ℝ≥0∞ :=
  ∫⁻ eps in Set.Ioc (0 : ℝ) D, dudleyIntegrand eps s

/-- Entropy integral ENNReal is monotone in D. -/
lemma entropyIntegralENNReal_mono_D {s : Set A} {D₁ D₂ : ℝ}
    (hD : D₁ ≤ D₂) :
    entropyIntegralENNReal s D₁ ≤ entropyIntegralENNReal s D₂ := by
  unfold entropyIntegralENNReal
  apply lintegral_mono'
  · apply Measure.restrict_mono
    · intro x hx
      exact ⟨hx.1, le_trans hx.2 hD⟩
    · exact le_rfl
  · exact fun _ => le_rfl

/-!
## Entropy Integral (Real-valued - User-facing)

The real-valued entropy integral is the `.toReal` of the ENNReal version.
It requires a finiteness assumption to be meaningful.
-/

/-- Real-valued entropy integral, obtained from the extended integral via `toReal`.
    It is only meaningful (and useful) when `entropyIntegralENNReal s D < ∞`. -/
def entropyIntegral (s : Set A) (D : ℝ) : ℝ :=
  (entropyIntegralENNReal s D).toReal

/-- Entropy integral is non-negative. -/
lemma entropyIntegral_nonneg {s : Set A} {D : ℝ} :
    0 ≤ entropyIntegral s D :=
  ENNReal.toReal_nonneg

/-- Entropy integral is monotone in D (with finiteness assumptions). -/
lemma entropyIntegral_mono_D {s : Set A} {D₁ D₂ : ℝ}
    (hD : D₁ ≤ D₂)
    (hfinite₂ : entropyIntegralENNReal s D₂ ≠ ⊤) :
    entropyIntegral s D₁ ≤ entropyIntegral s D₂ := by
  unfold entropyIntegral
  have hfinite₁ : entropyIntegralENNReal s D₁ ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite₂ (entropyIntegralENNReal_mono_D hD)
  rw [ENNReal.toReal_le_toReal hfinite₁ hfinite₂]
  exact entropyIntegralENNReal_mono_D hD

/-- Entropy integral is monotone in D for totally bounded sets (with finiteness). -/
lemma entropyIntegral_mono_D_of_totallyBounded {s : Set A} {D₁ D₂ : ℝ}
    (hD : D₁ ≤ D₂)
    (hfinite₂ : entropyIntegralENNReal s D₂ ≠ ⊤) :
    entropyIntegral s D₁ ≤ entropyIntegral s D₂ :=
  entropyIntegral_mono_D hD hfinite₂

/-!
## Integrability and Real-ENNReal Connection

For totally bounded sets, sqrtEntropy is integrable on [a, b] with a > 0.
-/

/-!
## Dyadic Sum Approximation

For the chaining proof, we relate the entropy integral to a dyadic sum.
-/

/-- Set lintegral over an interval is bounded by length times sup. -/
lemma setLIntegral_Ioc_le_length_mul_sup {f : ℝ → ℝ≥0∞} {a b : ℝ} {M : ℝ≥0∞}
    (hf : ∀ x ∈ Set.Ioc a b, f x ≤ M) :
    ∫⁻ x in Set.Ioc a b, f x ≤ ENNReal.ofReal (b - a) * M := by
  calc ∫⁻ x in Set.Ioc a b, f x
      ≤ ∫⁻ x in Set.Ioc a b, M := setLIntegral_mono' measurableSet_Ioc hf
    _ = M * volume (Set.Ioc a b) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ = M * ENNReal.ofReal (b - a) := by congr 1; rw [Real.volume_Ioc]
    _ = ENNReal.ofReal (b - a) * M := mul_comm _ _

/-!
## Truncated Entropy Integral

For the dyadic bound, we use truncated integrals over (δ, D] where δ > 0.
This avoids the potential divergence at 0 and is always finite.
-/

/-- Truncated Dudley entropy integral over (δ, D].
    Always finite when δ > 0 because `dudleyIntegrand` is bounded on [δ, D]. -/
def entropyIntegralENNRealTrunc (s : Set A) (δ D : ℝ) : ℝ≥0∞ :=
  ∫⁻ eps in Set.Ioc δ D, dudleyIntegrand eps s

/-- ENNReal dyadic RHS used in the dyadic bound for entropy integral. -/
def dyadicRHS_ENNReal (s : Set A) (D : ℝ) (K : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal D *
    ∑ k ∈ Finset.range K,
      ENNReal.ofReal ((2 : ℝ)^(-((k : ℤ) + 1))) *
        dudleyIntegrand (D * (2 : ℝ)^(-((k : ℤ) + 1))) s
  + ENNReal.ofReal (D * (2 : ℝ)^(-(K : ℤ))) *
      dudleyIntegrand (D * (2 : ℝ)^(-(K : ℤ))) s

/-- Public dyadic RHS for ENNReal inequality, total in `K`.
    For `K = 0`, we return `⊤` (trivial bound). For `K ≥ 1`, we use the concrete dyadic RHS. -/
def dyadicRHS_ENNReal_total (s : Set A) (D : ℝ) (K : ℕ) : ℝ≥0∞ :=
  if K = 0 then ⊤ else dyadicRHS_ENNReal s D K

/-- Real-valued dyadic RHS used in the real dyadic bound, valid for `K ≥ 1`. -/
def dyadicRHS_real (s : Set A) (D : ℝ) (K : ℕ) : ℝ :=
  D * ∑ k ∈ Finset.range K,
    (2 : ℝ)^(-((k : ℤ) + 1)) *
      sqrtEntropy (D * (2 : ℝ)^(-((k : ℤ) + 1))) s
  + D * (2 : ℝ)^(-(K : ℤ)) *
      sqrtEntropy (D * (2 : ℝ)^(-(K : ℤ))) s

/-- The dyadic RHS is non-negative when D > 0. -/
lemma dyadicRHS_real_nonneg {s : Set A} {D : ℝ} (hD : 0 < D) (K : ℕ) :
    0 ≤ dyadicRHS_real s D K := by
  unfold dyadicRHS_real
  apply add_nonneg
  · apply mul_nonneg (le_of_lt hD)
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) (sqrtEntropy_nonneg _ _)
  · apply mul_nonneg
    · apply mul_nonneg (le_of_lt hD) (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    · exact sqrtEntropy_nonneg _ _

/-- The ENNReal and real dyadic RHS are related by toReal when the ENNReal version is finite. -/
lemma dyadicRHS_ENNReal_toReal {s : Set A} {D : ℝ} {K : ℕ}
    (hD : 0 < D) :
    (dyadicRHS_ENNReal s D K).toReal = dyadicRHS_real s D K := by
  unfold dyadicRHS_ENNReal dyadicRHS_real dudleyIntegrand
  -- All terms are finite ENNReal.ofReal values, so we can convert to real.
  -- The key lemmas are ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_sum.
  have h_sum_finite : ENNReal.ofReal D *
      ∑ k ∈ Finset.range K, ENNReal.ofReal (2 ^ (-((k : ℤ) + 1))) *
        ENNReal.ofReal (sqrtEntropy (D * 2 ^ (-((k : ℤ) + 1))) s) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ne_top_of_lt
    rw [ENNReal.sum_lt_top]
    intro k _
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have h_tail_finite : ENNReal.ofReal (D * 2 ^ (-(K : ℤ))) *
      ENNReal.ofReal (sqrtEntropy (D * 2 ^ (-(K : ℤ))) s) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_add h_sum_finite h_tail_finite]
  congr 1
  · -- Sum part
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hD)]
    congr 1
    have h_terms_finite : ∀ k ∈ Finset.range K,
        ENNReal.ofReal (2 ^ (-((k : ℤ) + 1))) *
          ENNReal.ofReal (sqrtEntropy (D * 2 ^ (-((k : ℤ) + 1))) s) ≠ ⊤ := fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_sum h_terms_finite]
    apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 : ℝ) ^ (-((k : ℤ) + 1))),
        ENNReal.toReal_ofReal (sqrtEntropy_nonneg _ _)]
  · -- Tail part
    rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ D * 2 ^ (-(K : ℤ))),
        ENNReal.toReal_ofReal (sqrtEntropy_nonneg _ _)]

/-- Splitting lemma for truncated integrals: (δ, D] = (δ, c] ∪ (c, D] when δ ≤ c ≤ D. -/
lemma entropyIntegralENNRealTrunc_split {s : Set A} {δ c D : ℝ}
    (hδc : δ ≤ c) (hcD : c ≤ D) :
    entropyIntegralENNRealTrunc s δ D =
      entropyIntegralENNRealTrunc s δ c + entropyIntegralENNRealTrunc s c D := by
  unfold entropyIntegralENNRealTrunc
  have h_union : Set.Ioc δ D = Set.Ioc δ c ∪ Set.Ioc c D := (Set.Ioc_union_Ioc_eq_Ioc hδc hcD).symm
  have h_disj : Disjoint (Set.Ioc δ c) (Set.Ioc c D) := Set.Ioc_disjoint_Ioc_of_le le_rfl
  rw [h_union]
  rw [lintegral_union measurableSet_Ioc h_disj]

/-- Dyadic bound consistency: dyadicRHS(D/2, K) + (D/2)·f(D/2) = dyadicRHS(D, K+1). -/
lemma dyadicRHS_ENNReal_half_step {s : Set A} {D : ℝ} {K : ℕ}
    (hD : 0 < D) :
    dyadicRHS_ENNReal s (D / 2) K + ENNReal.ofReal (D / 2) * dudleyIntegrand (D / 2) s ≤
    dyadicRHS_ENNReal s D (K + 1) := by
  -- Key: (D/2) * 2^{-(k+1)} = D * 2^{-(k+2)} allows reindexing
  apply le_of_eq
  unfold dyadicRHS_ENNReal

  have h2ne : (2 : ℝ) ≠ 0 := by norm_num

  have h_half_tail : (D / 2) * (2 : ℝ) ^ (-(K : ℤ)) = D * (2 : ℝ) ^ (-((K : ℤ) + 1)) := by
    rw [show -((K : ℤ) + 1) = -(K : ℤ) + (-1) by ring]
    rw [zpow_add₀ h2ne, zpow_neg_one]
    ring

  -- Split RHS sum: range (K+1) = {0} ∪ {1, ..., K}
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero]

  -- Rewrite LHS tail and extra terms
  have h_tail_eq : ENNReal.ofReal ((D / 2) * (2 : ℝ) ^ (-(K : ℤ))) *
      dudleyIntegrand ((D / 2) * (2 : ℝ) ^ (-(K : ℤ))) s =
      ENNReal.ofReal (D * (2 : ℝ) ^ (-((K : ℤ) + 1))) *
      dudleyIntegrand (D * (2 : ℝ) ^ (-((K : ℤ) + 1))) s := by
    rw [h_half_tail]

  have h_extra_eq : ENNReal.ofReal (D / 2) * dudleyIntegrand (D / 2) s =
      ENNReal.ofReal D * (ENNReal.ofReal ((2 : ℝ) ^ (-(1 : ℤ))) *
        dudleyIntegrand (D * (2 : ℝ) ^ (-(1 : ℤ))) s) := by
    rw [zpow_neg_one]
    have hD2 : D / 2 = D * 2⁻¹ := by ring
    rw [hD2]
    rw [ENNReal.ofReal_mul (le_of_lt hD)]
    ring

  -- Rewrite LHS sum via (D/2) * 2^{-(k+1)} = D * 2^{-(k+2)}
  have h_sum_transform :
      ENNReal.ofReal (D / 2) * ∑ k ∈ Finset.range K,
        ENNReal.ofReal ((2 : ℝ) ^ (-((k : ℤ) + 1))) *
          dudleyIntegrand ((D / 2) * (2 : ℝ) ^ (-((k : ℤ) + 1))) s =
      ENNReal.ofReal D * ∑ k ∈ Finset.range K,
        ENNReal.ofReal ((2 : ℝ) ^ (-(((k : ℤ) + 1) + 1))) *
          dudleyIntegrand (D * (2 : ℝ) ^ (-(((k : ℤ) + 1) + 1))) s := by
    -- Factor out D/2 = D * 2^{-1}
    have hD2 : D / 2 = D * 2⁻¹ := by ring
    rw [hD2, ENNReal.ofReal_mul (le_of_lt hD)]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    -- Key identities
    have harg_eq : D * 2⁻¹ * (2 : ℝ) ^ (-((k : ℤ) + 1)) = D * (2 : ℝ) ^ (-((k : ℤ) + 1 + 1)) := by
      have h1 : -((k : ℤ) + 1 + 1) = -((k : ℤ) + 1) + (-1) := by ring
      rw [h1, zpow_add₀ h2ne, zpow_neg_one]
      ring
    have hcoef_eq : (2 : ℝ)⁻¹ * (2 : ℝ) ^ (-((k : ℤ) + 1)) = (2 : ℝ) ^ (-((k : ℤ) + 1 + 1)) := by
      have h1 : -((k : ℤ) + 1 + 1) = -((k : ℤ) + 1) + (-1) := by ring
      rw [h1, zpow_add₀ h2ne, zpow_neg_one, mul_comm]
    -- Transform via algebraic identities
    rw [harg_eq]
    rw [mul_assoc (ENNReal.ofReal D) (ENNReal.ofReal 2⁻¹) _]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), hcoef_eq]

  -- Now combine everything
  rw [h_sum_transform, h_tail_eq, h_extra_eq]

  -- Rearrange terms using associativity and commutativity
  rw [mul_add, add_assoc, add_assoc]
  congr 1
  rw [add_comm]
  simp only [zero_add, Int.reduceNeg, Nat.cast_add, Nat.cast_one]

/-- Real-valued truncated entropy integral over (δ, D]. -/
def entropyIntegralTrunc (s : Set A) (δ D : ℝ) : ℝ :=
  (entropyIntegralENNRealTrunc s δ D).toReal

/-!
## Real-Valued Entropy Integral Identification

Under finiteness, the ENNReal entropy integral equals a real Lebesgue integral.
-/

/-- The truncated ENNReal entropy integral is monotone in K (larger K means smaller δ_K). -/
lemma entropyIntegralENNRealTrunc_mono_K
    {s : Set A} {D : ℝ} (hD : 0 < D) :
    Monotone (fun K : ℕ => entropyIntegralENNRealTrunc s (D * 2^(-(K:ℤ))) D) := by
  intro K₁ K₂ hK
  unfold entropyIntegralENNRealTrunc
  apply lintegral_mono'
  · apply Measure.restrict_mono
    · -- Ioc δ_{K₁} D ⊆ Ioc δ_{K₂} D when K₁ ≤ K₂ (δ_{K₂} ≤ δ_{K₁})
      intro x hx
      constructor
      · -- δ_{K₂} < x
        calc D * 2 ^ (-(K₂ : ℤ)) ≤ D * 2 ^ (-(K₁ : ℤ)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hD)
              apply zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2:ℝ))
              simp only [neg_le_neg_iff, Int.ofNat_le]
              exact hK
          _ < x := hx.1
      · exact hx.2
    · exact le_rfl
  · exact fun _ => le_rfl

/-- The truncated ENNReal entropy integral is bounded by the full integral. -/
lemma entropyIntegralENNRealTrunc_le
    {s : Set A} {D : ℝ} (hD : 0 < D) (K : ℕ) :
    entropyIntegralENNRealTrunc s (D * 2^(-(K:ℤ))) D ≤ entropyIntegralENNReal s D := by
  unfold entropyIntegralENNRealTrunc entropyIntegralENNReal
  apply lintegral_mono'
  · apply Measure.restrict_mono
    · intro x hx
      exact ⟨lt_of_le_of_lt (by positivity) hx.1, hx.2⟩
    · exact le_rfl
  · exact fun _ => le_rfl

/-- The supremum of truncated ENNReal entropy integrals equals the full integral.
    This follows from the fact that ⋃_K Ioc(δ_K, D] = Ioc(0, D] as K → ∞. -/
lemma iSup_entropyIntegralENNRealTrunc_eq
    {s : Set A} {D : ℝ} (hD : 0 < D) :
    ⨆ K : ℕ, entropyIntegralENNRealTrunc s (D * 2^(-(K:ℤ))) D = entropyIntegralENNReal s D := by
  unfold entropyIntegralENNRealTrunc entropyIntegralENNReal
  apply le_antisymm
  · -- ⨆ K, ∫⁻ on Ioc(δ_K, D] ≤ ∫⁻ on Ioc(0, D]
    apply iSup_le
    intro K
    apply lintegral_mono'
    · apply Measure.restrict_mono
      · intro x hx
        exact ⟨lt_of_le_of_lt (by positivity) hx.1, hx.2⟩
      · exact le_rfl
    · exact fun _ => le_rfl
  · -- Monotone convergence: Ioc(D*2^{-K}, D] increasing with union Ioc(0, D]
    -- δ_K = D * 2^{-K} is decreasing
    have h_delta_anti : StrictAnti (fun K : ℕ => D * (2 : ℝ)^(-(K:ℤ))) := by
      intro K L hKL
      apply mul_lt_mul_of_pos_left _ hD
      -- Need: 2^{-L} < 2^{-K}
      simp only [zpow_neg, zpow_natCast]
      rw [inv_eq_one_div, inv_eq_one_div]
      apply one_div_lt_one_div_of_lt (by positivity)
      have h_nat : (2 : ℕ) ^ K < (2 : ℕ) ^ L := Nat.pow_lt_pow_right (by norm_num) hKL
      exact_mod_cast h_nat

    -- The sets Ioc(D * 2^{-K}, D) are increasing (directed by monotone)
    have h_sets_mono : Monotone (fun K : ℕ => Set.Ioc (D * 2^(-(K:ℤ))) D) := by
      intro K L hKL
      apply Set.Ioc_subset_Ioc_left
      rcases eq_or_lt_of_le hKL with rfl | hKL
      · exact le_refl _
      · exact le_of_lt (h_delta_anti hKL)

    -- The union of Ioc(D * 2^{-K}, D) equals Ioc(0, D)
    have h_union : ⋃ K : ℕ, Set.Ioc (D * 2^(-(K:ℤ))) D = Set.Ioc 0 D := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_iUnion, Set.mem_Ioc] at hx
        obtain ⟨K, hK⟩ := hx
        exact ⟨lt_of_le_of_lt (by positivity) hK.1, hK.2⟩
      · intro hx
        simp only [Set.mem_iUnion, Set.mem_Ioc] at *
        have h_tends : Filter.Tendsto (fun K : ℕ => D * 2^(-(K:ℤ))) Filter.atTop (nhds 0) := by
          have h1 : Filter.Tendsto (fun K : ℕ => (2 : ℝ)^(-(K:ℤ))) Filter.atTop (nhds 0) := by
            simp only [zpow_neg, zpow_natCast]
            -- (2^K)⁻¹ = (1/2)^K
            have h_eq : ∀ K : ℕ, ((2 : ℝ) ^ K)⁻¹ = (1/2 : ℝ) ^ K := by
              intro K
              rw [one_div, inv_pow]
            simp only [h_eq]
            exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
              (by norm_num : (1 : ℝ) / 2 < 1)
          convert Filter.Tendsto.const_mul D h1 using 1
          simp only [mul_zero]
        -- Find K such that D * 2^{-K} < x
        have h_ev := (Metric.tendsto_atTop.mp h_tends (x / 2) (by linarith))
        obtain ⟨K, hK⟩ := h_ev
        use K
        specialize hK K (le_refl K)
        simp only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : 0 ≤ D * 2^(-(K:ℤ)))] at hK
        constructor
        · linarith
        · exact hx.2

    -- Apply setLIntegral_iUnion_of_directed
    rw [← h_union]
    have h_directed : Directed (· ⊆ ·) (fun K : ℕ => Set.Ioc (D * 2^(-(K:ℤ))) D) :=
      h_sets_mono.directed_le
    rw [MeasureTheory.setLIntegral_iUnion_of_directed (dudleyIntegrand · s) h_directed]

/-- Truncated entropy integral converges to full entropy integral as K → ∞. -/
lemma entropyIntegralTrunc_tendsto_entropyIntegral
    {s : Set A} {D : ℝ}
    (hD : 0 < D)
    (hfinite : entropyIntegralENNReal s D ≠ ⊤) :
    Filter.Tendsto (fun K : ℕ => entropyIntegralTrunc s (D * 2^(-(K:ℤ))) D)
      Filter.atTop (nhds (entropyIntegral s D)) := by
  unfold entropyIntegralTrunc entropyIntegral
  have h_ennreal_mono : Monotone (fun K : ℕ => entropyIntegralENNRealTrunc s (D * 2^(-(K:ℤ))) D) :=
    entropyIntegralENNRealTrunc_mono_K hD
  have h_tendsto_ennreal : Filter.Tendsto
      (fun K : ℕ => entropyIntegralENNRealTrunc s (D * 2^(-(K:ℤ))) D)
      Filter.atTop (nhds (entropyIntegralENNReal s D)) := by
    rw [← iSup_entropyIntegralENNRealTrunc_eq hD]
    exact tendsto_atTop_iSup h_ennreal_mono
  -- Each truncated integral is bounded by the full integral, hence finite
  have h_trunc_finite : ∀ K : ℕ, entropyIntegralENNRealTrunc s (D * 2^(-(K:ℤ))) D ≠ ⊤ := by
    intro K
    exact ne_top_of_le_ne_top hfinite (entropyIntegralENNRealTrunc_le hD K)
  rw [ENNReal.tendsto_toReal_iff h_trunc_finite hfinite]
  exact h_tendsto_ennreal

/-!
## Key Upstream Lemmas for Dudley's Theorem
-/

/-- Truncated entropy integral ≤ full entropy integral (real-valued). -/
lemma entropyIntegralTrunc_le_entropyIntegral
    {s : Set A} {D : ℝ} (hD : 0 < D) (K : ℕ)
    (hfinite : entropyIntegralENNReal s D ≠ ⊤) :
    entropyIntegralTrunc s (D * 2^(-(K:ℤ))) D ≤ entropyIntegral s D := by
  unfold entropyIntegralTrunc entropyIntegral
  apply ENNReal.toReal_mono hfinite
  exact entropyIntegralENNRealTrunc_le hD K

end
