/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Tengoku.Leanslt.SLT.LeastSquares.LinearRegression.LocalizedBall

/-!
# Euclidean Covering Number Reduction

This file establishes the equivalence between covering numbers in empirical norm
and Euclidean norm, enabling dimension reduction from n to d.

## Main Definitions

* `empiricalToEuclidean`: The identity map from EmpiricalSpace to EuclideanSpace
* `euclideanToEmpirical`: The inverse map
* `designMatrixRange`: The range of the design matrix as a set
* `euclideanBallOrigin`: The Euclidean ball of radius r centered at origin
* `euclideanLocalizedBall`: The localized ball in Euclidean space
* `designMatrixRangeSubmodule`: The design matrix range as a submodule

## Main Results

* `dist_euclidean_eq_sqrt_n_mul_dist_empirical`: Distance scaling relation
* `linearCoveringNumber_eq_euclidean`: Covering number equivalence
* `linearCoveringNumber_le_euclideanBall_d`: Dimension reduction bound

-/

open MeasureTheory Finset BigOperators Real ProbabilityTheory Metric Set
open scoped NNReal ENNReal

namespace LeastSquares

variable {n d : ℕ}

/-! ## Euclidean Covering Number Equivalence

Convert covering in empirical norm ‖·‖_n to Euclidean norm ‖·‖_2:
N(s, B_n(δ), ‖·‖_n) = N(s√n, B_2^n(δ√n) ∩ range(X), ‖·‖_2)
-/

/-- The identity map from EmpiricalSpace n to EuclideanSpace ℝ (Fin n).
    This preserves values but changes the metric: dist in EmpiricalSpace = (1/√n) * dist in EuclideanSpace -/
def empiricalToEuclidean (n : ℕ) (v : EmpiricalSpace n) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm v

/-- The inverse map from EuclideanSpace to EmpiricalSpace -/
def euclideanToEmpirical (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : EmpiricalSpace n :=
  WithLp.equiv 2 (Fin n → ℝ) v

@[simp]
lemma euclideanToEmpirical_empiricalToEuclidean (v : EmpiricalSpace n) :
    euclideanToEmpirical n (empiricalToEuclidean n v) = v := by
  simp [euclideanToEmpirical, empiricalToEuclidean]

@[simp]
lemma empiricalToEuclidean_euclideanToEmpirical (v : EuclideanSpace ℝ (Fin n)) :
    empiricalToEuclidean n (euclideanToEmpirical n v) = v := by
  simp [euclideanToEmpirical, empiricalToEuclidean]

lemma empiricalToEuclidean_apply (v : EmpiricalSpace n) (i : Fin n) :
    empiricalToEuclidean n v i = v i := rfl

lemma euclideanToEmpirical_apply (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanToEmpirical n v i = v i := rfl

/-- Distance in EuclideanSpace equals √n times distance in EmpiricalSpace -/
theorem dist_euclidean_eq_sqrt_n_mul_dist_empirical (hn : 0 < n)
    (v₁ v₂ : EmpiricalSpace n) :
    dist (empiricalToEuclidean n v₁) (empiricalToEuclidean n v₂) =
    Real.sqrt n * dist v₁ v₂ := by
  -- Distance in EmpiricalSpace is empiricalNorm (v₁ - v₂)
  show ‖empiricalToEuclidean n v₁ - empiricalToEuclidean n v₂‖ =
       Real.sqrt n * empiricalNorm n (v₁ - v₂)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_nonneg : (0 : ℝ) ≤ n := le_of_lt hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- LHS: √(Σᵢ (v₁ i - v₂ i)²), RHS: √n * √(n⁻¹ * Σᵢ (v₁ i - v₂ i)²)
  rw [EuclideanSpace.norm_eq]
  unfold empiricalNorm
  -- The sums are the same
  have hsum_eq : ∑ i : Fin n, ‖(empiricalToEuclidean n v₁ - empiricalToEuclidean n v₂) i‖ ^ 2 =
      ∑ i : Fin n, ((v₁ - v₂) i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h1 : (empiricalToEuclidean n v₁ - empiricalToEuclidean n v₂) i = v₁ i - v₂ i := rfl
    have h2 : (v₁ - v₂) i = v₁ i - v₂ i := rfl
    rw [h1, h2, Real.norm_eq_abs, sq_abs]
  rw [hsum_eq]
  -- √(S) = √n * √(n⁻¹ * S) when n > 0
  set S := ∑ i : Fin n, ((v₁ - v₂) i) ^ 2
  calc Real.sqrt S = Real.sqrt (n * ((n : ℝ)⁻¹ * S)) := by rw [mul_inv_cancel_left₀ hn_ne S]
    _ = Real.sqrt n * Real.sqrt ((n : ℝ)⁻¹ * S) := Real.sqrt_mul hn_nonneg _

/-- Norm in EuclideanSpace equals √n times empirical norm -/
theorem norm_euclidean_eq_sqrt_n_mul_empiricalNorm (hn : 0 < n) (v : EmpiricalSpace n) :
    ‖empiricalToEuclidean n v‖ = Real.sqrt n * empiricalNorm n v := by
  have h := dist_euclidean_eq_sqrt_n_mul_dist_empirical hn v 0
  have hzero : empiricalToEuclidean n (0 : EmpiricalSpace n) = 0 := by
    ext i
    rfl
  rw [dist_eq_norm, hzero, sub_zero] at h
  convert h using 2
  · show empiricalNorm n v = empiricalNorm n (v - (0 : EmpiricalSpace n))
    congr 1
    ext i
    exact (sub_zero (v i)).symm

/-- The range of the design matrix as a set in EuclideanSpace -/
def designMatrixRange (n d : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Set.range (designMatrixMul x)

/-- The Euclidean ball of radius r centered at origin -/
def euclideanBallOrigin (n : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 r

/-- The localized ball in Euclidean space: B_2^n(δ√n) ∩ range(X) -/
def euclideanLocalizedBall (n d : ℕ) (δ : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  euclideanBallOrigin n (δ * Real.sqrt n) ∩ designMatrixRange n d x

/-- Membership in Euclidean localized ball via parameter θ -/
theorem mem_euclideanLocalizedBall_iff (_hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (δ : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ euclideanLocalizedBall n d δ x ↔
    ∃ θ : EuclideanSpace ℝ (Fin d), v = designMatrixMul x θ ∧ ‖v‖ ≤ δ * Real.sqrt n := by
  unfold euclideanLocalizedBall euclideanBallOrigin designMatrixRange
  simp only [Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, Set.mem_range]
  constructor
  · rintro ⟨hball, θ, rfl⟩
    exact ⟨θ, rfl, hball⟩
  · rintro ⟨θ, rfl, hball⟩
    exact ⟨hball, θ, rfl⟩

/-- The empirical image maps to the Euclidean localized ball under the scaling.
    More precisely: empiricalToEuclidean '' linearLocalizedBallImage = euclideanLocalizedBall -/
theorem empiricalToEuclidean_image_eq (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    empiricalToEuclidean n '' linearLocalizedBallImage n d δ x =
    euclideanLocalizedBall n d δ x := by
  ext v
  rw [Set.mem_image, mem_euclideanLocalizedBall_iff hn x δ v]
  constructor
  · -- Forward: v ∈ image → v ∈ euclideanLocalizedBall
    rintro ⟨w, hw, rfl⟩
    rw [linearLocalizedBallImage_eq hn x δ] at hw
    obtain ⟨θ, hθ_norm, rfl⟩ := hw
    use θ
    constructor
    · -- empiricalToEuclidean (fun i => ⟨θ, x i⟩) = designMatrixMul x θ
      ext i
      simp only [empiricalToEuclidean_apply, designMatrixMul_apply]
      first
        | (all_goals grind; done; trace "PORTFOLIO-OK grind")
        | (all_goals simp_all; done; trace "PORTFOLIO-OK simp_all")
        | (all_goals aesop; done; trace "PORTFOLIO-OK aesop")
        | (all_goals omega; done; trace "PORTFOLIO-OK omega")
        | (all_goals norm_num; done; trace "PORTFOLIO-OK norm_num")
        | (all_goals positivity; done; trace "PORTFOLIO-OK positivity")
        | (all_goals linarith; done; trace "PORTFOLIO-OK linarith")
        | (all_goals decide; done; trace "PORTFOLIO-OK decide")
        | (all_goals tauto; done; trace "PORTFOLIO-OK tauto")
    · -- ‖designMatrixMul x θ‖ ≤ δ * √n
      have heq : empiricalToEuclidean n (fun i => @inner ℝ _ _ θ (x i)) = designMatrixMul x θ := by
        ext i
        simp only [empiricalToEuclidean_apply, designMatrixMul_apply]
        first
          | (all_goals grind; done; trace "PORTFOLIO-OK grind")
          | (all_goals simp_all; done; trace "PORTFOLIO-OK simp_all")
          | (all_goals aesop; done; trace "PORTFOLIO-OK aesop")
          | (all_goals omega; done; trace "PORTFOLIO-OK omega")
          | (all_goals norm_num; done; trace "PORTFOLIO-OK norm_num")
          | (all_goals positivity; done; trace "PORTFOLIO-OK positivity")
          | (all_goals linarith; done; trace "PORTFOLIO-OK linarith")
          | (all_goals decide; done; trace "PORTFOLIO-OK decide")
          | (all_goals tauto; done; trace "PORTFOLIO-OK tauto")
      rw [heq]
      exact hθ_norm
  · -- Backward: v ∈ euclideanLocalizedBall → v ∈ image
    rintro ⟨θ, rfl, hball⟩
    use fun i => @inner ℝ _ _ θ (x i)
    constructor
    · rw [linearLocalizedBallImage_eq hn x δ]
      exact ⟨θ, hball, rfl⟩
    · ext i
      simp only [empiricalToEuclidean_apply, designMatrixMul_apply]
      first
        | (all_goals grind; done; trace "PORTFOLIO-OK grind")
        | (all_goals simp_all; done; trace "PORTFOLIO-OK simp_all")
        | (all_goals aesop; done; trace "PORTFOLIO-OK aesop")
        | (all_goals omega; done; trace "PORTFOLIO-OK omega")
        | (all_goals norm_num; done; trace "PORTFOLIO-OK norm_num")
        | (all_goals positivity; done; trace "PORTFOLIO-OK positivity")
        | (all_goals linarith; done; trace "PORTFOLIO-OK linarith")
        | (all_goals decide; done; trace "PORTFOLIO-OK decide")
        | (all_goals tauto; done; trace "PORTFOLIO-OK tauto")

/-- empiricalToEuclidean is a bijection from EmpiricalSpace to EuclideanSpace -/
lemma empiricalToEuclidean_bijective : Function.Bijective (empiricalToEuclidean n) := by
  constructor
  · -- Injective
    intro v₁ v₂ h
    have : euclideanToEmpirical n (empiricalToEuclidean n v₁) =
           euclideanToEmpirical n (empiricalToEuclidean n v₂) := by rw [h]
    simp at this
    exact this
  · -- Surjective
    intro v
    use euclideanToEmpirical n v
    simp

/-- Scaling property: for any s > 0, an s-net in EmpiricalSpace induces an (s√n)-net in EuclideanSpace -/
theorem isENet_empiricalToEuclidean_image (hn : 0 < n)
    {t : Finset (EmpiricalSpace n)} {s : ℝ} {S : Set (EmpiricalSpace n)}
    (hnet : IsENet t s S) :
    IsENet (t.image (empiricalToEuclidean n))
           (s * Real.sqrt n)
           (empiricalToEuclidean n '' S) := by
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx_cover := hnet hx
  rw [Set.mem_iUnion₂] at hx_cover
  obtain ⟨z, hz_mem, hx_ball⟩ := hx_cover
  rw [Set.mem_iUnion₂]
  refine ⟨empiricalToEuclidean n z, Finset.mem_image.mpr ⟨z, hz_mem, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall] at hx_ball ⊢
  rw [dist_euclidean_eq_sqrt_n_mul_dist_empirical hn x z, mul_comm s (Real.sqrt n)]
  exact mul_le_mul_of_nonneg_left hx_ball (Real.sqrt_nonneg n)

/-! ### Dimension Reduction Corollary

The covering number N(s, B_n(δ), ‖·‖_n) is bounded by the covering number of a
d-dimensional Euclidean ball B_2^d(δ√n) when:
- X has full column rank (range(X) is d-dimensional), or
- X satisfies an operator norm bound ‖Xθ‖ ≤ L·‖θ‖
-/

/-- The design matrix range as a submodule -/
noncomputable def designMatrixRangeSubmodule (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (designMatrixLinearMap x)

/-- When the design matrix has full column rank, the range is d-dimensional -/
lemma designMatrixRange_finrank_eq_of_injective
    (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (designMatrixMul x)) :
    Module.finrank ℝ (designMatrixRangeSubmodule x) = d := by
  unfold designMatrixRangeSubmodule
  have hlinear_inj : Function.Injective (designMatrixLinearMap x) := hinj
  rw [LinearMap.finrank_range_of_inj hlinear_inj]
  simp only [finrank_euclideanSpace, Fintype.card_fin]

/-! ### Design Matrix Rank

The rank of the design matrix is the dimension of its range. This generalizes
the full-rank assumption to arbitrary matrices. -/

/-- The rank of the design matrix: dim(range(X)) -/
noncomputable def designMatrixRank (x : Fin n → EuclideanSpace ℝ (Fin d)) : ℕ :=
  Module.finrank ℝ (designMatrixRangeSubmodule x)

/-- Rank is at most d (the column dimension) -/
lemma designMatrixRank_le_d (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    designMatrixRank x ≤ d := by
  unfold designMatrixRank designMatrixRangeSubmodule
  calc Module.finrank ℝ (LinearMap.range (designMatrixLinearMap x))
      ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := LinearMap.finrank_range_le _
    _ = d := by simp only [finrank_euclideanSpace, Fintype.card_fin]

/-- Rank equals d when X is injective (backward compatibility) -/
lemma designMatrixRank_eq_d_of_injective (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (designMatrixMul x)) :
    designMatrixRank x = d := by
  unfold designMatrixRank
  exact designMatrixRange_finrank_eq_of_injective x hinj

/-- Rank is positive iff range is nontrivial (i.e., ∃ θ, Xθ ≠ 0) -/
lemma designMatrixRank_pos_iff (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    0 < designMatrixRank x ↔ ∃ θ, designMatrixMul x θ ≠ 0 := by
  unfold designMatrixRank designMatrixRangeSubmodule
  rw [Module.finrank_pos_iff]
  -- Nontrivial (range X) ↔ ∃ θ, Xθ ≠ 0
  constructor
  · -- Nontrivial (range X) → ∃ θ, Xθ ≠ 0
    intro hnt
    obtain ⟨v, hv_ne⟩ := @exists_ne _ hnt 0
    obtain ⟨θ, hθ_eq⟩ := LinearMap.mem_range.mp v.prop
    use θ
    intro h
    apply hv_ne
    apply Subtype.ext
    simp only [Submodule.coe_zero]
    rw [← hθ_eq]
    exact h
  · -- ∃ θ, Xθ ≠ 0 → Nontrivial (range X)
    intro ⟨θ, hθ⟩
    refine ⟨⟨designMatrixLinearMap x θ, LinearMap.mem_range_self _ θ⟩, 0, ?_⟩
    intro h
    apply hθ
    exact Subtype.ext_iff.mp h

/-- The range submodule is nontrivial when rank is positive -/
lemma designMatrixRangeSubmodule_ne_bot_of_rank_pos (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hr : 0 < designMatrixRank x) :
    designMatrixRangeSubmodule x ≠ ⊥ := by
  rw [designMatrixRank_pos_iff] at hr
  obtain ⟨θ, hθ⟩ := hr
  intro h
  apply hθ
  have hmem : designMatrixMul x θ ∈ designMatrixRangeSubmodule x := by
    unfold designMatrixRangeSubmodule
    exact LinearMap.mem_range_self _ θ
  rw [h] at hmem
  exact (Submodule.mem_bot ℝ).mp hmem

/-- The restriction of designMatrixMul to its range as a linear equivalence when injective -/
noncomputable def designMatrixEquiv (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (designMatrixMul x)) :
    EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] designMatrixRangeSubmodule x :=
  LinearEquiv.ofInjective (designMatrixLinearMap x) hinj

/-- The design matrix induces an isometry from ℝ^d to its range when properly normalized.
    More precisely, if we consider the range with the induced Euclidean norm,
    then the map preserves the norm structure. -/
lemma designMatrixMul_mem_range (x : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) :
    designMatrixMul x θ ∈ designMatrixRange n d x := by
  unfold designMatrixRange
  exact ⟨θ, rfl⟩

/-- The euclidean localized ball is contained in a ball in ℝ^n -/
lemma euclideanLocalizedBall_subset_ball (x : Fin n → EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    euclideanLocalizedBall n d δ x ⊆
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (δ * Real.sqrt n) := by
  intro v hv
  unfold euclideanLocalizedBall euclideanBallOrigin at hv
  exact hv.1

/-- The euclidean localized ball is contained in the range of X -/
lemma euclideanLocalizedBall_subset_range (x : Fin n → EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    euclideanLocalizedBall n d δ x ⊆ designMatrixRange n d x := by
  intro v hv
  unfold euclideanLocalizedBall at hv
  exact hv.2

/-- Any d-dimensional subspace of a Euclidean space admits an isometric linear equivalence to ℝ^d.
    This is a fundamental result: all finite-dimensional inner product spaces of the same dimension
    are isometrically isomorphic. -/
lemma exists_linearIsometryEquiv_of_finrank_eq (hd : 0 < d) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hV : Module.finrank ℝ V = d) :
    Nonempty (V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) := by
  haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (hV ▸ hd)
  -- Get an orthonormal basis for V, indexed by Fin (finrank ℝ V)
  let b := stdOrthonormalBasis ℝ V
  -- We need an equiv from Fin (finrank ℝ V) to Fin d
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Fintype.card (Fin d) := by
    simp only [Fintype.card_fin, hV]
  -- Reindex the basis to use Fin d, then use repr to get the isometry equivalence
  let b' := b.reindex (Fintype.equivOfCardEq hcard)
  -- b'.repr gives V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)
  exact ⟨b'.repr⟩

/-- The ball in a subspace V equals the intersection of the ambient ball with V -/
lemma submodule_closedBall_eq_inter (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    V.subtypeL '' (Metric.closedBall (0 : V) r) =
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ∩ V := by
  ext v
  simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right, Set.mem_inter_iff,
             SetLike.mem_coe]
  constructor
  · rintro ⟨u, hu, rfl⟩
    constructor
    · -- ‖V.subtypeL u‖ ≤ r
      have : ‖V.subtypeL u‖ = ‖u‖ := by
        simp only [Submodule.subtypeL_apply, Submodule.coe_norm]
      rw [this]
      exact hu
    · exact u.2
  · intro ⟨hball, hmem⟩
    use ⟨v, hmem⟩
    constructor
    · -- ‖⟨v, hmem⟩‖ ≤ r
      simp only [Submodule.coe_norm]
      exact hball
    · simp only [Submodule.subtypeL_apply]

/-- Linear isometry equivalence preserves closed balls -/
lemma LinearIsometryEquiv.image_closedBall {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (r : ℝ) :
    e '' (Metric.closedBall 0 r) = Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [e.norm_map]
    exact hx
  · intro hy
    use e.symm y
    constructor
    · rw [e.symm.norm_map]
      exact hy
    · simp

end LeastSquares
