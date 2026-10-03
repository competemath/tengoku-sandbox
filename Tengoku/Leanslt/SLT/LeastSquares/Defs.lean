/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq
import Tengoku.Leanslt.SLT.GaussianMeasure

/-!
# Least Squares Regression: Core Definitions

This file contains the fundamental definitions for analyzing least squares regression.

## Main Definitions

* `IsStarShaped` - A function class is star-shaped around 0
* `empiricalNorm` - The empirical L² norm over a sample
* `localizedBall` - Ball in a function class w.r.t. empirical norm
* `stdGaussianPi` - Product measure of n i.i.d. standard Gaussians
* `LocalGaussianComplexity` - Local Gaussian complexity at radius δ
* `satisfiesCriticalInequality` - The critical inequality G_n(δ)/δ ≤ δ/(2σ)
* `shiftedClass` - The shifted function class F - {f*}
* `isLeastSquaresEstimator` - Definition of least squares estimator
* `RegressionModel` - The regression model y_i = f*(x_i) + σw_i

-/

open MeasureTheory Finset BigOperators Real ProbabilityTheory GaussianMeasure

namespace LeastSquares

variable {X : Type*}

/-- Star-shaped set: A set H of functions is star-shaped around 0 if:
1. The zero function is in H
2. For any h ∈ H and α ∈ [0,1], we have α • h ∈ H -/
def IsStarShaped (H : Set (X → ℝ)) : Prop :=
  (0 : X → ℝ) ∈ H ∧ ∀ h ∈ H, ∀ α : ℝ, 0 ≤ α → α ≤ 1 → (α • h) ∈ H

/-- The empirical L² norm: ‖f‖_n = √(n⁻¹ Σᵢ fᵢ²) -/
noncomputable def empiricalNorm (n : ℕ) (f : Fin n → ℝ) : ℝ :=
  Real.sqrt ((n : ℝ)⁻¹ * ∑ k : Fin n, f k ^ 2)

/-- The squared empirical norm equals n⁻¹ Σᵢ fᵢ² -/
lemma empiricalNorm_sq (n : ℕ) (f : Fin n → ℝ) :
    (empiricalNorm n f) ^ 2 = (n : ℝ)⁻¹ * ∑ k : Fin n, f k ^ 2 := by
  unfold empiricalNorm
  rw [sq_sqrt]
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · exact sum_nonneg fun i _ => sq_nonneg _

/-- Empirical norm is non-negative -/
lemma empiricalNorm_nonneg (n : ℕ) (f : Fin n → ℝ) : 0 ≤ empiricalNorm n f :=
  Real.sqrt_nonneg _

/-- Empirical norm of zero is zero -/
lemma empiricalNorm_zero (n : ℕ) : empiricalNorm n (0 : Fin n → ℝ) = 0 := by
  unfold empiricalNorm
  simp

/-- Empirical norm is symmetric under negation: ‖-f‖_n = ‖f‖_n -/
lemma empiricalNorm_neg (n : ℕ) (f : Fin n → ℝ) : empiricalNorm n (-f) = empiricalNorm n f := by
  unfold empiricalNorm
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply, neg_sq]

/-- Wrapper type for Fin n → ℝ with the empirical norm as metric.
The empirical metric is dist(a,b) = √(n⁻¹ Σᵢ (aᵢ - bᵢ)²). -/
def EmpiricalSpace (n : ℕ) := Fin n → ℝ

namespace EmpiricalSpace

instance (n : ℕ) : Inhabited (EmpiricalSpace n) := ⟨fun _ => 0⟩

instance (n : ℕ) : Zero (EmpiricalSpace n) := ⟨fun _ => 0⟩

instance (n : ℕ) : Add (EmpiricalSpace n) := ⟨fun a b i => a i + b i⟩

instance (n : ℕ) : Sub (EmpiricalSpace n) := ⟨fun a b i => a i - b i⟩

instance (n : ℕ) : Neg (EmpiricalSpace n) := ⟨fun a i => -a i⟩

/-- Distance in EmpiricalSpace is the empirical norm of the difference -/
noncomputable instance instDist (n : ℕ) : Dist (EmpiricalSpace n) where
  dist a b := empiricalNorm n (a - b)

/-- EmpiricalSpace has an extended distance -/
noncomputable instance instEDist (n : ℕ) : EDist (EmpiricalSpace n) where
  edist a b := ENNReal.ofReal (dist a b)

/-- dist(a, a) = 0 -/
lemma dist_self (n : ℕ) (a : EmpiricalSpace n) : dist a a = 0 := by
  show empiricalNorm n (a - a) = 0
  have h : (a - a : EmpiricalSpace n) = 0 := by
    funext i
    show a i - a i = (0 : Fin n → ℝ) i
    simp
  rw [h]
  exact empiricalNorm_zero n

/-- dist(a, b) = dist(b, a) -/
lemma dist_comm (n : ℕ) (a b : EmpiricalSpace n) : dist a b = dist b a := by
  show empiricalNorm n (a - b) = empiricalNorm n (b - a)
  have h : (a - b : EmpiricalSpace n) = -(b - a) := by
    funext i
    show a i - b i = -(b i - a i)
    ring
  rw [h]
  exact empiricalNorm_neg n _

/-- dist(a, b) ≥ 0 -/
lemma dist_nonneg (n : ℕ) (a b : EmpiricalSpace n) : 0 ≤ dist a b :=
  empiricalNorm_nonneg n (a - b)

/-- Triangle inequality: dist(a, c) ≤ dist(a, b) + dist(b, c) -/
lemma dist_triangle (n : ℕ) (a b c : EmpiricalSpace n) :
    dist a c ≤ dist a b + dist b c := by
  show empiricalNorm n (a - c) ≤ empiricalNorm n (a - b) + empiricalNorm n (b - c)
  unfold empiricalNorm
  -- Expand subtraction in EmpiricalSpace
  have eq_ac : ∀ k, (a - c : EmpiricalSpace n) k = a k - c k := fun k => rfl
  have eq_ab : ∀ k, (a - b : EmpiricalSpace n) k = a k - b k := fun k => rfl
  have eq_bc : ∀ k, (b - c : EmpiricalSpace n) k = b k - c k := fun k => rfl
  simp_rw [eq_ac, eq_ab, eq_bc]
  by_cases hn : n = 0
  · simp [hn]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn_inv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hn_pos)
  -- Factor out √(n⁻¹) and use EuclideanSpace norm
  have h_factor : ∀ f : Fin n → ℝ, Real.sqrt ((n : ℝ)⁻¹ * ∑ i, (f i)^2) =
      Real.sqrt (n : ℝ)⁻¹ * Real.sqrt (∑ i, (f i)^2) := fun f => by
    rw [Real.sqrt_mul hn_inv_nonneg]
  rw [h_factor (fun i => a i - c i), h_factor (fun i => a i - b i),
      h_factor (fun i => b i - c i), ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  -- Convert to EuclideanSpace norms using the equivalence
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let a' : EuclideanSpace ℝ (Fin n) := e.symm a
  let b' : EuclideanSpace ℝ (Fin n) := e.symm b
  let c' : EuclideanSpace ℝ (Fin n) := e.symm c
  -- The equivalence preserves function values
  have h_a' : ∀ i, a' i = a i := fun i => rfl
  have h_b' : ∀ i, b' i = b i := fun i => rfl
  have h_c' : ∀ i, c' i = c i := fun i => rfl
  have h_norm : ∀ (x y : EuclideanSpace ℝ (Fin n)),
      Real.sqrt (∑ i, (x i - y i)^2) = ‖x - y‖ := fun x y => by
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
    rfl
  -- Rewrite using the equalities
  simp only [← h_a', ← h_b', ← h_c']
  rw [h_norm a' c', h_norm a' b', h_norm b' c']
  -- a - c = (a - b) + (b - c), then use norm_add_le
  have h_eq : a' - c' = (a' - b') + (b' - c') := (sub_add_sub_cancel a' b' c').symm
  rw [h_eq]
  exact norm_add_le (a' - b') (b' - c')

/-- edist is well-defined -/
lemma edist_dist (n : ℕ) (a b : EmpiricalSpace n) :
    edist a b = ENNReal.ofReal (dist a b) := rfl

/-- EmpiricalSpace is a PseudoMetricSpace with empirical norm distance -/
noncomputable instance instPseudoMetricSpace (n : ℕ) : PseudoMetricSpace (EmpiricalSpace n) where
  dist_self := dist_self n
  dist_comm := dist_comm n
  dist_triangle := dist_triangle n
  edist_dist := edist_dist n

/-- Coercion from EmpiricalSpace to Fin n → ℝ -/
def toFun (n : ℕ) (v : EmpiricalSpace n) : Fin n → ℝ := v

/-- Coercion from Fin n → ℝ to EmpiricalSpace -/
def ofFun (n : ℕ) (v : Fin n → ℝ) : EmpiricalSpace n := v

@[simp]
lemma toFun_ofFun (n : ℕ) (v : Fin n → ℝ) : toFun n (ofFun n v) = v := rfl

@[simp]
lemma ofFun_toFun (n : ℕ) (v : EmpiricalSpace n) : ofFun n (toFun n v) = v := rfl

end EmpiricalSpace

/-- Empirical metric image: Map a function g : X → ℝ to its empirical representation in EmpiricalSpace n.
This is the evaluation at sample points: g ↦ (g(x₁), ..., g(xₙ)). -/
def empiricalMetricImage {X : Type*} (n : ℕ) (x : Fin n → X) (g : X → ℝ) : EmpiricalSpace n :=
  fun i => g (x i)

/-- The distance between empiricalMetricImages equals the empirical norm of pointwise differences -/
lemma dist_empiricalMetricImage {X : Type*} (n : ℕ) (x : Fin n → X) (g₁ g₂ : X → ℝ) :
    dist (empiricalMetricImage n x g₁) (empiricalMetricImage n x g₂) =
    empiricalNorm n (fun i => g₁ (x i) - g₂ (x i)) := by
  rfl

/-- The localized ball B_n(δ; H) = {h ∈ H : ‖h‖_n ≤ δ} -/
def localizedBall {n : ℕ} (H : Set (X → ℝ)) (δ : ℝ) (x : Fin n → X) : Set (X → ℝ) :=
  {h ∈ H | empiricalNorm n (fun i => h (x i)) ≤ δ}

/-- Local Gaussian complexity:
G_n(δ; H) = 𝔼_w[sup_{h ∈ B_n(δ;H)} |n⁻¹ Σᵢ wᵢh(xᵢ)|]
where w ~ N(0, I_n) -/
noncomputable def LocalGaussianComplexity (n : ℕ) (H : Set (X → ℝ)) (δ : ℝ) (x : Fin n → X) : ℝ :=
  ∫ w, ⨆ h ∈ localizedBall H δ x, |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)| ∂(stdGaussianPi n)

/-- The critical inequality: G_n(δ)/δ ≤ δ/(2σ) -/
def satisfiesCriticalInequality (n : ℕ) (σ δ : ℝ) (H : Set (X → ℝ)) (x : Fin n → X) : Prop :=
  LocalGaussianComplexity n H δ x / δ ≤ δ / (2 * σ)

/-- The shifted class F* = F - {f*} = {f - f* : f ∈ F} -/
def shiftedClass (F : Set (X → ℝ)) (f_star : X → ℝ) : Set (X → ℝ) :=
  {h | ∃ f ∈ F, h = f - f_star}

/-- f - f* is in the shifted class when f ∈ F -/
lemma mem_shiftedClass_of_mem {F : Set (X → ℝ)} {f_star f : X → ℝ} (hf : f ∈ F) :
    f - f_star ∈ shiftedClass F f_star :=
  ⟨f, hf, rfl⟩

/-- 0 is in the shifted class when f* ∈ F -/
lemma zero_mem_shiftedClass_of_f_star_mem {F : Set (X → ℝ)} {f_star : X → ℝ} (hf : f_star ∈ F) :
    (0 : X → ℝ) ∈ shiftedClass F f_star := by
  use f_star, hf
  ext x
  simp

/-- A function f_hat is the least squares estimator if:
1. f_hat ∈ F
2. For all f ∈ F: Σᵢ(yᵢ - f_hat(xᵢ))² ≤ Σᵢ(yᵢ - f(xᵢ))² -/
def isLeastSquaresEstimator {n : ℕ} (y : Fin n → ℝ) (F : Set (X → ℝ)) (x : Fin n → X)
    (f_hat : X → ℝ) : Prop :=
  f_hat ∈ F ∧ ∀ f ∈ F, ∑ i, (y i - f_hat (x i))^2 ≤ ∑ i, (y i - f (x i))^2

/-- The optimality condition of least squares -/
lemma isLeastSquaresEstimator.le_of_mem {n : ℕ} {y : Fin n → ℝ} {F : Set (X → ℝ)} {x : Fin n → X}
    {f_hat : X → ℝ} (h : isLeastSquaresEstimator y F x f_hat) {f : X → ℝ} (hf : f ∈ F) :
    ∑ i, (y i - f_hat (x i))^2 ≤ ∑ i, (y i - f (x i))^2 :=
  h.2 f hf

/-! ### Regression Model -/

/-- The regression model bundles:
- x : design points
- f_star : true function
- σ : noise scale (positive)
- noiseDistribution : distribution of noise (default: stdGaussianPi n)

The model equation is: y_i = f*(x_i) + σ * w_i where w ~ noiseDistribution -/
structure RegressionModel (n : ℕ) (X : Type*) where
  /-- Design points -/
  x : Fin n → X
  /-- True regression function -/
  f_star : X → ℝ
  /-- Noise scale -/
  σ : ℝ
  /-- σ is positive -/
  hσ_pos : 0 < σ
  /-- Noise distribution (default: n i.i.d. standard Gaussians) -/
  noiseDistribution : Measure (Fin n → ℝ) := stdGaussianPi n

variable {n : ℕ}

/-- The response given a noise realization:
y_i = f*(x_i) + σ * w_i -/
def RegressionModel.response (M : RegressionModel n X) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M.f_star (M.x i) + M.σ * w i

/-- Response at index i equals f*(x_i) + σ * w_i -/
@[simp]
lemma RegressionModel.response_apply (M : RegressionModel n X) (w : Fin n → ℝ) (i : Fin n) :
    M.response w i = M.f_star (M.x i) + M.σ * w i := rfl

/-- σ² is positive -/
lemma RegressionModel.sq_σ_pos (M : RegressionModel n X) : 0 < M.σ ^ 2 :=
  sq_pos_of_pos M.hσ_pos

/-- σ is non-negative -/
lemma RegressionModel.σ_nonneg (M : RegressionModel n X) : 0 ≤ M.σ :=
  le_of_lt M.hσ_pos

end LeastSquares
