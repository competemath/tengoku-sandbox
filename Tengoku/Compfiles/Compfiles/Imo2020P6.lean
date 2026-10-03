/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 2020, Problem 6

Consider an integer n > 1, and a set S of n points in the plane
such that the distance between any two points in S is at least 1.
Prove that there is a line l separating S such that the distance
from any point of S to l is at least Ω(n ^ (-1/3)).

(A line l separates a set of points S if some segment jointing
two points in S croses l.)
-/

namespace Imo2020P6

open Finset Module
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] (dim : Nat) [Fact (finrank ℝ V = dim + 1)]

theorem exists_between_and_separated {ι : Type*} (S : Finset ι) (f : ι → ℝ) (n : Nat)
    (a b : ℝ) (hab : a < b) (hS : #{p ∈ S | f p ∈ Set.Ioo a b} < n) :
    ∃ x ∈ Set.Ioo a b, ∀ p ∈ S, (b - a) / (2 * n) ≤ |x - f p| := by
  -- make `n` defEq to `_ + 1`
  cases n with | zero => contradiction | succ n => _
  set n := n+1
  -- separate the interval `(0,1)` into `n` equally spaced intervals
  let interval (i : Fin n) : Set ℝ :=
    Set.Ioo (AffineMap.lineMap a b ((i : ℝ) / n)) (AffineMap.lineMap a b (((i : ℝ) + 1) / n))

  let rel (p : ι) (k : Fin n) : Prop :=
    f p ∈ interval k

  by_cases h : ∀ k ∈ Finset.univ, ∃ p ∈ ({p ∈ S | f p ∈ Set.Ioo a b} : Finset _), rel p k
  · -- show that the `n` intervals are disjoint
    have disjoint : Pairwise fun i j => Disjoint (interval i) (interval j) := by
      rw [pairwise_disjoint_on]
      intro i j hlt
      unfold interval
      rw [Set.Ioo_disjoint_Ioo]; apply le_sup_of_le_right; apply inf_le_of_left_le
      rw [lineMap_le_lineMap_iff_of_lt' hab]
      gcongr
      norm_cast
    -- use the pigeon hole principle on the disjoint intervals
    have := card_le_card_of_forall_subsingleton' rel h <| by
      simp only [mem_univ, true_and]
      intro p _
      unfold rel
      intro i hi j hj
      by_contra h
      replace disjoint : Disjoint (interval i) (interval j) := disjoint h
      rw [Set.disjoint_left] at disjoint
      exact disjoint hi hj
    rw [card_univ, Fintype.card_fin] at this
    lia
  push Not at h; simp only [mem_univ, Set.mem_Ioo, mem_filter, and_imp, true_and] at h
  -- the `i`th interval in disjoint with `(f '' S) ∩ (a, b)`
  obtain ⟨i, h⟩ := h; unfold rel at h
  -- use the midpoint of the `i`th interval
  use AffineMap.lineMap a b (i / n + 1 / (2 * n) : ℝ)
  have ineq₁: (i / n : ℝ) ≤ 1 - 1 / n := by grw [Fin.is_le]; field_simp [n]; simp [n]
  have : b - a > 0 := sub_pos.mpr hab
  -- check that the point is in between `a` and `b`
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [one_div, mul_inv_rev, AffineMap.lineMap_apply_ring', lt_add_iff_pos_left]
    positivity
  · rw [AffineMap.lineMap_apply_ring']
    have ineq₂: (1 / (2 * n) : ℝ) < 1 / n := by
      gcongr; norm_cast; lia
    linear_combination (ineq₁ + ineq₂) * (b - a)
  intro p hp
  -- the `i`th interval is disjoint with `f '' S`
  have : f p ∉ interval i := by
    by_cases ha : a < f p
    · by_cases hb : f p < b
      · exact h p hp ha hb
      · apply Set.notMem_Ioo_of_ge
        push Not at hb
        rw [AffineMap.lineMap_apply_ring']
        linear_combination ineq₁ * (b - a) + hb
    · apply Set.notMem_Ioo_of_le
      push Not at ha
      grw [ha]
      rw [AffineMap.lineMap_apply_ring', le_add_iff_nonneg_left]
      positivity
  simp only [interval, Set.mem_Ioo, not_and_or, not_lt] at this
  -- `y ∈ S` is either above or below the interval, either way we get the bound
  rcases this with h | h
  · grw [← le_abs_self, h]
    rw [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_ring']
    ring_nf; rfl
  · rw [abs_sub_comm]
    grw [← le_abs_self, ← h]
    rw [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_ring']
    ring_nf; rfl

/-- Computes "how far along" the segment from `a` to `b` the point `p` lies. -/
noncomputable def project (a b p : P) : ℝ := innerSL ℝ (a -ᵥ b) (a -ᵥ p) / ‖a -ᵥ b‖

@[simp] theorem project_self_left {a b : P} : project a b a = 0 := by simp [project]
@[simp] theorem project_self_right {a b : P} (h : a ≠ b) : project a b b = ‖a -ᵥ b‖ := by
  simp only [project, innerSL_apply_apply]
  rw [real_inner_self_eq_norm_sq, div_eq_iff, pow_two]
  · rwa [norm_ne_zero_iff, vsub_ne_zero]

theorem exists_affine_between_and_separated {ι : Type*} (S : Finset ι) (f : ι → P) (n : ℝ)
    (a b : P) (i j : ℝ) (hi : 0 ≤ i) (hij : i < j) (hj : j ≤ dist a b)
    (hS : #{p ∈ S | project a b (f p) ∈ Set.Ioo i j} ≤ n - 1)
    (hab : a ≠ b) :
    ∃ l : AffineSubspace ℝ P, finrank ℝ l.direction = dim ∧ l.SOppSide a b ∧
    ∀ p ∈ S, (j - i) / (2 * n) ≤ Metric.infDist (f p) l := by

  obtain ⟨x, x_ioo, hx⟩ := exists_between_and_separated S (project a b <| f ·) (⌊n-1⌋₊+1) i j hij
    (by
      rw [← Nat.cast_lt (α := ℝ)]; push_cast
      grw [hS]
      exact Nat.lt_floor_add_one (n - 1))

  use .mk' (AffineMap.lineMap a b (x / dist a b)) (LinearMap.ker (innerₛₗ ℝ (a -ᵥ b)))

  have : Nonempty (AffineSubspace.mk'
      (AffineMap.lineMap a b (x / dist a b)) (LinearMap.ker (innerₛₗ ℝ (a -ᵥ b)))) := by
    constructor
    use (AffineMap.lineMap a b (x / dist a b))
    apply AffineSubspace.self_mem_mk'

  constructor
  · -- The subspace has the required dimension
    have : LinearMap.ker ((innerₛₗ ℝ) (a -ᵥ b)) = (ℝ ∙ (a -ᵥ b))ᗮ := by
      ext x
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; rfl
    rw [AffineSubspace.direction_mk', this]
    apply Submodule.finrank_orthogonal_span_singleton (by rwa [vsub_ne_zero])
  have : 0 < ‖a -ᵥ b‖ := by
    rwa [norm_pos_iff, vsub_ne_zero]
  constructor
  · refine Sbtw.sOppSide_of_notMem_of_mem ?_ ?_ (AffineSubspace.self_mem_mk' _ _)
    · simp [hab, lt_of_le_of_lt hi x_ioo.1, lt_of_lt_of_le x_ioo.2 hj, div_lt_one]
    · simp [hab, (lt_of_le_of_lt hi x_ioo.1).ne.symm]

  intro p hp
  -- we show that the distance between `p` and the plane corresponds to
  -- the distance between `project p` and `x`.
  specialize hx p hp
  rw [project, sub_div' (by positivity), abs_div, le_div_iff₀' (by positivity),
    abs_of_pos (by positivity)] at hx
  rw [Metric.infDist_eq_iInf]
  apply le_ciInf
  simp only [SetLike.coe_sort_coe, dist_eq_norm_vsub, Subtype.forall, AffineSubspace.mem_mk',
             LinearMap.mem_ker, innerₛₗ_apply_apply]
  intro y hy
  rw [← mul_le_mul_iff_right₀ this]
  calc
    _ ≤ ‖a -ᵥ b‖ * ((j - i) / (2 * ↑(⌊n - 1⌋₊ + 1))) := by
      gcongr
      push_cast; rw [← le_sub_iff_add_le]
      refine Nat.floor_le ?_
      grw [← hS]
      simp
    _ ≤ |x * ‖a -ᵥ b‖ - ⟪a -ᵥ b, a -ᵥ f p⟫| := hx
    _ = |⟪a -ᵥ b, f p -ᵥ (AffineMap.lineMap a b) (x / ‖a -ᵥ b‖)⟫| := by
      congr 1
      rw [sub_eq_iff_eq_add', ← inner_add_right]
      simp only [vsub_add_vsub_cancel, AffineMap.left_vsub_lineMap]
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    _ = |⟪a -ᵥ b, f p -ᵥ y⟫| := by congr 1; rw [← sub_eq_zero, ← inner_sub_right]; simp; exact hy
    _ ≤ ‖a -ᵥ b‖ * ‖f p -ᵥ y‖ := abs_real_inner_le_norm ..

theorem card_le_of_separated {ι : Type*} (S : Finset ι) (f : ι → ℝ) {ε a b : ℝ} (hε : 0 < ε)
    (hab : a ≤ b) (h_sep : (S : Set ι).Pairwise fun x y => ε ≤ dist (f x) (f y))
    (hbound : ∀ x ∈ S, f x ∈ Set.Icc a b) : #S ≤ ⌊(b - a) / ε + 1⌋ := by
  suffices h : #S ≤ #(Icc 0 ⌊(b - a) / ε⌋) by
    have : 0 ≤ ⌊(b - a) / ε⌋ + 1 := by
      have := sub_nonneg_of_le hab
      positivity
    simpa [this] using h
  apply Finset.card_le_card_of_injOn fun x => ⌊(f x - a) / ε⌋
  · intro x hx
    rw [coe_Icc, Set.mem_Icc]; constructor
    · rw [Int.floor_nonneg]
      refine div_nonneg ?_ hε.le
      rw [sub_nonneg]
      exact (hbound x hx).1
    · apply Int.floor_le_floor
      rw [div_le_div_iff_of_pos_right hε, sub_le_sub_iff_right]
      exact (hbound x hx).2
  · intro x hx y hy h
    apply Int.abs_sub_lt_one_of_floor_eq_floor at h
    field_simp at h
    rw [sub_sub_sub_cancel_right, abs_div, abs_eq_self.mpr hε.le, div_lt_one hε] at h
    contrapose! h
    exact h_sep hx hy h

/--
In a strip of width `1/2`, if the points have pairwise distance at least `1`,
then we can bound the number of points.
-/
theorem card_le_of_separated_in_strip (eqv : P ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (S : Finset P)
    (h_sep : (S.filter (eqv · 0 ∈ Set.Ioo 0 (1 / 2)) : Set P).Pairwise fun x y => 1 ≤ dist x y)
    {N : ℝ} (hN : 1 ≤ N) (h_bound : ∀ x ∈ S.filter (eqv · 0 ∈ Set.Ioo 0 (1 / 2)), |eqv x 1| ≤ N) :
    #(S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) ≤ N*6-1 := by
  suffices h : #(S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) ≤ ⌊(N - (-N)) / (1/2) + 1⌋ by
    rw [Int.le_floor, Int.cast_natCast] at h
    linarith only [h, hN]
  refine card_le_of_separated (S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) (eqv · 1)
    (by norm_num) (by linarith only [hN]) ?_
    (fun x hx => ⟨neg_le_of_abs_le (h_bound x hx), le_of_abs_le (h_bound x hx)⟩)
  intro x hx y hy h_ne
  specialize h_sep hx hy h_ne
  dsimp only
  have := EuclideanSpace.dist_eq (eqv x) (eqv y)
  simp at this
  rw [this] at h_sep
  rw [Real.one_le_sqrt] at h_sep
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices (dist (eqv x 0) (eqv y 0))^2 ≤ (1/2)^2 by
    linarith only [this, h_sep]
  rw [sq_le_sq₀ (by positivity) (by positivity), Real.dist_eq, abs_le]
  rw [coe_filter] at hx hy
  rcases hx with ⟨_, xl, xr⟩
  rcases hy with ⟨_, yl, yr⟩
  constructor
  · linear_combination xl + yr
  · linear_combination xr + yl

variable [Fact (Module.finrank ℝ V = 2)]

end Imo2020P6
