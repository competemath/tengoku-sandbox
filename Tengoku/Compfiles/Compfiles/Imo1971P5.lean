/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1971, Problem 5

Prove that for every natural number m there exists a nonempty finite
set S of points in the plane with the following property:
For every point s in S, there are exactly m points which are at a unit
distance from s.
-/

namespace Imo1971P5

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

lemma norm_one_infinity : {p : Pt | ‖p‖ = 1}.Infinite := by
  suffices h : (Metric.sphere (0 : Pt) 1).Infinite by
    convert h using 1; ext p; simp
  apply IsPreconnected.infinite_of_nontrivial
  · refine isPreconnected_sphere ?_ 0 1
    rw [← Module.finrank_eq_rank (R := ℝ) (M := Pt), finrank_euclideanSpace_fin]
    norm_num
  · refine ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single],
            EuclideanSpace.single 1 1, by simp [PiLp.norm_single], ?_⟩
    intro h
    have : (EuclideanSpace.single 0 (1 : ℝ) : Pt) 1 = (EuclideanSpace.single 1 (1 : ℝ) : Pt) 1 :=
      congr_arg (· 1) h
    simp at this

universe u

lemma exists_three_of_infinite
  {α : Type u} {s : Set α} (hs : s.Infinite)
  : ∃ p q r : α, p ∈ s ∧ q ∈ s ∧ r ∈ s
    ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hs.nontrivial
  obtain ⟨r, hr, hrpq⟩ := (hs.sdiff (Set.toFinite {p, q})).nonempty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hrpq
  exact ⟨p, q, r, hp, hq, hr, hpq, fun h => hrpq.2 h.symm, fun h => hrpq.1 h⟩

lemma sphere_inter_finite
  {s₁ s₂ : EuclideanGeometry.Sphere Pt} (hs : s₁ ≠ s₂) :
  ((s₁ : Set Pt) ∩ s₂).Finite := by
  by_contra! h'
  rcases exists_three_of_infinite h' with ⟨p, q, r, hp, hq, hr, hpq, hqr, hrp⟩
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  rw [Set.mem_inter_iff, EuclideanGeometry.Sphere.mem_coe, EuclideanGeometry.Sphere.mem_coe] at hp hq hr
  have h'' := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
    hd hs hpq hp.left hq.left hr.left hp.right hq.right hr.right
  grind only

lemma sphere_eq_sub_norm (o : Pt) (r : ℝ)
  : {p : Pt | ‖p - o‖ = r} = (EuclideanGeometry.Sphere.mk o r : Set Pt) := by
  ext p
  rw [Set.mem_ofPred_eq, mem_sphere_iff_norm]

lemma norm_one_inter_finite {s : Pt} (hs : s ≠ 0)
  : ({p : Pt | ‖p - 0‖ = 1} ∩ {p : Pt | ‖p - s‖ = 1}).Finite := by
  rw [sphere_eq_sub_norm 0 1, sphere_eq_sub_norm s 1]
  apply sphere_inter_finite
  rw [ne_eq, EuclideanGeometry.Sphere.ext_iff]
  dsimp
  rw [and_iff_left rfl, ← ne_eq]
  symm
  exact hs

lemma finite₁ {S : Set Pt} (hS : S.Finite)
  : {p | ∃ s t, s ∈ S ∧ t ∈ S ∧ s - t = p}.Finite := by
  have h' : {p | ∃ s t, s ∈ S ∧ t ∈ S ∧ s - t = p}
    = ⋃ s ∈ S, ⋃ t ∈ S, {s - t} := by
    ext p
    simp
    constructor <;> rintro ⟨s, hs, t, ht, hstp⟩ <;> use s <;> rw [and_iff_right hs]
      <;> use t <;> rw [and_iff_right ht, hstp]
  rw [h']
  apply Set.Finite.biUnion hS
  intro s hs
  apply Set.Finite.biUnion hS
  intro t ht
  apply Set.finite_singleton

lemma finite₂ {S : Set Pt} (hS : S.Finite)
  : {p : Pt | ∃ (s t : Pt), s ∈ S ∧ t ∈ S ∧ s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1}.Finite := by
  have h' : {p : Pt | ∃ (s t : Pt), s ∈ S ∧ t ∈ S ∧ s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1}
    = ⋃ s ∈ S, ⋃ t ∈ S, {p : Pt | s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1} := by
    ext p
    simp
    constructor <;> rintro ⟨s, hs, t, ht, hstp⟩ <;> use s <;> rw [and_iff_right hs]
      <;> use t <;> rw [and_iff_right ht] <;> tauto
  rw [h']
  apply Set.Finite.biUnion hS
  intro s hs
  apply Set.Finite.biUnion hS
  intro t ht
  by_cases! hst : s = t
  · have h'' :  {p | s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p
      contrapose! hst
      dsimp at hst
      exact hst.left
    rw [h'']
    exact Set.finite_empty
  · have h'' :  {p | s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1}
      = {p : Pt | ‖p - 0‖ = 1} ∩ {p : Pt | ‖p - (s - t)‖ = 1} := by
      ext p
      simp [- ne_eq]
      rw [and_iff_right hst]
      constructor <;> rintro ⟨hp₁, hp₂⟩ <;> rw [and_iff_right hp₁, ← hp₂]
        <;> rw [← sub_add, dist_comm, dist_eq_norm] <;> abel_nf
    rw [h'']
    rw [← sub_eq_zero.ne] at hst
    exact norm_one_inter_finite hst

end Imo1971P5
