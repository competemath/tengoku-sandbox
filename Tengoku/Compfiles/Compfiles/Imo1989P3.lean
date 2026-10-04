/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1989, Problem 3

Let $n$ and $k$ be positive integers and let $S$ be a set of $n$ points in
the plane such that
  (i) no three points of $S$ are collinear, and
  (ii) for each point $P$ of $S$ there are at least $k$ points of $S$
       equidistant from $P$.
Prove that $k < \frac{1}{2} + \sqrt{2n}$.
-/

namespace Imo1989P3

abbrev Pt := EuclideanSpace ℝ (Fin 2)

open scoped InnerProductSpace

/-- If `P` and `Q` are both equidistant from `A` and `B`, then `P - Q` is
orthogonal to `B - A`. -/
lemma inner_sub_eq_zero_of_dist_eq {A B P Q : Pt} (hP : dist P A = dist P B)
    (hQ : dist Q A = dist Q B) : ⟪P - Q, B - A⟫_ℝ = 0 := by
  have hsq : ∀ X : Pt, dist X A = dist X B →
      ‖X‖ ^ 2 - 2 * ⟪X, A⟫_ℝ + ‖A‖ ^ 2 = ‖X‖ ^ 2 - 2 * ⟪X, B⟫_ℝ + ‖B‖ ^ 2 := by
    intro X hX
    rw [dist_eq_norm, dist_eq_norm] at hX
    have hsqx : ‖X - A‖ ^ 2 = ‖X - B‖ ^ 2 := by rw [hX]
    rwa [norm_sub_sq_real, norm_sub_sq_real] at hsqx
  have h1 := hsq P hP
  have h2 := hsq Q hQ
  simp only [inner_sub_left, inner_sub_right]
  linear_combination (h1 - h2) / 2

/-- Three points that are all equidistant from two distinct points `A`, `B`
are collinear (they lie on the perpendicular bisector of `A` and `B`,
which is a line). -/
lemma collinear_of_dist_eq {A B : Pt} (hAB : A ≠ B) {p₁ p₂ p₃ : Pt} (h₁₂ : p₁ ≠ p₂)
    (h1 : dist p₁ A = dist p₁ B) (h2 : dist p₂ A = dist p₂ B)
    (h3 : dist p₃ A = dist p₃ B) :
    Collinear ℝ ({p₁, p₂, p₃} : Set Pt) := by
  have hv : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hu20 : p₂ - p₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have hu2mem : p₂ - p₁ ∈ (ℝ ∙ (B - A))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (inner_eq_zero_symm.mp (inner_sub_eq_zero_of_dist_eq h2 h1))
  have hu3mem : p₃ - p₁ ∈ (ℝ ∙ (B - A))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (inner_eq_zero_symm.mp (inner_sub_eq_zero_of_dist_eq h3 h1))
  have : Fact (Module.finrank ℝ Pt = 1 + 1) := ⟨by rw [finrank_euclideanSpace_fin]⟩
  have hfin : Module.finrank ℝ (ℝ ∙ (B - A))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton hv
  have heq : (ℝ ∙ (B - A))ᗮ = ℝ ∙ (p₂ - p₁) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin hu2mem hu20
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (heq ▸ hu3mem)
  rw [collinear_iff_of_mem (Set.mem_insert p₁ _)]
  refine ⟨p₂ -ᵥ p₁, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨r, ?_⟩
    rw [vsub_eq_sub, vadd_eq_add, hr, sub_add_cancel]

end Imo1989P3
