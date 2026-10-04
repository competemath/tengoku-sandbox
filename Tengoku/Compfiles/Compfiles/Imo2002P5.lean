/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2002, Problem 5

Determine all functions f : ℝ → ℝ such that

  (f(x) + f(z))(f(y) + f(t)) = f(xy - zt) + f(xt + yz)

for all real numbers x,y,z,t.
-/

namespace Imo2002P5

lemma extend_function_mono
    {u f : ℝ → ℝ}
    (u_mono : ∀ x y, 0 ≤ x → x ≤ y → u x ≤ u y)
    (f_cont : Continuous f)
    (h : ∀ x : ℚ, u x = f x)
    (x : ℝ) (xpos : 0 < x) :
    u x = f x := by
  by_contra! hx
  let ε : ℝ := |u x - f x|
  have hε : 0 < ε := abs_sub_pos.mpr hx

  -- then find a δ such that for all z, |z-x| < δ implies that
  -- |f z - f x| < ε.
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp f_cont x ε hε
  obtain h1 | h2 | h3 := lt_trichotomy (u x) (f x)
  · -- pick a rational point less than x that's in the ball s,
    -- and greater than zero
    have : ∃ z : ℚ, (z:ℝ) < x ∧ dist (z:ℝ) x < δ ∧ 0 < (z:ℝ) := by
      obtain h3 | h4 := le_or_gt x δ
      · obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn xpos
        refine ⟨z, hz2, ?_⟩
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hz2)]
        constructor
        · linarith
        · order
      have hxδ : x - δ < x := sub_lt_self x hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hxδ
      refine ⟨z, hz2, ?_⟩
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hz2)]
      constructor
      · linarith
      · linarith

    obtain ⟨z, h_z_lt_x, hxz, zpos⟩ := this
    -- then dist (f z) (f x) < ε.
    have hbzb := hδ z hxz
    rw [← h z] at hbzb
    have huzuy : u x < u z := by
      have hufp : u x - f x < 0 := by linarith
      have hua : ε = -(u x - f x) := abs_of_neg hufp
      rw [hua, Real.dist_eq] at hbzb
      obtain h5 | h6 := em (f x < u z)
      · linarith
      · have : u z - f x ≤ 0 := by linarith
        rw[abs_eq_neg_self.mpr this] at hbzb
        linarith
    -- so u(z) < u(x), contradicting u_mono.
    have := u_mono z x zpos.le h_z_lt_x.le
    linarith
  · exact hx h2
  · -- pick a rational point z greater than x that's in the ball s,
    have : ∃ z : ℚ, x < z ∧ dist (z:ℝ) x < δ := by
      have hxδ : x < x + δ := lt_add_of_pos_right x hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hxδ
      refine ⟨z, hz1, ?_⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hz1)]
      exact sub_left_lt_of_lt_add hz2
    obtain ⟨z, h_x_lt_z, hxz⟩ := this
    -- then dist (f z) (f y) < ε.
    have hbzb := hδ z hxz
    rw [← h z] at hbzb
    have huzuy : u z < u x := by
      have hufp : 0 < u x - f x := by linarith
      have hua : ε = u x - f x := abs_of_pos hufp
      rw [hua, Real.dist_eq] at hbzb
      cases em (f x < u z)
      · have : 0 ≤ u z - f x := by linarith
        rw[abs_eq_self.mpr this] at hbzb
        linarith
      · linarith
    -- so u(z) < u(x), contradicting u_mono.
    have := u_mono x z xpos.le h_x_lt_z.le
    linarith

abbrev SolutionSet : Set (ℝ → ℝ) :=
  { fun x ↦ 0, fun x ↦ 1/2, fun x ↦ x^2 }

end Imo2002P5
