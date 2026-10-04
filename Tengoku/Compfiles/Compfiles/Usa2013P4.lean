/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2013, Problem 4

Find all real numbers x, y, z ≥ 1 satisfying

  min(√(x + xyz), √(y + xyz), √(z + xyz)) = √(x - 1) + √(y - 1) + √(z - 1).
-/

namespace Usa2013P4

open Real

/-- The condition that `x` is the "distinguished" coordinate of a solution
(the coordinate at which the minimum of the left-hand side is attained):
the other two shifted coordinates `y - 1`, `z - 1` multiply to `1`, and
`x - 1` is the reciprocal of `(√(y - 1) + √(z - 1))²`. -/
def Distinguished (x y z : ℝ) : Prop :=
  (y - 1) * (z - 1) = 1 ∧ (x - 1) * (√(y - 1) + √(z - 1)) ^ 2 = 1

/-!
### Proof sketch

We follow the solution in Evan Chen's USAMO 2013 notes
(https://web.evanchen.cc/exams/USAMO-2013-notes.pdf).
Substitute `x = 1 + u`, `y = 1 + v`, `z = 1 + w` with `u, v, w ≥ 0`.
Then `x + xyz = (1 + u)(1 + (1 + v)(1 + w))`, and the key identity

  (1+u)(1+(1+v)(1+w)) - (√u + √v + √w)²
    = (√u·(√v+√w) - 1)² + (1+u)·(√v·√w - 1)²

shows that the square of every term on the left-hand side is at least the
square of the right-hand side, with equality iff `v·w = 1` and
`u·(√v + √w)² = 1`. These conditions force `u ≤ v` and `u ≤ w`, so the
solution set is as described.
-/

/-- The key algebraic identity: the difference between `(1+u)(1+(1+v)(1+w))`
and `(√u + √v + √w)²` is a sum of two squares. -/
lemma key_identity (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (1 + u) * (1 + (1 + v) * (1 + w)) - (√u + √v + √w) ^ 2 =
      (√u * (√v + √w) - 1) ^ 2 + (1 + u) * (√v * √w - 1) ^ 2 := by
  have e1 : (√u + √v + √w) ^ 2
      = √u ^ 2 + √v ^ 2 + √w ^ 2 + 2 * (√u * √v + √u * √w + √v * √w) := by ring
  have e2 : (√u * (√v + √w) - 1) ^ 2
      = √u ^ 2 * (√v + √w) ^ 2 - 2 * (√u * √v + √u * √w) + 1 := by ring
  have e3 : (√v + √w) ^ 2 = √v ^ 2 + √w ^ 2 + 2 * (√v * √w) := by ring
  have e4 : (√v * √w - 1) ^ 2 = (√v * √w) ^ 2 - 2 * (√v * √w) + 1 := by ring
  have hvw : (√v * √w) ^ 2 = v * w := by rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hw]
  rw [e1, e2, e3, e4, hvw, Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sq_sqrt hw]
  ring

/-- Equality conditions: if `(1+u)(1+(1+v)(1+w)) = (√u + √v + √w)²` for
nonnegative `u, v, w`, then `v * w = 1` and `u * (√v + √w)² = 1`. -/
lemma eq_conds {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : (1 + u) * (1 + (1 + v) * (1 + w)) = (√u + √v + √w) ^ 2) :
    v * w = 1 ∧ u * (√v + √w) ^ 2 = 1 := by
  have hid := key_identity u v w hu hv hw
  rw [h, sub_self] at hid
  have hnn1 : 0 ≤ (√u * (√v + √w) - 1) ^ 2 := sq_nonneg _
  have hnn2 : 0 ≤ (1 + u) * (√v * √w - 1) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hA : (√u * (√v + √w) - 1) ^ 2 = 0 := by linarith
  have hB : (1 + u) * (√v * √w - 1) ^ 2 = 0 := by linarith
  have hvw1 : v * w = 1 := by
    have h1 : (√v * √w - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hB with h0 | h0
      · linarith
      · exact h0
    have h2 : √v * √w = 1 := by
      have h3 := sq_eq_zero_iff.mp h1
      linarith
    have h4 : (√v * √w) ^ 2 = v * w := by
      rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hw]
    rw [h2, one_pow] at h4
    exact h4.symm
  have hus1 : u * (√v + √w) ^ 2 = 1 := by
    have h1 : √u * (√v + √w) = 1 := by
      have h2 := sq_eq_zero_iff.mp hA
      linarith
    have h3 : (√u * (√v + √w)) ^ 2 = u * (√v + √w) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hu]
    rw [← h3, h1, one_pow]
  exact ⟨hvw1, hus1⟩

/-- The conditions `v * w = 1` and `u * (√v + √w)² = 1` imply the equation,
with the minimum attained at the term corresponding to `u`. -/
lemma min_eq_of_conds {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h1 : v * w = 1) (h2 : u * (√v + √w) ^ 2 = 1) :
    min (min (√((1 + u) * (1 + (1 + v) * (1 + w))))
            (√((1 + v) * (1 + (1 + u) * (1 + w)))))
        (√((1 + w) * (1 + (1 + u) * (1 + v)))) = √u + √v + √w := by
  have hvw : √v * √w = 1 := by rw [← Real.sqrt_mul hv, h1, Real.sqrt_one]
  have hs_nonneg : 0 ≤ √v + √w := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hS_nonneg : 0 ≤ √u + √v + √w := by positivity
  have hs2_pos : 0 < (√v + √w) ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h0 : (√v + √w) ^ 2 = 0 := le_antisymm hcon (sq_nonneg _)
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  -- `√u * (√v + √w) = 1`, since its square is `1` and it is nonnegative
  have hus : √u * (√v + √w) = 1 := by
    have h3 : (√u * (√v + √w)) ^ 2 = 1 := by
      have h4 : (√u * (√v + √w)) ^ 2 = u * (√v + √w) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hu]
      rw [h4, h2]
    have h5 : 0 ≤ √u * (√v + √w) := mul_nonneg (Real.sqrt_nonneg _) hs_nonneg
    rcases sq_eq_one_iff.mp h3 with h6 | h6
    · exact h6
    · linarith
  -- the squared equation holds
  have hf_eq : (1 + u) * (1 + (1 + v) * (1 + w)) = (√u + √v + √w) ^ 2 := by
    have hid := key_identity u v w hu hv hw
    rw [hus, hvw] at hid
    linear_combination hid
  -- hence the `u`-term equals the right-hand side
  have hg_u : √((1 + u) * (1 + (1 + v) * (1 + w))) = √u + √v + √w := by
    rw [hf_eq, Real.sqrt_sq hS_nonneg]
  -- `u` is the minimum of `u, v, w`
  have e3 : (√v + √w) ^ 2 = v + w + 2 * (√v * √w) := by
    rw [add_sq, Real.sq_sqrt hv, Real.sq_sqrt hw]
    ring
  have huv : u ≤ v := by
    have hv_s : v * (√v + √w) ^ 2 = (v + 1) ^ 2 := by
      rw [e3, hvw]
      linear_combination h1
    have hle : u * (√v + √w) ^ 2 ≤ v * (√v + √w) ^ 2 := by
      rw [h2, hv_s]
      nlinarith [sq_nonneg v, hv]
    exact le_of_mul_le_mul_right hle hs2_pos
  have huw : u ≤ w := by
    have hw_s : w * (√v + √w) ^ 2 = (w + 1) ^ 2 := by
      rw [e3, hvw]
      have h1' : w * v = 1 := by rw [mul_comm]; exact h1
      linear_combination h1'
    have hle : u * (√v + √w) ^ 2 ≤ w * (√v + √w) ^ 2 := by
      rw [h2, hw_s]
      nlinarith [sq_nonneg w, hw]
    exact le_of_mul_le_mul_right hle hs2_pos
  -- therefore the minimum of the three terms is the `u`-term
  have hdiff_v : (1 + v) * (1 + (1 + u) * (1 + w)) -
      (1 + u) * (1 + (1 + v) * (1 + w)) = v - u := by ring
  have hdiff_w : (1 + w) * (1 + (1 + u) * (1 + v)) -
      (1 + u) * (1 + (1 + v) * (1 + w)) = w - u := by ring
  have hle_gv : √((1 + u) * (1 + (1 + v) * (1 + w)))
      ≤ √((1 + v) * (1 + (1 + u) * (1 + w))) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hle_gw : √((1 + u) * (1 + (1 + v) * (1 + w)))
      ≤ √((1 + w) * (1 + (1 + u) * (1 + v))) := by
    apply Real.sqrt_le_sqrt
    linarith
  rw [min_eq_left hle_gv, min_eq_left hle_gw, hg_u]

/-- Backward direction for one distinguished coordinate: the conditions
`v * w = 1` and `u * (√v + √w)² = 1` imply `u, v, w > 0` and the equation. -/
lemma solution_of_conds {u v w : ℝ} (h1 : v * w = 1)
    (h2 : u * (√v + √w) ^ 2 = 1) :
    1 < 1 + u ∧ 1 < 1 + v ∧ 1 < 1 + w ∧
      min (min (√((1 + u) * (1 + (1 + v) * (1 + w))))
              (√((1 + v) * (1 + (1 + u) * (1 + w)))))
          (√((1 + w) * (1 + (1 + u) * (1 + v)))) = √u + √v + √w := by
  have hs_ne : √v + √w ≠ 0 := by
    intro hs
    rw [hs] at h2
    norm_num at h2
  have hv_pos : 0 < v := by
    by_contra hv'
    push Not at hv'
    have hsv : √v = 0 := Real.sqrt_eq_zero_of_nonpos hv'
    have hw_neg : w < 0 := by
      by_contra hw'
      push Not at hw'
      have hle : v * w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv' hw'
      linarith [h1]
    have hsw : √w = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hw_neg)
    exact hs_ne (by rw [hsv, hsw, add_zero])
  have hw_pos : 0 < w := by
    by_contra hw'
    push Not at hw'
    have hsw : √w = 0 := Real.sqrt_eq_zero_of_nonpos hw'
    have hv_neg : v < 0 := by
      by_contra hv''
      push Not at hv''
      have hle : v * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv'' hw'
      linarith [h1]
    have hsv : √v = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hv_neg)
    exact hs_ne (by rw [hsv, hsw, add_zero])
  have hu_pos : 0 < u := by
    have hs2_pos : 0 < (√v + √w) ^ 2 := by positivity
    by_contra hu'
    push Not at hu'
    have hle : u * (√v + √w) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu' (sq_nonneg _)
    linarith [h2]
  exact ⟨by linarith, by linarith, by linarith,
    min_eq_of_conds (le_of_lt hu_pos) (le_of_lt hv_pos) (le_of_lt hw_pos) h1 h2⟩

lemma min_swap12 (a b c : ℝ) : min (min a b) c = min (min b a) c := by
  rw [min_comm a b]

lemma min_rotate (a b c : ℝ) : min (min a b) c = min (min b c) a := by
  rw [min_comm (min b c) a, ← min_assoc]

abbrev solution_set : Set (ℝ × ℝ × ℝ) :=
  { p : ℝ × ℝ × ℝ |
      Distinguished p.1 p.2.1 p.2.2 ∨ Distinguished p.2.1 p.1 p.2.2 ∨
        Distinguished p.2.2 p.1 p.2.1 }

end Usa2013P4
