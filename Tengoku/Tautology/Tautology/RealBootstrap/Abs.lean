import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra

/-!
# The absolute value

`abs` by case split on sign, and everything the rest of the library asks of it:
the two triangle inequalities, multiplicativity, the reverse triangle
inequality, the characterisation by two-sided bounds, and vanishing exactly at
zero.

These are among the most consumed statements in the library: the names declared
here appear about 3800 times across 172 files. Every epsilon argument --
limits, continuity, integrals -- is written in terms of `abs`, and the metric
of `Tautology.RealTopology.Basic` is defined as `abs` of a difference, so the
metric axioms proved there are one-line restatements of the facts here.

## Position and role

Implementation module over an arbitrary ordered field, built directly on
`Tautology.RealBootstrap.OrderAlgebra`. No completeness is involved at any
point.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The absolute value by a case split on sign: `x` itself when `0 ≤ x`, its
negation otherwise. The case split is classical rather than decidable, which
is why the definition is marked `noncomputable`. -/
noncomputable def abs (x : alpha) : alpha := by
  classical
  exact if F.le F.zero x then x else F.neg x

theorem nonpos_of_not_nonneg {x : alpha}
    (h : Not (F.le F.zero x)) :
    F.le x F.zero := by
  cases F.le_total F.zero x with
  | inl h0x =>
      exact False.elim (h h0x)
  | inr hx0 =>
      exact hx0

theorem neg_nonneg_of_nonpos {x : alpha}
    (hx : F.le x F.zero) :
    F.le F.zero (F.neg x) := by
  have h := F.add_le_add_right hx (F.neg x)
  rwa [F.add_neg, F.zero_add] at h

theorem neg_nonpos_of_nonneg {x : alpha}
    (hx : F.le F.zero x) :
    F.le (F.neg x) F.zero := by
  have h := F.add_le_add_right hx (F.neg x)
  rwa [F.zero_add, F.add_neg] at h

theorem nonpos_of_neg_nonneg {x : alpha}
    (hx : F.le F.zero (F.neg x)) :
    F.le x F.zero := by
  have h := F.add_le_add_right hx x
  rwa [F.zero_add, F.neg_add] at h

theorem nonneg_of_neg_nonpos {x : alpha}
    (hx : F.le (F.neg x) F.zero) :
    F.le F.zero x := by
  have h := F.add_le_add_right hx x
  rwa [F.neg_add, F.zero_add] at h

theorem abs_of_nonneg {x : alpha}
    (hx : F.le F.zero x) :
    abs F x = x := by
  unfold abs
  simp [hx]

theorem abs_of_nonpos {x : alpha}
    (hx : F.le x F.zero) :
    abs F x = F.neg x := by
  unfold abs
  by_cases h0x : F.le F.zero x
  · have hx0 : x = F.zero := F.le_antisymm hx h0x
    rw [ite_eq_left h0x, hx0, neg_zero F]
  · simp [h0x]

theorem abs_zero :
    abs F F.zero = F.zero := by
  exact abs_of_nonneg F (F.le_refl F.zero)

theorem abs_one :
    abs F F.one = F.one := by
  exact abs_of_nonneg F (le_of_lt F (zero_lt_one F))

theorem abs_nonneg (x : alpha) :
    F.le F.zero (abs F x) := by
  by_cases hx : F.le F.zero x
  · rw [abs_of_nonneg F hx]
    exact hx
  · rw [abs_of_nonpos F (nonpos_of_not_nonneg F hx)]
    exact neg_nonneg_of_nonpos F (nonpos_of_not_nonneg F hx)

theorem abs_add_one_pos (x : alpha) :
    F.lt F.zero (F.add (abs F x) F.one) := by
  have hstep : F.lt (abs F x) (F.add (abs F x) F.one) := by
    have h := add_lt_add_left F (zero_lt_one F) (abs F x)
    rwa [F.add_zero] at h
  exact lt_of_le_of_lt F (abs_nonneg F x) hstep

theorem abs_neg (x : alpha) :
    abs F (F.neg x) = abs F x := by
  by_cases hx : F.le F.zero x
  · have hnx : F.le (F.neg x) F.zero :=
      neg_nonpos_of_nonneg F hx
    rw [abs_of_nonpos F hnx]
    rw [neg_neg F x]
    rw [abs_of_nonneg F hx]
  · have hx0 : F.le x F.zero :=
      nonpos_of_not_nonneg F hx
    have h0nx : F.le F.zero (F.neg x) :=
      neg_nonneg_of_nonpos F hx0
    rw [abs_of_nonneg F h0nx]
    rw [abs_of_nonpos F hx0]

theorem le_abs_self (x : alpha) :
    F.le x (abs F x) := by
  by_cases hx : F.le F.zero x
  · rw [abs_of_nonneg F hx]
    exact F.le_refl x
  · have hx0 : F.le x F.zero :=
      nonpos_of_not_nonneg F hx
    exact F.le_trans hx0 (abs_nonneg F x)

theorem neg_le_abs_self (x : alpha) :
    F.le (F.neg x) (abs F x) := by
  by_cases hx : F.le F.zero x
  · rw [abs_of_nonneg F hx]
    exact F.le_trans (neg_nonpos_of_nonneg F hx) hx
  · have hx0 : F.le x F.zero :=
      nonpos_of_not_nonneg F hx
    rw [abs_of_nonpos F hx0]
    exact F.le_refl (F.neg x)

/-- A common upper bound on `x` and on `-x` is already an upper bound on
`|x|`. Both triangle bounds below close through it, each supplying the two
one-sided estimates as hypotheses. -/
theorem abs_le_of_bounds {x b : alpha}
    (hxb : F.le x b)
    (hnxb : F.le (F.neg x) b) :
    F.le (abs F x) b := by
  by_cases hx : F.le F.zero x
  · rwa [abs_of_nonneg F hx]
  · have hx0 : F.le x F.zero :=
      nonpos_of_not_nonneg F hx
    rwa [abs_of_nonpos F hx0]

/-- The triangle inequality. It is the most consumed statement of this module:
the library's epsilon arguments bound an error by a sum of errors through it,
directly or through the waist re-export in `Tautology.RealTheory.Abs`. -/
theorem abs_add_le_abs_add_abs (x y : alpha) :
    F.le (abs F (F.add x y)) (F.add (abs F x) (abs F y)) := by
  apply abs_le_of_bounds F
  · exact add_le_add F (le_abs_self F x) (le_abs_self F y)
  · rw [neg_add_distrib F x y]
    exact add_le_add F (neg_le_abs_self F x) (neg_le_abs_self F y)

/-- The triangle inequality in its two-error form: the deviation of a paired
sum `x + y` from `I + J` is bounded by the sum of the separate deviations of
the two terms. -/
theorem abs_add_sub_add_le_abs_sub_add_abs_sub
    (x y I J : alpha) :
    F.le
      (abs F (F.sub (F.add x y) (F.add I J)))
      (F.add (abs F (F.sub x I)) (abs F (F.sub y J))) := by
  rw [add_sub_add_eq_sub_add_sub F]
  exact abs_add_le_abs_add_abs F (F.sub x I) (F.sub y J)

theorem abs_mul (x y : alpha) :
    abs F (F.mul x y) = F.mul (abs F x) (abs F y) := by
  by_cases hx : F.le F.zero x
  · by_cases hy : F.le F.zero y
    · have hxy : F.le F.zero (F.mul x y) :=
        F.mul_nonneg hx hy
      rw [abs_of_nonneg F hx]
      rw [abs_of_nonneg F hy]
      rw [abs_of_nonneg F hxy]
    · have hy0 : F.le y F.zero :=
        nonpos_of_not_nonneg F hy
      have hny : F.le F.zero (F.neg y) :=
        neg_nonneg_of_nonpos F hy0
      have hnegprod : F.le F.zero (F.neg (F.mul x y)) := by
        have hprod : F.le F.zero (F.mul x (F.neg y)) :=
          F.mul_nonneg hx hny
        rwa [F.mul_neg] at hprod
      have hprod0 : F.le (F.mul x y) F.zero :=
        nonpos_of_neg_nonneg F hnegprod
      rw [abs_of_nonneg F hx]
      rw [abs_of_nonpos F hy0]
      rw [abs_of_nonpos F hprod0]
      rw [F.mul_neg]
  · have hx0 : F.le x F.zero :=
      nonpos_of_not_nonneg F hx
    have hnx : F.le F.zero (F.neg x) :=
      neg_nonneg_of_nonpos F hx0
    by_cases hy : F.le F.zero y
    · have hnegprod : F.le F.zero (F.neg (F.mul x y)) := by
        have hprod : F.le F.zero (F.mul (F.neg x) y) :=
          F.mul_nonneg hnx hy
        rwa [F.neg_mul] at hprod
      have hprod0 : F.le (F.mul x y) F.zero :=
        nonpos_of_neg_nonneg F hnegprod
      rw [abs_of_nonpos F hx0]
      rw [abs_of_nonneg F hy]
      rw [abs_of_nonpos F hprod0]
      rw [F.neg_mul]
    · have hy0 : F.le y F.zero :=
        nonpos_of_not_nonneg F hy
      have hny : F.le F.zero (F.neg y) :=
        neg_nonneg_of_nonpos F hy0
      have hprod : F.le F.zero (F.mul x y) := by
        have hprod' : F.le F.zero (F.mul (F.neg x) (F.neg y)) :=
          F.mul_nonneg hnx hny
        rwa [F.neg_mul_neg] at hprod'
      rw [abs_of_nonpos F hx0]
      rw [abs_of_nonpos F hy0]
      rw [abs_of_nonneg F hprod]
      rw [F.neg_mul_neg]

theorem abs_sub_comm (x y : alpha) :
    abs F (F.sub x y) = abs F (F.sub y x) := by
  rw [sub_rev_eq_neg_sub F y x]
  rw [abs_neg F (F.sub y x)]

/-- The reverse triangle inequality, `||x| - |y|| ≤ |x - y|`. It bounds a
difference of absolute values by a distance, and is consumed above through
the waist re-export `Tautology.RealTheory.Abs`. -/
theorem abs_abs_sub_abs_le_abs_sub (x y : alpha) :
    F.le
      (abs F (F.sub (abs F x) (abs F y)))
      (abs F (F.sub x y)) := by
  have hxyTriangle := abs_add_le_abs_add_abs F (F.sub x y) y
  change
    F.le
      (F.abs (F.add (F.sub x y) y))
      (F.add (F.abs (F.sub x y)) (F.abs y)) at hxyTriangle
  rw [F.sub_add_cancel] at hxyTriangle
  have hupper := F.sub_le_sub_of_le_of_le
    hxyTriangle (F.le_refl (F.abs y))
  change
    F.le
      (F.sub (F.abs x) (F.abs y))
      (F.sub
        (F.add (F.abs (F.sub x y)) (F.abs y)) (F.abs y)) at hupper
  rw [F.add_sub_cancel] at hupper
  have hyxTriangle := abs_add_le_abs_add_abs F (F.sub y x) x
  change
    F.le
      (F.abs (F.add (F.sub y x) x))
      (F.add (F.abs (F.sub y x)) (F.abs x)) at hyxTriangle
  rw [F.sub_add_cancel] at hyxTriangle
  have hreverse := F.sub_le_sub_of_le_of_le
    hyxTriangle (F.le_refl (F.abs x))
  change
    F.le
      (F.sub (F.abs y) (F.abs x))
      (F.sub
        (F.add (F.abs (F.sub y x)) (F.abs x)) (F.abs x)) at hreverse
  rw [F.add_sub_cancel] at hreverse
  rw [abs_sub_comm F y x] at hreverse
  have hlower :
      F.le
        (F.neg (F.sub (F.abs x) (F.abs y)))
        (F.abs (F.sub x y)) := by
    rw [<- F.sub_rev_eq_neg_sub (F.abs x) (F.abs y)]
    exact hreverse
  exact abs_le_of_bounds F hupper hlower

theorem abs_eq_zero_of_eq_zero {x : alpha}
    (hx : x = F.zero) :
    abs F x = F.zero := by
  rw [hx]
  exact abs_zero F

theorem eq_zero_of_abs_eq_zero {x : alpha}
    (hx : abs F x = F.zero) :
    x = F.zero := by
  by_cases h0x : F.le F.zero x
  · rwa [abs_of_nonneg F h0x] at hx
  · have hx0 : F.le x F.zero :=
      nonpos_of_not_nonneg F h0x
    have hneg : F.neg x = F.zero := by
      rwa [abs_of_nonpos F hx0] at hx
    calc
      x = F.neg (F.neg x) := by rw [neg_neg F x]
      _ = F.neg F.zero := by rw [hneg]
      _ = F.zero := neg_zero F

theorem abs_eq_zero_iff {x : alpha} :
    abs F x = F.zero <-> x = F.zero :=
  Iff.intro
    (eq_zero_of_abs_eq_zero F)
    (abs_eq_zero_of_eq_zero F)

theorem abs_pos_of_ne_zero {x : alpha}
    (hx : Not (x = F.zero)) :
    F.lt F.zero (abs F x) := by
  apply lt_of_le_of_not_le F
  · exact abs_nonneg F x
  · intro hle
    have hzero : abs F x = F.zero :=
      F.le_antisymm hle (abs_nonneg F x)
    exact hx ((abs_eq_zero_iff F).mp hzero)

/-- Moves an error committed in a quotient onto the dividend: the deviation
of `A * (1/d)` from `c` equals the remainder `A - c * d` scaled by `1/d`.
The difference-quotient bookkeeping of the Riemann fundamental theorem in
`Tautology.RealIntegral.Riemann.Proper.FundamentalTheorem` runs on it. -/
theorem quotient_error_eq_remainder_mul_inv
    {A c d : alpha}
    (hd : Not (d = F.zero)) :
    F.sub (F.mul A (F.inv d)) c =
      F.mul (F.sub A (F.mul c d)) (F.inv d) := by
  have hc : F.mul (F.mul c d) (F.inv d) = c := by
    calc
      F.mul (F.mul c d) (F.inv d) =
          F.mul c (F.mul d (F.inv d)) := by
            rw [F.mul_assoc]
      _ = F.mul c F.one := by rw [F.mul_inv_cancel hd]
      _ = c := by rw [F.mul_one]
  calc
    F.sub (F.mul A (F.inv d)) c =
        F.sub (F.mul A (F.inv d))
          (F.mul (F.mul c d) (F.inv d)) := by rw [hc]
    _ = F.mul (F.sub A (F.mul c d)) (F.inv d) := by
      exact Eq.symm
        (sub_mul_eq_sub_mul F A (F.mul c d) (F.inv d))

theorem abs_mul_inv_le_of_abs_le_mul_abs
    {R M d : alpha}
    (hd : Not (d = F.zero))
    (hR : F.le (abs F R) (F.mul M (abs F d))) :
    F.le (abs F (F.mul R (F.inv d))) M := by
  have hden_pos : F.lt F.zero (abs F d) :=
    abs_pos_of_ne_zero F hd
  have hprod_eq :
      F.mul (abs F (F.mul R (F.inv d))) (abs F d) =
        abs F R := by
    rw [<- abs_mul F (F.mul R (F.inv d)) d]
    have hcancel : F.mul (F.mul R (F.inv d)) d = R := by
      calc
        F.mul (F.mul R (F.inv d)) d =
            F.mul R (F.mul (F.inv d) d) := by rw [F.mul_assoc]
        _ = F.mul R F.one := by rw [F.inv_mul_cancel hd]
        _ = R := by rw [F.mul_one]
    rw [hcancel]
  have hmul_le :
      F.le
        (F.mul (abs F (F.mul R (F.inv d))) (abs F d))
        (F.mul M (abs F d)) := by
    rw [hprod_eq]
    exact hR
  by_cases hle : F.le (abs F (F.mul R (F.inv d))) M
  case pos => exact hle
  case neg =>
    have hMle : F.le M (abs F (F.mul R (F.inv d))) := by
      cases F.le_total M (abs F (F.mul R (F.inv d))) with
      | inl h => exact h
      | inr h => exact False.elim (hle h)
    have hMlt : F.lt M (abs F (F.mul R (F.inv d))) :=
      lt_of_le_of_not_le F hMle hle
    have hstrict := mul_lt_mul_pos_right F hMlt hden_pos
    exact False.elim ((not_le_of_lt F hstrict) hmul_le)

theorem abs_sub_self (x : alpha) :
    abs F (F.sub x x) = F.zero := by
  rw [sub_self F x]
  exact abs_zero F

theorem abs_sub_lt_of_two_sided_sub_lt
    {x I eps : alpha}
    (hupper : F.lt (F.sub x I) eps)
    (hlower : F.lt (F.sub I x) eps) :
    F.lt (abs F (F.sub x I)) eps := by
  by_cases hnonneg : F.le F.zero (F.sub x I)
  case pos =>
    rw [abs_of_nonneg F hnonneg]
    exact hupper
  case neg =>
    have hnonpos : F.le (F.sub x I) F.zero :=
      nonpos_of_not_nonneg F hnonneg
    rw [abs_of_nonpos F hnonpos]
    rwa [sub_rev_eq_neg_sub F x I] at hlower

theorem lt_left_add_of_abs_sub_lt
    {x I eps : alpha}
    (h : F.lt (abs F (F.sub x I)) eps) :
    F.lt I (F.add x eps) := by
  have hsym : F.lt (abs F (F.sub I x)) eps := by
    rwa [abs_sub_comm F I x]
  have hsub : F.lt (F.sub I x) eps :=
    lt_of_le_of_lt F (le_abs_self F (F.sub I x)) hsym
  exact lt_add_of_sub_lt F hsub

theorem lt_right_add_of_abs_sub_lt
    {x I eps : alpha}
    (h : F.lt (abs F (F.sub x I)) eps) :
    F.lt x (F.add I eps) := by
  have hsub : F.lt (F.sub x I) eps :=
    lt_of_le_of_lt F (le_abs_self F (F.sub x I)) h
  exact lt_add_of_sub_lt F hsub

/-- A fixed constant can always be scaled inside a positive bound: some
positive `eta` makes `|c| * eta < eps`. This is the absorption step the
epsilon arguments above quote when an estimate carries a constant factor. -/
theorem exists_pos_eta_abs_mul_lt
    (c : alpha) {eps : alpha}
    (heps : F.lt F.zero eps) :
    Exists
      (fun eta : alpha =>
        And (F.lt F.zero eta)
          (F.lt (F.mul (abs F c) eta) eps)) := by
  let C := abs F c
  by_cases hC_zero : C = F.zero
  case pos =>
    refine Exists.intro F.one ?_
    refine And.intro F.zero_lt_one ?_
    change F.lt (F.mul C F.one) eps
    rw [hC_zero, F.zero_mul]
    exact heps
  case neg =>
    let e2 := half F eps
    let eta := F.mul e2 (F.inv C)
    have he2_pos : F.lt F.zero e2 :=
      half_pos F heps
    have he2_lt_eps : F.lt e2 eps := by
      have h := add_lt_add_left F he2_pos e2
      change F.lt (F.add e2 F.zero) (F.add e2 e2) at h
      rwa [F.add_zero, half_add_half F eps] at h
    have hc_ne : Not (c = F.zero) := by
      intro hc
      exact hC_zero (abs_eq_zero_of_eq_zero F hc)
    have hC_pos : F.lt F.zero C :=
      abs_pos_of_ne_zero F hc_ne
    have hinv_pos : F.lt F.zero (F.inv C) :=
      inv_pos F hC_pos
    refine Exists.intro eta ?_
    refine And.intro (F.mul_pos he2_pos hinv_pos) ?_
    have hC_eta : F.mul C eta = e2 := by
      dsimp [eta]
      calc
        F.mul C (F.mul e2 (F.inv C)) =
            F.mul (F.mul C e2) (F.inv C) := by
              rw [<- F.mul_assoc]
        _ = F.mul (F.mul e2 C) (F.inv C) := by
              rw [F.mul_comm C e2]
        _ = F.mul e2 (F.mul C (F.inv C)) := by
              rw [F.mul_assoc]
        _ = F.mul e2 F.one := by
              rw [F.mul_inv_cancel hC_zero]
        _ = e2 := by
              rw [F.mul_one]
    change F.lt (F.mul C eta) eps
    rw [hC_eta]
    exact he2_lt_eps

end IsOrderedFieldBaseLike
end Tautology
