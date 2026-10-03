import Tengoku.Tautology.Tautology.RealBootstrap.PositiveOne

/-!
# The order-arithmetic core, and the constants two, half and quarter

The first half of the order-compatible arithmetic: adding to both sides of an
inequality, moving terms across it, positivity of products and inverses, and
then the small constants that every epsilon argument in the library is written
with -- `two`, `half`, `quarter`, with the facts that they are positive and
that two halves rejoin.

Splitting these off from `Tautology.RealBootstrap.OrderAlgebra` is what lets
the absolute value be defined without a cycle: `abs` needs the order
arithmetic, and the order arithmetic proper needs nothing from `abs`.

## Position and role

Implementation module over an arbitrary ordered field, imported by
`Tautology.RealBootstrap.OrderAlgebra` immediately above it.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem add_le_add_left {x y : alpha}
    (hxy : F.le x y) (z : alpha) :
    F.le (F.add z x) (F.add z y) := by
  rw [F.add_comm z x, F.add_comm z y]
  exact F.add_le_add_right hxy z

theorem add_le_add {w x y z : alpha}
    (hwx : F.le w x) (hyz : F.le y z) :
    F.le (F.add w y) (F.add x z) := by
  exact F.le_trans
    (F.add_le_add_right hwx y)
    (add_le_add_left F hyz x)

theorem sub_add_cancel (x y : alpha) :
    F.add (F.sub x y) y = x := by
  rw [F.sub_eq_add_neg]
  calc
    F.add (F.add x (F.neg y)) y =
        F.add x (F.add (F.neg y) y) := by rw [F.add_assoc]
    _ = F.add x F.zero := by rw [F.neg_add]
    _ = x := by rw [F.add_zero]

theorem add_sub_cancel (x y : alpha) :
    F.sub (F.add x y) y = x := by
  rw [F.sub_eq_add_neg]
  exact add_neg_cancel_right F x y

theorem sub_neg_neg_eq_neg_sub (x y : alpha) :
    F.sub (F.neg x) (F.neg y) = F.neg (F.sub x y) := by
  rw [F.sub_eq_add_neg]
  rw [neg_neg F y]
  rw [F.sub_eq_add_neg x y]
  rw [neg_add_distrib F x (F.neg y)]
  rw [neg_neg F y]

theorem sub_rev_eq_neg_sub (x y : alpha) :
    F.sub y x = F.neg (F.sub x y) := by
  rw [F.sub_eq_add_neg y x]
  rw [F.sub_eq_add_neg x y]
  rw [neg_add_distrib F x (F.neg y)]
  rw [neg_neg F y]
  rw [F.add_comm y (F.neg x)]

theorem add_sub_add_eq_sub_add_sub (x y a b : alpha) :
    F.sub (F.add x y) (F.add a b) =
      F.add (F.sub x a) (F.sub y b) := by
  rw [F.sub_eq_add_neg]
  rw [neg_add_distrib F a b]
  rw [F.sub_eq_add_neg x a]
  rw [F.sub_eq_add_neg y b]
  have hinner :
      F.add y (F.add (F.neg a) (F.neg b)) =
        F.add (F.neg a) (F.add y (F.neg b)) := by
    calc
      F.add y (F.add (F.neg a) (F.neg b)) =
          F.add (F.add y (F.neg a)) (F.neg b) := by
            rw [<- F.add_assoc]
      _ = F.add (F.add (F.neg a) y) (F.neg b) := by
            rw [F.add_comm y (F.neg a)]
      _ = F.add (F.neg a) (F.add y (F.neg b)) := by
            rw [F.add_assoc]
  calc
    F.add (F.add x y) (F.add (F.neg a) (F.neg b)) =
        F.add x (F.add y (F.add (F.neg a) (F.neg b))) := by
          rw [F.add_assoc]
    _ = F.add x (F.add (F.neg a) (F.add y (F.neg b))) := by
          rw [hinner]
    _ = F.add (F.add x (F.neg a)) (F.add y (F.neg b)) := by
          rw [<- F.add_assoc]

theorem neg_one_lt_zero : F.lt (F.neg F.one) F.zero := by
  have h := add_lt_add_right F (zero_lt_one F) (F.neg F.one)
  rwa [F.zero_add, F.add_neg] at h

theorem sub_nonneg_of_le {x y : alpha}
    (hxy : F.le x y) :
    F.le F.zero (F.sub y x) := by
  have h := F.add_le_add_right hxy (F.neg x)
  rwa [F.add_neg, <- F.sub_eq_add_neg y x] at h

theorem le_of_sub_nonneg {x y : alpha}
    (h : F.le F.zero (F.sub y x)) :
    F.le x y := by
  have h' := F.add_le_add_right h x
  rwa [F.zero_add, sub_add_cancel F y x] at h'

theorem lt_add_of_sub_lt {x a eps : alpha}
    (h : F.lt (F.sub x a) eps) :
    F.lt x (F.add a eps) := by
  have h' := add_lt_add_right F h a
  have hright : F.add eps a = F.add a eps := F.add_comm eps a
  rwa [sub_add_cancel F x a, hright] at h'

theorem neg_le_neg {x y : alpha}
    (hxy : F.le x y) :
    F.le (F.neg y) (F.neg x) := by
  have hdiff : F.le F.zero (F.sub y x) :=
    sub_nonneg_of_le F hxy
  apply le_of_sub_nonneg F
  rwa [sub_neg_neg_eq_neg_sub F x y, <- sub_rev_eq_neg_sub F x y]

theorem sub_le_sub_of_le_of_le {x y a b : alpha}
    (hxb : F.le x b)
    (hay : F.le a y) :
    F.le (F.sub x y) (F.sub b a) := by
  rw [F.sub_eq_add_neg x y, F.sub_eq_add_neg b a]
  exact add_le_add F hxb (neg_le_neg F hay)

theorem mul_pos {x y : alpha}
    (hx : F.lt F.zero x) (hy : F.lt F.zero y) :
    F.lt F.zero (F.mul x y) := by
  have hnonneg : F.le F.zero (F.mul x y) :=
    F.mul_nonneg (le_of_lt F hx) (le_of_lt F hy)
  apply lt_of_le_of_not_le F hnonneg
  intro hle0
  have hzero : F.mul x y = F.zero :=
    F.le_antisymm hle0 hnonneg
  cases mul_eq_zero_cases F hzero with
  | inl hx0 =>
      exact ne_of_lt F hx hx0.symm
  | inr hy0 =>
      exact ne_of_lt F hy hy0.symm

theorem inv_pos {x : alpha}
    (hx : F.lt F.zero x) :
    F.lt F.zero (F.inv x) := by
  have hxne : Not (x = F.zero) := by
    intro h
    exact ne_of_lt F hx h.symm
  have h0x : F.le F.zero x := le_of_lt F hx
  have hle0inv : F.le F.zero (F.inv x) := by
    by_cases h : F.le F.zero (F.inv x)
    · exact h
    · have hinv0 : F.le (F.inv x) F.zero := by
        cases F.le_total (F.inv x) F.zero with
        | inl hle => exact hle
        | inr h0inv => exact False.elim (h h0inv)
      have hneg_nonneg : F.le F.zero (F.neg (F.inv x)) := by
        have h' := F.add_le_add_right hinv0 (F.neg (F.inv x))
        rwa [F.add_neg, F.zero_add] at h'
      have hprod_nonneg :
          F.le F.zero (F.mul x (F.neg (F.inv x))) :=
        F.mul_nonneg h0x hneg_nonneg
      have hprod :
          F.mul x (F.neg (F.inv x)) = F.neg F.one := by
        rw [mul_neg F, F.mul_inv_cancel hxne]
      have hnegone_nonneg : F.le F.zero (F.neg F.one) := by
        rwa [hprod] at hprod_nonneg
      exact False.elim
        ((not_le_of_lt F (neg_one_lt_zero F)) hnegone_nonneg)
  apply lt_of_le_of_not_le F hle0inv
  intro hinv0
  exact (inv_ne_zero_of_ne_zero F hxne)
    (F.le_antisymm hinv0 hle0inv)

/-- The constant two, one plus one; the denominator that `half` below
inverts. Positivity is `zero_lt_two`. -/
def two : alpha :=
  F.add F.one F.one

/-- Halving, as multiplication by the inverse of `two`, since the bundle has
no division primitive. `half_add_half` below is what lets two halves rejoin,
and that reassembly is what lets an epsilon budget be split in half. -/
def half (x : alpha) : alpha :=
  F.mul x (F.inv (two F))

theorem zero_lt_two :
    F.lt F.zero (two F) := by
  unfold two
  have hone_two : F.lt F.one (F.add F.one F.one) := by
    have h := add_lt_add_right F (zero_lt_one F) F.one
    rwa [F.zero_add] at h
  exact lt_trans F (zero_lt_one F) hone_two

theorem two_ne_zero :
    Not (two F = F.zero) := by
  intro h
  exact ne_of_lt F (zero_lt_two F) h.symm

theorem half_pos {eps : alpha}
    (heps : F.lt F.zero eps) :
    F.lt F.zero (half F eps) := by
  unfold half
  exact mul_pos F heps (inv_pos F (zero_lt_two F))

theorem half_add_half (eps : alpha) :
    F.add (half F eps) (half F eps) = eps := by
  unfold half
  unfold two
  have hmul_two :
      F.mul eps (F.add F.one F.one) = F.add eps eps := by
    rw [F.mul_add]
    rw [F.mul_one]
  have htwo_ne : Not (F.add F.one F.one = F.zero) := by
    intro h
    exact (two_ne_zero F) h
  calc
    F.add (F.mul eps (F.inv (F.add F.one F.one)))
        (F.mul eps (F.inv (F.add F.one F.one))) =
        F.mul (F.add eps eps) (F.inv (F.add F.one F.one)) := by
          rw [F.add_mul]
    _ = F.mul (F.mul eps (F.add F.one F.one))
        (F.inv (F.add F.one F.one)) := by
          rw [hmul_two]
    _ = F.mul eps
        (F.mul (F.add F.one F.one) (F.inv (F.add F.one F.one))) := by
          rw [F.mul_assoc]
    _ = F.mul eps F.one := by
          rw [F.mul_inv_cancel htwo_ne]
    _ = eps := by rw [F.mul_one]

/-- A quarter of x, the half of a half. It exists for the three-way budget
split of `add_lt_quarter_half_quarter`, where two quarter-sized error terms
and one half-sized term must rejoin to eps. -/
def quarter (x : alpha) : alpha :=
  half F (half F x)

theorem quarter_pos {x : alpha}
    (hx : F.lt F.zero x) :
    F.lt F.zero (quarter F x) :=
  half_pos F (half_pos F hx)

/-- Three error terms bounded by eps / 4, eps / 2 and eps / 4 sum to less
than eps, the fractions reassembling exactly. This is the budget shape for an
estimate that must accommodate three separate errors in one eps, as the
integrability and uniform continuity arguments above do. -/
theorem add_lt_quarter_half_quarter
    {a b c eps : alpha}
    (ha : F.lt a (quarter F eps))
    (hb : F.lt b (half F eps))
    (hc : F.lt c (quarter F eps)) :
    F.lt (F.add a (F.add b c)) eps := by
  let e2 := half F eps
  let e4 := quarter F eps
  have hsum :
      F.lt (F.add a (F.add b c))
        (F.add e4 (F.add e2 e4)) :=
    add_lt_add F ha (add_lt_add F hb hc)
  have htarget : F.add e4 (F.add e2 e4) = eps := by
    unfold e4
    unfold quarter
    calc
      F.add (half F (half F eps))
          (F.add (half F eps) (half F (half F eps))) =
          F.add (half F (half F eps))
            (F.add (half F (half F eps)) (half F eps)) := by
              rw [F.add_comm (half F eps) (half F (half F eps))]
      _ = F.add
            (F.add (half F (half F eps)) (half F (half F eps)))
            (half F eps) := by
              rw [F.add_assoc]
      _ = F.add (half F eps) (half F eps) := by
              rw [half_add_half F (half F eps)]
      _ = eps := half_add_half F eps
  rwa [htarget] at hsum
end IsOrderedFieldBaseLike
end Tautology
