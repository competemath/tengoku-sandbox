import Tengoku.Tautology.Tautology.RealBootstrap.Base

/-!
# Field algebra without the order

Cancellation, negation, inverses: the facts that hold in any field, proved from
the bundle's axioms with no appeal to the order beyond what
`Tautology.RealBootstrap.Base` already fixed. Zero divisors are ruled out here,
which is what makes the cancellation laws and the inverse laws usable
everywhere above.

Every statement is short and its name is its content, which is why this file
carries almost no prose; the interesting question about it is not what it
proves but where it sits -- everything in the library that manipulates an
equation eventually lands on one of these.

## Position and role

Implementation module over an arbitrary ordered field; the order half of the
same layer is `Tautology.RealBootstrap.StrictOrder` and
`Tautology.RealBootstrap.OrderAlgebra`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem one_ne_zero : Not (F.one = F.zero) := by
  intro h
  exact F.zero_ne_one h.symm

theorem add_add_add_comm (a b c d : alpha) :
    F.add (F.add a b) (F.add c d) =
      F.add (F.add a c) (F.add b d) := by
  calc
    F.add (F.add a b) (F.add c d) =
        F.add a (F.add b (F.add c d)) := by
          rw [F.add_assoc]
    _ = F.add a (F.add (F.add b c) d) := by
          rw [<- F.add_assoc b c d]
    _ = F.add a (F.add (F.add c b) d) := by
          rw [F.add_comm b c]
    _ = F.add a (F.add c (F.add b d)) := by
          rw [F.add_assoc c b d]
    _ = F.add (F.add a c) (F.add b d) := by
          rw [<- F.add_assoc a c (F.add b d)]

theorem add_left_cancel {a b c : alpha}
    (h : F.add a b = F.add a c) : b = c := by
  calc
    b = F.add F.zero b := by rw [F.zero_add]
    _ = F.add (F.add (F.neg a) a) b := by rw [F.neg_add]
    _ = F.add (F.neg a) (F.add a b) := by rw [F.add_assoc]
    _ = F.add (F.neg a) (F.add a c) := by rw [h]
    _ = F.add (F.add (F.neg a) a) c := by rw [<- F.add_assoc]
    _ = F.add F.zero c := by rw [F.neg_add]
    _ = c := by rw [F.zero_add]

theorem add_right_cancel {a b c : alpha}
    (h : F.add b a = F.add c a) : b = c := by
  apply add_left_cancel F (a := a)
  calc
    F.add a b = F.add b a := F.add_comm a b
    _ = F.add c a := h
    _ = F.add a c := F.add_comm c a

theorem add_neg_cancel_right (x y : alpha) :
    F.add (F.add x y) (F.neg y) = x := by
  calc
    F.add (F.add x y) (F.neg y) =
        F.add x (F.add y (F.neg y)) := by rw [F.add_assoc]
    _ = F.add x F.zero := by rw [F.add_neg]
    _ = x := by rw [F.add_zero]

theorem neg_add_cancel_left (x y : alpha) :
    F.add (F.neg x) (F.add x y) = y := by
  calc
    F.add (F.neg x) (F.add x y) =
        F.add (F.add (F.neg x) x) y := by rw [<- F.add_assoc]
    _ = F.add F.zero y := by rw [F.neg_add]
    _ = y := by rw [F.zero_add]

theorem eq_zero_of_add_eq_self_left {x y : alpha}
    (h : F.add x y = x) : y = F.zero := by
  apply add_left_cancel F (a := x)
  rw [h, F.add_zero]

theorem eq_zero_of_add_eq_self_right {x y : alpha}
    (h : F.add y x = x) : y = F.zero := by
  apply eq_zero_of_add_eq_self_left F (x := x)
  calc
    F.add x y = F.add y x := F.add_comm x y
    _ = x := h

theorem eq_neg_of_add_eq_zero_left {x y : alpha}
    (h : F.add x y = F.zero) : y = F.neg x := by
  apply add_left_cancel F (a := x)
  rw [h, F.add_neg]

theorem eq_neg_of_add_eq_zero_right {x y : alpha}
    (h : F.add y x = F.zero) : y = F.neg x := by
  apply eq_neg_of_add_eq_zero_left F (x := x)
  calc
    F.add x y = F.add y x := F.add_comm x y
    _ = F.zero := h

theorem neg_zero : F.neg F.zero = F.zero := by
  apply eq_zero_of_add_eq_self_right F (x := F.zero)
  exact F.neg_add F.zero

theorem neg_neg (x : alpha) : F.neg (F.neg x) = x := by
  symm
  apply eq_neg_of_add_eq_zero_left F (x := F.neg x)
  exact F.neg_add x

theorem neg_add_distrib (x y : alpha) :
    F.neg (F.add x y) = F.add (F.neg x) (F.neg y) := by
  symm
  apply eq_neg_of_add_eq_zero_left F (x := F.add x y)
  have hinner :
      F.add y (F.add (F.neg x) (F.neg y)) = F.neg x := by
    calc
      F.add y (F.add (F.neg x) (F.neg y)) =
          F.add y (F.add (F.neg y) (F.neg x)) := by
            rw [F.add_comm (F.neg x) (F.neg y)]
      _ = F.add (F.add y (F.neg y)) (F.neg x) := by
            rw [<- F.add_assoc]
      _ = F.add F.zero (F.neg x) := by rw [F.add_neg]
      _ = F.neg x := by rw [F.zero_add]
  calc
    F.add (F.add x y) (F.add (F.neg x) (F.neg y)) =
        F.add x (F.add y (F.add (F.neg x) (F.neg y))) := by
          rw [F.add_assoc]
    _ = F.add x (F.neg x) := by rw [hinner]
    _ = F.zero := F.add_neg x

theorem sub_self (x : alpha) : F.sub x x = F.zero := by
  rw [F.sub_eq_add_neg]
  exact F.add_neg x

theorem zero_mul (x : alpha) : F.mul F.zero x = F.zero := by
  have hsum :
      F.add (F.mul F.zero x) (F.mul F.zero x) =
        F.mul F.zero x := by
    calc
      F.add (F.mul F.zero x) (F.mul F.zero x) =
          F.mul (F.add F.zero F.zero) x := by rw [F.add_mul]
      _ = F.mul F.zero x := by rw [F.add_zero]
  exact eq_zero_of_add_eq_self_left F hsum

theorem mul_zero (x : alpha) : F.mul x F.zero = F.zero := by
  rw [F.mul_comm]
  exact zero_mul F x

theorem mul_left_cancel_of_ne_zero {x y z : alpha}
    (hx : Not (x = F.zero))
    (h : F.mul x y = F.mul x z) : y = z := by
  calc
    y = F.mul F.one y := by rw [F.one_mul]
    _ = F.mul (F.mul (F.inv x) x) y := by rw [F.inv_mul_cancel hx]
    _ = F.mul (F.inv x) (F.mul x y) := by rw [F.mul_assoc]
    _ = F.mul (F.inv x) (F.mul x z) := by rw [h]
    _ = F.mul (F.mul (F.inv x) x) z := by rw [<- F.mul_assoc]
    _ = F.mul F.one z := by rw [F.inv_mul_cancel hx]
    _ = z := by rw [F.one_mul]

theorem mul_right_cancel_of_ne_zero {x y z : alpha}
    (hz : Not (z = F.zero))
    (h : F.mul x z = F.mul y z) : x = y := by
  apply mul_left_cancel_of_ne_zero F (x := z) hz
  calc
    F.mul z x = F.mul x z := F.mul_comm z x
    _ = F.mul y z := h
    _ = F.mul z y := F.mul_comm y z

theorem eq_zero_of_mul_eq_zero_left {x y : alpha}
    (hx : Not (x = F.zero))
    (h : F.mul x y = F.zero) : y = F.zero := by
  apply mul_left_cancel_of_ne_zero F (x := x) hx
  rw [h, mul_zero]

theorem eq_zero_of_mul_eq_zero_right {x y : alpha}
    (hy : Not (y = F.zero))
    (h : F.mul x y = F.zero) : x = F.zero := by
  apply mul_right_cancel_of_ne_zero F (z := y) hy
  rw [h, zero_mul]

/-- A field has no zero divisors: a vanishing product has a vanishing factor.
Stated as a case split rather than as a negated equation, because consumers
rule out one factor and keep the other. -/
theorem mul_eq_zero_cases {x y : alpha}
    (h : F.mul x y = F.zero) : Or (x = F.zero) (y = F.zero) := by
  by_cases hx : x = F.zero
  · exact Or.inl hx
  · exact Or.inr (eq_zero_of_mul_eq_zero_left F hx h)

theorem mul_ne_zero {x y : alpha}
    (hx : Not (x = F.zero))
    (hy : Not (y = F.zero)) :
    Not (F.mul x y = F.zero) := by
  intro h
  cases mul_eq_zero_cases F h with
  | inl hx0 => exact hx hx0
  | inr hy0 => exact hy hy0

theorem eq_one_of_mul_eq_self_left {x y : alpha}
    (hx : Not (x = F.zero))
    (h : F.mul x y = x) : y = F.one := by
  apply mul_left_cancel_of_ne_zero F (x := x) hx
  rw [h, F.mul_one]

theorem eq_inv_of_mul_eq_one_left {x y : alpha}
    (hx : Not (x = F.zero))
    (h : F.mul x y = F.one) : y = F.inv x := by
  apply mul_left_cancel_of_ne_zero F (x := x) hx
  rw [h, F.mul_inv_cancel hx]

theorem eq_inv_of_mul_eq_one_right {x y : alpha}
    (hx : Not (x = F.zero))
    (h : F.mul y x = F.one) : y = F.inv x := by
  apply eq_inv_of_mul_eq_one_left F hx
  calc
    F.mul x y = F.mul y x := F.mul_comm x y
    _ = F.one := h

theorem inv_one : F.inv F.one = F.one := by
  symm
  apply eq_inv_of_mul_eq_one_left F (x := F.one)
  · exact one_ne_zero F
  · rw [F.mul_one]

/-- The reciprocal of a product is the product of the reciprocals, in the
reversed order. `inv_mul_inv_right` below builds the reciprocal of a
quotient on this exchange. -/
theorem inv_mul {x y : alpha}
    (hx : Not (x = F.zero))
    (hy : Not (y = F.zero)) :
    F.inv (F.mul x y) = F.mul (F.inv y) (F.inv x) := by
  symm
  apply eq_inv_of_mul_eq_one_left F
    (x := F.mul x y)
  · exact mul_ne_zero F hx hy
  · calc
      F.mul (F.mul x y) (F.mul (F.inv y) (F.inv x)) =
          F.mul x (F.mul y (F.mul (F.inv y) (F.inv x))) := by
            rw [F.mul_assoc x y (F.mul (F.inv y) (F.inv x))]
      _ = F.mul x (F.mul (F.mul y (F.inv y)) (F.inv x)) := by
            rw [<- F.mul_assoc y (F.inv y) (F.inv x)]
      _ = F.mul x (F.mul F.one (F.inv x)) := by
            rw [F.mul_inv_cancel hy]
      _ = F.mul x (F.inv x) := by rw [F.one_mul]
      _ = F.one := by rw [F.mul_inv_cancel hx]

theorem inv_ne_zero_of_ne_zero {x : alpha}
    (hx : Not (x = F.zero)) :
    Not (F.inv x = F.zero) := by
  intro hinv
  have h := F.mul_inv_cancel hx
  rw [hinv, mul_zero F x] at h
  exact F.zero_ne_one h

/-- Inverting a quotient exchanges numerator and denominator: the reciprocal
of `a * (1/b)` is `b * (1/a)`. -/
theorem inv_mul_inv_right {a b : alpha}
    (ha : Not (a = F.zero))
    (hb : Not (b = F.zero)) :
    F.inv (F.mul a (F.inv b)) =
      F.mul b (F.inv a) := by
  have hinvb_ne := inv_ne_zero_of_ne_zero F hb
  have hinv_inv : F.inv (F.inv b) = b := by
    symm
    exact eq_inv_of_mul_eq_one_left F hinvb_ne (F.inv_mul_cancel hb)
  rw [inv_mul F ha hinvb_ne, hinv_inv]

theorem inv_inv_of_ne_zero {x : alpha}
    (hx : Not (x = F.zero)) :
    F.inv (F.inv x) = x := by
  have hinv_ne : Not (F.inv x = F.zero) :=
    inv_ne_zero_of_ne_zero F hx
  symm
  exact eq_inv_of_mul_eq_one_left F hinv_ne (F.inv_mul_cancel hx)

theorem mul_inv_mul_cancel_right (x : alpha) {y : alpha}
    (hy : Not (y = F.zero)) :
    F.mul (F.mul x (F.inv y)) y = x := by
  calc
    F.mul (F.mul x (F.inv y)) y =
        F.mul x (F.mul (F.inv y) y) := by rw [F.mul_assoc]
    _ = F.mul x F.one := by rw [F.inv_mul_cancel hy]
    _ = x := by rw [F.mul_one]

theorem mul_mul_inv_cancel_right (x : alpha) {y : alpha}
    (hy : Not (y = F.zero)) :
    F.mul (F.mul x y) (F.inv y) = x := by
  calc
    F.mul (F.mul x y) (F.inv y) =
        F.mul x (F.mul y (F.inv y)) := by rw [F.mul_assoc]
    _ = F.mul x F.one := by rw [F.mul_inv_cancel hy]
    _ = x := by rw [F.mul_one]

end IsOrderedFieldBaseLike
end Tautology
