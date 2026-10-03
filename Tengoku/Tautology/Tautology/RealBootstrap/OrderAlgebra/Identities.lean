import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra
import Tengoku.Tautology.Tautology.RealBootstrap.InternalNat

/-!
# Three identities that needed the internal naturals

A small appendix to `Tautology.RealBootstrap.OrderAlgebra`, separated because
its statements mention the embedded natural numbers and so cannot appear before
`Tautology.RealBootstrap.InternalNat`. Doubling as addition to itself, a
square-inverse rearrangement, and the four-fold difference of a sum and
difference of squares.

## Position and role

Implementation module over an arbitrary ordered field. It exists for the
dependency order alone; mathematically it belongs with the identities at
the end of `OrderAlgebra`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Doubling by the embedded two: `nat 2` times z is z plus itself. The Landen
elliptic chain (`Tautology.RealElliptic.Landen`) computes with the embedded
naturals and uses this to unfold doublings. -/
theorem nat_two_mul_eq_add_self (z : alpha) :
    F.mul (F.nat 2) z = F.add z z := by
  have htwo : F.nat 2 = F.add F.one F.one := by
    rw [nat_succ F 1]
    rw [nat_succ F 0]
    rw [nat_zero F]
    change F.add (F.add F.zero F.one) F.one = F.add F.one F.one
    rw [F.zero_add]
  rw [htwo, F.add_mul, F.one_mul]

/-- Squaring commutes with forming the quotient: the square of
`a * inv b` equals `a * a` times `inv (b * b)`, with nothing cancelled along
the way. Its consumers sit in the Landen elliptic chain
(`Tautology.RealElliptic.Landen`). -/
theorem square_mul_inv_eq_mul_inv_square
    (a b : alpha) (hb : Not (b = F.zero)) :
    F.mul (F.mul a (F.inv b)) (F.mul a (F.inv b)) =
      F.mul (F.mul a a) (F.inv (F.mul b b)) := by
  rw [mul_mul_mul_comm F a (F.inv b) a (F.inv b)]
  rw [<- inv_mul F hb hb]

/-- The squared sum minus the squared difference is four times the product,
with the four carried as the embedded product `nat 2 * nat 2`. The Landen chain
(`Tautology.RealElliptic.Landen`) trades between squared sums and products
through it. -/
theorem sum_sq_sub_diff_sq_eq_four_mul (a b : alpha) :
    F.sub (F.mul (F.add a b) (F.add a b))
      (F.mul (F.sub a b) (F.sub a b)) =
      F.mul (F.mul (F.nat 2) (F.nat 2)) (F.mul a b) := by
  let A := F.add a b
  let q := F.sub a b
  have hminus : F.sub A q = F.add b b := by
    unfold A q
    rw [F.sub_eq_add_neg a b]
    rw [add_sub_add_eq_sub_add_sub F a b a (F.neg b)]
    rw [sub_self F a]
    rw [F.zero_add]
    rw [F.sub_eq_add_neg b (F.neg b)]
    rw [neg_neg F b]
  have hplus : F.add A q = F.add a a := by
    unfold A q
    exact add_add_sub_cancel_same F a a b
  have hsquare (x y : alpha) :
      F.sub (F.mul x x) (F.mul y y) =
        F.mul (F.sub x y) (F.add x y) := by
    rw [mul_sub_mul_eq_sub_mul_add_mul_sub F x x y y]
    rw [F.mul_add]
    rw [F.mul_comm y (F.sub x y)]
  calc
    F.sub (F.mul A A) (F.mul q q) =
        F.mul (F.sub A q) (F.add A q) := hsquare A q
    _ = F.mul (F.add b b) (F.add a a) := by rw [hminus, hplus]
    _ = F.mul (F.mul (F.nat 2) b) (F.mul (F.nat 2) a) := by
      rw [nat_two_mul_eq_add_self F b]
      rw [nat_two_mul_eq_add_self F a]
    _ = F.mul (F.mul (F.nat 2) (F.nat 2)) (F.mul a b) := by
      rw [mul_mul_mul_comm F (F.nat 2) b (F.nat 2) a]
      rw [F.mul_comm b a]

end IsOrderedFieldBaseLike
end Tautology
