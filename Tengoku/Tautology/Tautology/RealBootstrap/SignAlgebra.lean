import Tengoku.Tautology.Tautology.RealBootstrap.Algebra

/-!
# How negation moves through products

Six rewriting facts about signs -- negation as multiplication by minus one, and
the ways it commutes with a product. Small, but they are the bridge between the
purely additive cancellation of `Tautology.RealBootstrap.Algebra` and the
order-sensitive multiplication arguments above, where the sign of a factor
decides whether an inequality flips.

## Position and role

Implementation module over an arbitrary ordered field.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Negation read as multiplication by minus one. It is the pivot of
this module -- `neg_mul` rewrites both sides through it -- and the
multiplied-out orientation reappears above in
`Tautology.RealBootstrap.OrderAlgebra`. -/
theorem neg_eq_neg_one_mul (x : alpha) :
    F.neg x = F.mul (F.neg F.one) x := by
  symm
  apply eq_neg_of_add_eq_zero_left F (x := x)
  calc
    F.add x (F.mul (F.neg F.one) x) =
        F.add (F.mul F.one x) (F.mul (F.neg F.one) x) := by
          rw [F.one_mul]
    _ = F.mul (F.add F.one (F.neg F.one)) x := by rw [F.add_mul]
    _ = F.mul F.zero x := by rw [F.add_neg]
    _ = F.zero := zero_mul F x

theorem neg_mul (x y : alpha) :
    F.mul (F.neg x) y = F.neg (F.mul x y) := by
  rw [neg_eq_neg_one_mul F x]
  rw [neg_eq_neg_one_mul F (F.mul x y)]
  rw [F.mul_assoc]

theorem mul_neg (x y : alpha) :
    F.mul x (F.neg y) = F.neg (F.mul x y) := by
  rw [F.mul_comm x (F.neg y)]
  rw [neg_mul F y x]
  rw [F.mul_comm y x]

theorem neg_one_mul_neg_one :
    F.mul (F.neg F.one) (F.neg F.one) = F.one := by
  have hzero :
      F.add (F.neg F.one)
        (F.mul (F.neg F.one) (F.neg F.one)) = F.zero := by
    calc
      F.add (F.neg F.one)
          (F.mul (F.neg F.one) (F.neg F.one)) =
          F.add (F.mul (F.neg F.one) F.one)
            (F.mul (F.neg F.one) (F.neg F.one)) := by
            rw [F.mul_one]
      _ = F.mul (F.neg F.one) (F.add F.one (F.neg F.one)) := by
            rw [F.mul_add]
      _ = F.mul (F.neg F.one) F.zero := by rw [F.add_neg]
      _ = F.zero := mul_zero F (F.neg F.one)
  calc
    F.mul (F.neg F.one) (F.neg F.one) =
        F.neg (F.neg F.one) := eq_neg_of_add_eq_zero_left F hzero
    _ = F.one := neg_neg F F.one

theorem neg_mul_neg (x y : alpha) :
    F.mul (F.neg x) (F.neg y) = F.mul x y := by
  rw [neg_mul F x (F.neg y)]
  rw [mul_neg F x y]
  rw [neg_neg F]

theorem neg_one_mul_neg (x : alpha) :
    F.mul (F.neg F.one) (F.neg x) = x := by
  rw [neg_mul_neg F F.one x]
  rw [F.one_mul]

end IsOrderedFieldBaseLike
end Tautology
