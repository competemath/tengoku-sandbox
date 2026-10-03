import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra.Identities

/-!
# Three field identities the Landen argument keeps reaching for

Doubling, squaring a quotient, and the difference of the squares of a sum and a
difference. All three are forwarding declarations: the proofs are the
corresponding lemmas of `Tautology.RealBootstrap.OrderAlgebra.Identities`, and
the only thing added is a name local to this development. The last of them,
`sum_sq_sub_diff_sq_eq_four_mul_base`, is the algebraic identity behind the
arithmetic--geometric step itself, which is why those lemmas exist upstream at
all -- the module header of `Tautology.RealBootstrap.OrderAlgebra` records that
its closing identities were put there for specific consumers, and this is the
consumer.

## The namespace does not match the directory, for a historical reason

Declarations here sit in `namespace RealIntegral.Riemann.LandenInternal`,
which is where the whole Landen development lived before it was lifted out of
`RealDerivative/Integral/Riemann/` into `RealElliptic/`. The move deliberately
left the namespace alone so that no qualified name changed. As elsewhere in
this library, the directory records the dependency position and the namespace
records the subject and its history; neither is wrong.

## Role

Implementation, and the base of the Landen subtree: every other module under
`RealElliptic/Landen/` sits above it.
-/

namespace Tautology
namespace RealIntegral
namespace Riemann
namespace LandenInternal

theorem nat_two_mul_eq_add_self_base
    {alpha : Type} (F : IsOrderedFieldBaseLike alpha) (z : alpha) :
    F.mul (F.nat 2) z = F.add z z :=
  IsOrderedFieldBaseLike.nat_two_mul_eq_add_self F z

theorem square_mul_inv_eq_mul_inv_square_base
    {alpha : Type} (F : IsOrderedFieldBaseLike alpha) (a b : alpha)
    (hb : Not (b = F.zero)) :
    F.mul (F.mul a (F.inv b)) (F.mul a (F.inv b)) =
      F.mul (F.mul a a) (F.inv (F.mul b b)) :=
  IsOrderedFieldBaseLike.square_mul_inv_eq_mul_inv_square F a b hb

theorem sum_sq_sub_diff_sq_eq_four_mul_base
    {alpha : Type} (F : IsOrderedFieldBaseLike alpha) (a b : alpha) :
    F.sub (F.mul (F.add a b) (F.add a b))
      (F.mul (F.sub a b) (F.sub a b)) =
      F.mul (F.mul (F.nat 2) (F.nat 2)) (F.mul a b) :=
  IsOrderedFieldBaseLike.sum_sq_sub_diff_sq_eq_four_mul F a b

end LandenInternal
end Riemann
end RealIntegral
end Tautology
