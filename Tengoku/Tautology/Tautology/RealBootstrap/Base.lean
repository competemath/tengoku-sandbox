import Tengoku.Tautology.Tautology.Foundation.OrderField

/-!
# The first definitions above the valve room

Where the library starts doing arithmetic. `Tautology.Foundation.OrderField`
supplies the bundled structure `IsOrderedFieldBaseLike` with its primitive
operations and axioms; this file defines the two derived notions everything
else is phrased with -- subtraction as addition of the negation, and strict
order as `le` together with the failure of `le` in the other direction -- and
proves the handful of one-line consequences that the axioms leave implicit.

## Position and role

Implementation module, the base of `RealBootstrap` and hence of every real
statement in the library. It is stated over an arbitrary
`(F : IsOrderedFieldBaseLike alpha)`, passed explicitly because the project
uses no typeclasses; nothing here is about the selected carrier, and no
completeness is available at this level.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

/-- Subtraction as a derived operation: `x - y` is `x + -y`. The bundle
axiomatises no subtraction primitive, so every difference written anywhere
above this module unfolds through this definition. -/
def sub {alpha : Type} (self : IsOrderedFieldBaseLike alpha) :
    alpha -> alpha -> alpha :=
  fun x y => self.add x (self.neg y)

/-- Strict order as a derived notion: `x < y` when `le x y` holds and `le y x`
fails. Totality of `le` makes this the expected strict order; its properties
are derived in `Tautology.RealBootstrap.StrictOrder` rather than assumed. -/
def lt {alpha : Type} (self : IsOrderedFieldBaseLike alpha) :
    alpha -> alpha -> Prop :=
  fun x y => And (self.le x y) (Not (self.le y x))

theorem lt_def {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    {x y : alpha} :
    self.lt x y <-> And (self.le x y) (Not (self.le y x)) :=
  Iff.rfl

theorem zero_add {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    (x : alpha) :
    self.add self.zero x = x := by
  rw [self.add_comm]
  exact self.add_zero x

theorem neg_add {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    (x : alpha) :
    self.add (self.neg x) x = self.zero := by
  rw [self.add_comm]
  exact self.add_neg x

theorem sub_eq_add_neg {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    (x y : alpha) :
    self.sub x y = self.add x (self.neg y) :=
  rfl

theorem one_mul {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    (x : alpha) :
    self.mul self.one x = x := by
  rw [self.mul_comm]
  exact self.mul_one x

/-- Distributivity with the sum on the left factor. The bundle axiom
`mul_add` covers only a sum on the right of the product, so this mirrored
form is derived through commutativity. -/
theorem add_mul {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    (x y z : alpha) :
    self.mul (self.add x y) z = self.add (self.mul x z) (self.mul y z) := by
  calc
    self.mul (self.add x y) z = self.mul z (self.add x y) := self.mul_comm _ _
    _ = self.add (self.mul z x) (self.mul z y) := self.mul_add z x y
    _ = self.add (self.mul x z) (self.mul y z) := by
      rw [self.mul_comm z x, self.mul_comm z y]

/-- Multiplying by the inverse on the left: the inverse of x times x is one,
for x nonzero. The bundle's `mul_inv_cancel` axiom states this only with the
inverse on the right, so this is the commuted form. -/
theorem inv_mul_cancel {alpha : Type} (self : IsOrderedFieldBaseLike alpha)
    {x : alpha} :
    Not (x = self.zero) -> self.mul (self.inv x) x = self.one := by
  intro hx
  rw [self.mul_comm]
  exact self.mul_inv_cancel hx

end IsOrderedFieldBaseLike
end Tautology
