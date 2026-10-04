/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.Action.Basic
public import Tengoku.Seed.Algebra.GroupWithZero.Action.Units
public import Tengoku.Seed.Algebra.Group.Units.Opposite
public import Tengoku.Seed.Algebra.Module.Opposite

/-!
# Multiplication on the left/right as additive automorphisms

In this file we define `AddAut.mulLeft` and `AddAut.mulRight`.

See also `AddMonoidHom.mulLeft`, `AddMonoidHom.mulRight`, `AddMonoid.End.mulLeft`, and
`AddMonoid.End.mulRight` for multiplication by `R` as an endomorphism instead of multiplication by
`Rˣ` as an automorphism.
-/

@[expose] public section


namespace AddAut

variable {R : Type*} [Semiring R]

/-- Left multiplication by a unit of a semiring as an additive automorphism. -/
@[simps! +simpRhs]
def mulLeft : Rˣ →* Multiplicative (AddAut R) :=
  DistribMulAction.toAddAut _ _

/-- Right multiplication by a unit of a semiring as an additive automorphism. -/
def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]
theorem mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u :=
  rfl

@[simp]
theorem mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹ :=
  rfl

end AddAut
