module

public import Tengoku

public section

namespace AddChar
variable {R M N : Type*} [CommMonoid M] [Semiring R] [AddCommMonoid N] [Module R N]

/-- Interpret a character of the `R`-module `N` as a homomorphism from `N` to character of `R`,
via precomposition by scalar multiplication. -/
@[expose, simps]
def toAddMonoidHomAddChar (γ : AddChar N M) : N →+ AddChar R M where
  toFun x := {
    toFun r := γ (r • x)
    map_zero_eq_one' := by simp
    map_add_eq_mul' r s := by simp [add_smul, map_add_eq_mul]
  }
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [map_add_eq_mul, smul_add]

end AddChar
