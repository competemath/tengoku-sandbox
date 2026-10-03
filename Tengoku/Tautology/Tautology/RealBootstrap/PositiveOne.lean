import Tengoku.Tautology.Tautology.RealBootstrap.StrictOrder

/-!
# One is positive

Three declarations for a single fact. It cannot be assumed -- the bundle does
not axiomatise it -- and it cannot be skipped, because the embedded naturals,
the halving arguments and every Archimedean statement above depend on it. The
proof is the classical one: were one at most zero, multiplying the inequality
by itself would contradict the order axioms.

## Position and role

Implementation module over an arbitrary ordered field. Small, but it is the
hinge between the sign algebra below and the internal number systems above:
`Tautology.RealBootstrap.InternalNat` starts here.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The squaring step towards positivity of one: if one were at most zero,
minus one would be nonnegative, and its square -- one -- would be nonnegative
too, the reverse inequality. Read with antisymmetry this leaves no way for
one to be nonpositive. -/
theorem zero_le_one_of_one_le_zero (h10 : F.le F.one F.zero) :
    F.le F.zero F.one := by
  have hneg_nonneg : F.le F.zero (F.neg F.one) := by
    have h := F.add_le_add_right h10 (F.neg F.one)
    rwa [F.add_neg, F.zero_add] at h
  have hsquare :
      F.le F.zero (F.mul (F.neg F.one) (F.neg F.one)) :=
    F.mul_nonneg hneg_nonneg hneg_nonneg
  rwa [neg_one_mul_neg_one F] at hsquare

/-- Positivity of one, derived rather than assumed: the bundle's axioms do not
state it. Totality leaves either `zero < one` outright or `one <= zero`, and
the squaring argument above turns the second case into its own reverse, so
antisymmetry against `zero_ne_one` closes both cases. Everything above
this module -- the embedded naturals, halving, the Archimedean principles --
starts from here. -/
theorem zero_lt_one : F.lt F.zero F.one := by
  cases F.le_total F.zero F.one with
  | inl h01 =>
      apply lt_of_le_of_not_le F h01
      intro h10
      exact F.zero_ne_one (F.le_antisymm h01 h10)
  | inr h10 =>
      have h01 : F.le F.zero F.one :=
        zero_le_one_of_one_le_zero F h10
      exact False.elim (F.zero_ne_one (F.le_antisymm h01 h10))

theorem zero_le_one : F.le F.zero F.one :=
  le_of_lt F (zero_lt_one F)

end IsOrderedFieldBaseLike
end Tautology
