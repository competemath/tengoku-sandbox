import Tengoku.Tautology.Tautology.RealBootstrap.InternalInt

/-!
# The rationals inside the field

The third internal system: quotients of an internal integer by a nonzero
internal natural, with the embedding of Lean's `Rat` landing inside it. Short,
because the work was done below -- once the integers are pinned down the
rationals are one division away.

Like its two predecessors, `InternalRat` is a predicate on field elements
rather than a type.

## Position and role

Implementation module over an arbitrary ordered field, and the vocabulary that
density (`Tautology.RealBootstrap.RationalDensity`) and the countable interval
basis of `Tautology.RealTopology.RationalBasis` are stated in.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The canonical image of an external rational, read off the normalized
numerator and denominator that `Rat` carries: the internal integer of the
numerator times the inverse of the internal natural of the denominator. The
denominator is nonzero by `Rat`'s own invariant, supplying the nonzero side
condition of `InternalRat`. -/
def rat (q : Rat) : alpha :=
  F.mul (int F q.num) (F.inv (nat F q.den))

/-- The internal rationals: quotients of an internal integer by a nonzero
internal natural. As with the other internal systems this is a predicate on
field elements rather than an external type; `internalRat_of_rat` shows the
embedding lands inside it. -/
def InternalRat (x : alpha) : Prop :=
  Exists
    (fun z : alpha =>
      Exists
        (fun d : alpha =>
          And (InternalInt F z)
            (And (InternalNat F d)
              (And (Not (d = F.zero))
                (x = F.mul z (F.inv d))))))

theorem internalRat_of_internalInt {z : alpha}
    (hz : InternalInt F z) :
    InternalRat F z := by
  refine Exists.intro z ?_
  refine Exists.intro F.one ?_
  exact And.intro hz
    (And.intro (internalNat_one F)
      (And.intro (one_ne_zero F) (by rw [inv_one F, F.mul_one])))

theorem internalRat_zero : InternalRat F F.zero :=
  internalRat_of_internalInt F (internalInt_zero F)

theorem internalRat_one : InternalRat F F.one :=
  internalRat_of_internalInt F (internalInt_one F)

/-- The embedding lands inside the predicate, with the normalized numerator and
denominator of `q` as the witness pair. Unlike at the two levels below, no
converse is proved in this strand: the countability of `InternalRat` is reached
through the coding of `Tautology.RealBootstrap.InternalCountable` rather than
by enumerating external `Rat`s. -/
theorem internalRat_of_rat (q : Rat) :
    InternalRat F (rat F q) := by
  refine Exists.intro (int F q.num) ?_
  refine Exists.intro (nat F q.den) ?_
  exact And.intro (internalInt_of_int F q.num)
    (And.intro (internalNat_of_nat F q.den)
      (And.intro (nat_ne_zero_of_ne_zero F q.den_nz) rfl))

end IsOrderedFieldBaseLike
end Tautology
