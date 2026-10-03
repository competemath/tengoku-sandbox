import Tengoku.Tautology.Tautology.Foundation.Cardinal.Pairing
import Init.Data.Int.Lemmas
import Init.Data.Rat.Lemmas

/-!
# The integers and the rationals are enumerable

Both proofs have the same two-line shape: exhibit a surjection from something
already known to be enumerable, then apply `enumerable_of_surjective`. A
difference of two naturals covers `Int`; a numerator paired with a shifted
denominator covers `Rat`, the shift being what keeps the denominator away from
zero. Neither map is injective and neither needs to be -- partial enumerations,
in the sense of `Tautology.Foundation.Cardinal.Countable`, tolerate repetition.

## These are Lean's `Int` and `Rat`, not the library's number systems

The file is about the external types from Lean core, which is why it is the
one place in the subtree importing `Init.Data.Int.Lemmas` and
`Init.Data.Rat.Lemmas`. The library's own number systems are something else
entirely: `InternalNat`, `InternalInt` and `InternalRat` are *predicates* on a
carrier saying that an element of the field is a natural, an integer or a
rational, and there is no coercion from `Nat` into a carrier anywhere. Reading
this module as being about those is the mistake to avoid.

The two are connected exactly once. `Tautology.RealBootstrap.InternalCountable`
uses the results here to show the internal rationals of a carrier are
countable, by transporting along the correspondence between the predicate and
the external type. That is also why this module sits where it does:
countability of the internal rationals was originally filed under
`RealCardinality`, and moving it down to `RealBootstrap` during the batch 3
restructuring removed a region cycle, which was possible only because
everything it needs stops here.

## Position in the development

Above `Tautology.Foundation.Cardinal.Pairing`, whose pairing enumeration both
proofs consume. A leaf of the subtree.

## Role

Implementation.
The words this header uses in a sense particular to this library -- region,
route, waist, valve, facade, and the three kinds of aggregation module -- are
each defined once, in the header of the root module `Tautology`. This region
has no umbrella to carry that pointer, so the modules that use the vocabulary
carry it themselves.

-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- A pair of naturals read as the integer difference of its components.
Far from injective -- `(n, 0)` and `(n + 1, 1)` both give `n` -- and it does
not need to be, since enumerations tolerate repetition. -/
def intOfNatPair (p : Nat × Nat) : Int :=
  ((p.fst : Nat) : Int) - ((p.snd : Nat) : Int)

/-- Every integer is covered, at a pair chosen by sign: `z >= 0` at
`(z.toNat, 0)` and `z < 0` at `(0, (-z).toNat)`. -/
theorem intOfNatPair_surjective :
    Surjective intOfNatPair := by
  intro z
  by_cases hz : 0 <= z
  · refine Exists.intro (z.toNat, 0) ?_
    unfold intOfNatPair
    have hcast : ((z.toNat : Nat) : Int) = z :=
      Int.toNat_of_nonneg hz
    rw [hcast]
    simp
  · refine Exists.intro (0, (-z).toNat) ?_
    unfold intOfNatPair
    have hneg : 0 <= -z := by omega
    have hcast : (((-z).toNat : Nat) : Int) = -z :=
      Int.toNat_of_nonneg hneg
    rw [hcast]
    omega

theorem enumerable_int :
    Enumerable Int :=
  enumerable_of_surjective enumerable_nat_prod_nat
    intOfNatPair_surjective

/-- A pair read as a rational: the first component over the second plus one.
The shift keeps the denominator at least `1`, matching `Rat.den`, which is
positive by construction. -/
def ratOfIntNatPair (p : Int × Nat) : Rat :=
  Rat.divInt p.fst (((p.snd + 1 : Nat) : Int))

/-- Every rational is hit at `(q.num, q.den - 1)`, the shift undone by
`q.den_pos`. -/
theorem ratOfIntNatPair_surjective :
    Surjective ratOfIntNatPair := by
  intro q
  refine Exists.intro (q.num, q.den - 1) ?_
  unfold ratOfIntNatPair
  have hden : q.den - 1 + 1 = q.den := by
    have hpos : 0 < q.den := q.den_pos
    omega
  rw [hden]
  exact Rat.num_divInt_den q

theorem enumerable_rat :
    Enumerable Rat := by
  have hprod : Enumerable (Int × Nat) :=
    enumerable_prod enumerable_int enumerable_nat
  exact enumerable_of_surjective hprod ratOfIntNatPair_surjective

end Cardinal
end Foundation
end Tautology
