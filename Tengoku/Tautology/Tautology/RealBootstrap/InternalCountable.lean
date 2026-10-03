import Tengoku.Tautology.Tautology.Foundation.Cardinal
import Tengoku.Tautology.Tautology.RealBootstrap.InternalRat

/-!
# The internal number systems are countable

Explicit enumerations for the internal naturals, integers and rationals: an
integer is coded by a pair of naturals, a rational by such a pair together with
a denominator, and the countability statements follow from the coding lemmas of
`Tautology.Foundation.Cardinal`.

Countability here is a fact about *any* ordered field, needing neither
completeness nor an Archimedean principle -- the field's own copy of the
rationals is countable simply because the coding is. That is why this module
can sit this low, and it matters structurally: the cardinality results upstream
need it, and the countable basis of the topology needs it, but neither should
have to reach up into a region above them to get it.

## Position and role

Implementation module over an arbitrary ordered field. Consumed by
`Tautology.RealTopology.RationalBasis`, by `RealCardinality`, and through the
umbrella by the facades.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The field element coded by a pair of naturals: the difference of their
images. Coding internal integers through `Nat × Nat` is what lets their
countability inherit from `Foundation.Cardinal.enumerable_nat_prod_nat`. -/
def internalIntCodeValue (p : Nat × Nat) : alpha :=
  F.sub (nat F p.fst) (nat F p.snd)

/-- The field element coded by a triple: the internal integer coded by the
pair component, divided by the image of the third natural. Enumerating
these triples through `Foundation.Cardinal.enumerable_prod` is how
`internalRat_countable` below enumerates the internal rationals. -/
def internalRatCodeValue (p : (Nat × Nat) × Nat) : alpha :=
  F.mul (internalIntCodeValue F p.fst) (F.inv (nat F p.snd))

/-- The internal naturals are countable, with the embedding itself serving
as the enumeration: each internal natural appears at its own external
index, exhaustiveness being exactly `internalNat_exists_nat`. -/
theorem internalNat_countable :
    Foundation.Cardinal.CountableSet (InternalNat F) := by
  refine Exists.intro (fun n : Nat => some (nat F n)) ?_
  intro x hx
  cases internalNat_exists_nat F hx with
  | intro n hn =>
      exact Exists.intro n (by rw [hn])

/-- The internal integers are countable, enumerated through the pair coding
`internalIntCodeValue`. The coding is far from injective -- every pair
`(m + k, n + k)` codes the same difference -- which is harmless here:
countability asks only that the enumeration reach every internal integer,
not that it reach each one once. -/
theorem internalInt_countable :
    Foundation.Cardinal.CountableSet (InternalInt F) := by
  have hdom : Foundation.Cardinal.Enumerable (Nat × Nat) :=
    Foundation.Cardinal.enumerable_nat_prod_nat
  refine Exists.intro
    (fun n : Nat =>
      Foundation.Cardinal.OptionMap (internalIntCodeValue F)
        (Classical.choose hdom n)) ?_
  intro x hx
  cases hx with
  | intro a ha =>
      cases ha with
      | intro b hb =>
          cases internalNat_exists_nat F hb.left with
          | intro m hm =>
              cases internalNat_exists_nat F hb.right.left with
              | intro n hn =>
                  let p : Nat × Nat := (m, n)
                  have hp := Classical.choose_spec hdom p
                  cases hp with
                  | intro k hk =>
                      refine Exists.intro k ?_
                      change
                        Foundation.Cardinal.OptionMap
                            (internalIntCodeValue F)
                            (Classical.choose hdom k) =
                          some x
                      simp [Foundation.Cardinal.OptionMap, hk,
                        internalIntCodeValue, p, hb.right.right, hm, hn]

/-- The internal rationals form a countable set, enumerated through the
coding of `internalRatCodeValue`. Completeness plays no part here: the
statement lives at the ordered-field level. -/
theorem internalRat_countable :
    Foundation.Cardinal.CountableSet (InternalRat F) := by
  have hpair : Foundation.Cardinal.Enumerable (Nat × Nat) :=
    Foundation.Cardinal.enumerable_nat_prod_nat
  have hdom : Foundation.Cardinal.Enumerable ((Nat × Nat) × Nat) :=
    Foundation.Cardinal.enumerable_prod hpair
      Foundation.Cardinal.enumerable_nat
  refine Exists.intro
    (fun n : Nat =>
      Foundation.Cardinal.OptionMap (internalRatCodeValue F)
        (Classical.choose hdom n)) ?_
  intro x hx
  cases hx with
  | intro z hz =>
      cases hz with
      | intro d hd =>
          cases hd.left with
          | intro a ha =>
              cases ha with
              | intro b hb =>
                  cases internalNat_exists_nat F hb.left with
                  | intro m hm =>
                      cases internalNat_exists_nat F hb.right.left with
                      | intro n hn =>
                          cases internalNat_exists_nat F hd.right.left with
                          | intro k hk =>
                              let p : (Nat × Nat) × Nat := ((m, n), k)
                              have hp := Classical.choose_spec hdom p
                              cases hp with
                              | intro idx hidx =>
                                  refine Exists.intro idx ?_
                                  change
                                    Foundation.Cardinal.OptionMap
                                        (internalRatCodeValue F)
                                        (Classical.choose hdom idx) =
                                      some x
                                  simp [Foundation.Cardinal.OptionMap, hidx,
                                    internalRatCodeValue, internalIntCodeValue,
                                    p,
                                    hd.right.right.right,
                                    hb.right.right, hm, hn, hk]

end IsOrderedFieldBaseLike
end Tautology
