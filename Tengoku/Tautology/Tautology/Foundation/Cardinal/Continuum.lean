import Tengoku.Tautology.Tautology.Foundation.Cardinal.Cantor
import Tengoku.Tautology.Tautology.Foundation.Cardinal.CantorBernstein

/-!
# The size of the continuum, stated without the reals

`BinarySequences` is `Nat -> Prop`, and a type is `ContinuumSized` when it is
equipotent to it. The two one-sided forms, `ContinuumLowerBound` and
`ContinuumUpperBound`, are the ones a proof actually establishes, and
`continuumSized_iff_bounds` puts them together -- which is an application of
Cantor--Bernstein and the reason
`Tautology.Foundation.Cardinal.CantorBernstein` is imported.

Everything here is about an arbitrary type. Nothing in this file mentions an
ordered field, and the reals appear nowhere; `RealCardinality` later shows the
selected carrier satisfies these predicates, and the statement it proves is
the one defined here. Keeping the definition at this level is what lets
"the reals have the size of the continuum" be a theorem about a carrier rather
than a definition of one.

## What `predicateCodeOfEnum` is doing

Given an enumeration of a type, it codes a predicate on that type as a
predicate on `Nat`, by asking the question at the enumerated point and
answering `False` where the enumeration is undefined. Injectivity of that
coding is `powerset_cardLE_binarySequences_of_enumerable`: the powerset of a
countable type is no larger than the continuum. Together with
`Tautology.Foundation.Cardinal.Cantor` this gives
`binarySequences_uncountable`, and the last two theorems transport
uncountability from a continuum bound to any type carrying one.

## Position in the development

Top of the cardinality subtree, above both
`Tautology.Foundation.Cardinal.Cantor` and
`Tautology.Foundation.Cardinal.CantorBernstein`. `RealCardinality` is its
consumer.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- The stand-in for the continuum throughout this file: predicates on
`Nat`, read as binary sequences. -/
abbrev BinarySequences : Type :=
  Nat -> Prop

/-- At least continuum many points: `Nat -> Prop` injects into `alpha`. -/
def ContinuumLowerBound (alpha : Type u) : Prop :=
  CardLE BinarySequences alpha

/-- At most continuum many points: `alpha` injects into `Nat -> Prop`. -/
def ContinuumUpperBound (alpha : Type u) : Prop :=
  CardLE alpha BinarySequences

/-- Exactly the size of the continuum: equipotent to `Nat -> Prop`. -/
def ContinuumSized (alpha : Type u) : Prop :=
  Equipotent alpha BinarySequences

/-- Code a predicate on `alpha` as a predicate on `Nat`: ask it at the
enumerated points, and answer `False` wherever the enumeration is
undefined. -/
def predicateCodeOfEnum {alpha : Type u}
    (e : Nat -> Option alpha) (S : alpha -> Prop) : BinarySequences :=
  fun n =>
    match e n with
    | none => False
    | some x => S x

/-- The code is faithful when the enumeration reaches every point. Pointwise
agreement of predicates becomes equality by `funext` and `propext` -- the
bridge from agreement at each index to equality of predicates. -/
theorem predicateCodeOfEnum_injective
    {alpha : Type u}
    {e : Nat -> Option alpha}
    (he : forall x : alpha, Exists (fun n : Nat => e n = some x)) :
    Injective (predicateCodeOfEnum e) := by
  intro S T hST
  apply funext
  intro x
  apply propext
  constructor
  · intro hx
    cases he x with
    | intro n hn =>
        have hpoint := congrFun hST n
        unfold predicateCodeOfEnum at hpoint
        rw [hn] at hpoint
        simp at hpoint
        rwa [hpoint] at hx
  · intro hx
    cases he x with
    | intro n hn =>
        have hpoint := congrFun hST n
        unfold predicateCodeOfEnum at hpoint
        rw [hn] at hpoint
        simp at hpoint
        rwa [<- hpoint] at hx

/-- The powerset of an enumerable type is no larger than the continuum:
predicates code into binary sequences through the enumeration. -/
theorem powerset_cardLE_binarySequences_of_enumerable
    {alpha : Type u}
    (h : Enumerable alpha) :
    CardLE (alpha -> Prop) BinarySequences := by
  cases h with
  | intro e he =>
      exact Exists.intro (predicateCodeOfEnum e)
        (predicateCodeOfEnum_injective he)

theorem binarySequences_uncountable :
    Uncountable BinarySequences :=
  uncountable_nat_powerset

/-- The two one-sided bounds combine into full continuum size. The
interesting direction is Cantor--Bernstein, which is why this module sits
above it. -/
theorem continuumSized_iff_bounds {alpha : Type u} :
    ContinuumSized alpha <->
      And (ContinuumLowerBound alpha) (ContinuumUpperBound alpha) := by
  unfold ContinuumSized ContinuumLowerBound ContinuumUpperBound
  constructor
  · intro h
    exact And.intro
      (cardLE_symm_of_equipotent h)
      (cardLE_of_equipotent h)
  · intro h
    exact cantor_bernstein h.right h.left

theorem uncountable_of_continuumLowerBound
    {alpha : Type u}
    (h : ContinuumLowerBound alpha) :
    Uncountable alpha :=
  uncountable_of_cardLE_nat_powerset h

theorem uncountable_of_continuumSized
    {alpha : Type u}
    (h : ContinuumSized alpha) :
    Uncountable alpha := by
  have hbounds := (continuumSized_iff_bounds).mp h
  exact uncountable_of_continuumLowerBound hbounds.left

end Cardinal
end Foundation
end Tautology
