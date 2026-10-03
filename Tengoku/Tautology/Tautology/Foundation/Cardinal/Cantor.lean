import Tengoku.Tautology.Tautology.Foundation.Cardinal.Choice
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Countable

/-!
# Cantor's theorem, and the uncountability it exports

A type never surjects onto its powerset. Here a powerset is `alpha -> Prop`,
the same predicate representation used everywhere in this library, so the
diagonal argument is the direct one: given `f : alpha -> (alpha -> Prop)`,
the predicate `fun x => Not (f x x)` is not in its image.

`singletonPred` supplies the easy direction, `cardLE_powerset`, and together
they give `cantor_powerset_strict` in the strong sense of
`Tautology.Foundation.Cardinal.Maps` -- not merely "not equipotent" but "no
injection back". Specialising to `Nat` yields `uncountable_nat_powerset`.

## The last two theorems are the ones other regions call

`uncountable_of_cardLE_nat_powerset` and `uncountable_of_cardGE_nat_powerset`
transport uncountability along a comparison: a type that `Nat -> Prop` injects
into, or that surjects onto `Nat -> Prop`, is uncountable. That is how
uncountability reaches a type that has nothing to do with powersets --
`RealCardinality` proves the reals uncountable by exhibiting such a comparison
rather than by running a diagonal argument on the reals themselves. Reading
this file as being only about powersets misses what it is for.

## Position in the development

Above `Tautology.Foundation.Cardinal.Choice` and
`Tautology.Foundation.Cardinal.Countable` -- the latter because uncountability
is stated through the partial-enumeration interface
`uncountable_of_every_option_enum_misses`, which is exactly the shape a
diagonal argument produces. Below `Tautology.Foundation.Cardinal.Continuum`.

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

/-- The singleton embedding of a type into its own powerset: `x` goes to the
predicate `y = x`. Distinct points give distinct predicates, which is the
injection of `cardLE_powerset`. -/
def singletonPred {alpha : Type u} (x : alpha) : alpha -> Prop :=
  fun y => y = x

theorem singletonPred_injective {alpha : Type u} :
    Injective (singletonPred : alpha -> alpha -> Prop) := by
  intro x y h
  have hx : singletonPred x x := rfl
  rw [h] at hx
  exact hx

theorem cardLE_powerset (alpha : Type u) :
    CardLE alpha (alpha -> Prop) :=
  Exists.intro singletonPred singletonPred_injective

/-- No map reaches every predicate: the diagonal `fun x => Not (f x x)`
disagrees with `f a` at `a` itself, whichever way `f a` answers. -/
theorem no_surjection_to_powerset
    {alpha : Type u}
    (f : alpha -> (alpha -> Prop)) :
    Not (Surjective f) := by
  intro hf
  let diagonal : alpha -> Prop := fun x => Not (f x x)
  cases hf diagonal with
  | intro a ha =>
      by_cases hfa : f a a
      · have hdiag : diagonal a := by
          rw [← ha]
          exact hfa
        exact hdiag hfa
      · have hdiag : diagonal a := hfa
        rw [← ha] at hdiag
        exact hfa hdiag

theorem not_cardGE_powerset (alpha : Type u) :
    Not (CardGE alpha (alpha -> Prop)) := by
  intro h
  cases h with
  | intro f hf =>
      exact no_surjection_to_powerset f hf

/-- The powerset does not inject back into the type. There is no second
diagonal here: such an injection would, since `alpha -> Prop` is nonempty,
give a surjection the other way, and that is what Cantor forbids. -/
theorem not_cardLE_powerset_to_self (alpha : Type u) :
    Not (CardLE (alpha -> Prop) alpha) := by
  intro h
  haveI : Nonempty (alpha -> Prop) :=
    ⟨fun _ => False⟩
  have hsurj : CardGE alpha (alpha -> Prop) :=
    cardLE_to_cardGE_swap_of_nonempty h
  exact not_cardGE_powerset alpha hsurj

theorem cantor_powerset_strict (alpha : Type u) :
    CardLT alpha (alpha -> Prop) :=
  And.intro
    (cardLE_powerset alpha)
    (not_cardLE_powerset_to_self alpha)

/-- The powerset of `Nat` is uncountable: an enumeration of it would be a
surjection from `Nat` onto it, which Cantor forbids. -/
theorem uncountable_nat_powerset :
    Uncountable (Nat -> Prop) := by
  intro h
  have hsurj : CardGE Nat (Nat -> Prop) :=
    cardGE_nat_of_enumerable h
  exact not_cardGE_powerset Nat hsurj

/-- Uncountability transports along an injection out of `Nat -> Prop`: a
type that the binary sequences embed into cannot be enumerable, since an
enumeration would pull the powerset of `Nat` back into `Nat`. -/
theorem uncountable_of_cardLE_nat_powerset
    {alpha : Type u}
    (h : CardLE (Nat -> Prop) alpha) :
    Uncountable alpha := by
  intro henum
  cases h with
  | intro f hf =>
      haveI : Nonempty alpha :=
        ⟨f (fun _ : Nat => False)⟩
      have hGE : CardGE Nat alpha :=
        cardGE_nat_of_enumerable henum
      have hLE : CardLE (Nat -> Prop) Nat :=
        cardLE_trans (Exists.intro f hf) (cardGE_to_cardLE_swap hGE)
      exact not_cardLE_powerset_to_self Nat hLE

/-- The surjection form of the same transport: a type that maps onto
`Nat -> Prop` would make the powerset of `Nat` enumerable itself. -/
theorem uncountable_of_cardGE_nat_powerset
    {alpha : Type u}
    (h : CardGE alpha (Nat -> Prop)) :
    Uncountable alpha := by
  intro henum
  cases h with
  | intro f hf =>
      have hpow : Enumerable (Nat -> Prop) :=
        enumerable_of_surjective henum hf
      exact uncountable_nat_powerset hpow

end Cardinal
end Foundation
end Tautology
