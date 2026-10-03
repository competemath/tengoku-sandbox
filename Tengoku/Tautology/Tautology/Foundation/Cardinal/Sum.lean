import Tengoku.Tautology.Tautology.Foundation.Cardinal.Union

/-!
# A sum of two enumerable types is enumerable

Four declarations, and the interest is entirely in how the proof is arranged.
Rather than interleaving two enumerations by parity, the sum type is presented
as a countable *family* of sets -- `sumSide` sends `0` to the image of the left
injection, `1` to the image of the right, and everything above to the empty set
-- and then the countable union of `Tautology.Foundation.Cardinal.Union` does
the work.

That is more machinery than a parity argument would need, and it is the point:
the union lemma already exists, is already proved, and covers this case
without a second interleaving argument to get right. The padding with empty
sets past index `1` is what lets a two-element situation be fed to a
`Nat`-indexed family.

## Position in the development

Above `Tautology.Foundation.Cardinal.Union`. Nothing in the subtree sits above
it; it is a leaf reached through the entry point
`Tautology.Foundation.Cardinal`.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- The sum type dressed as a `Nat`-indexed family: index `0` carries the
image of the left injection, index `1` the image of the right, and every
later index is empty. Handing this to the countable-union lemma is the whole
proof. -/
def sumSide (alpha : Type u) (beta : Type v) :
    Nat -> Sum alpha beta -> Prop
  | 0 => Image Sum.inl (fun _ : alpha => True)
  | n + 1 =>
      match n with
      | 0 => Image Sum.inr (fun _ : beta => True)
      | _ + 1 => fun _ => False

theorem sumSide_countable
    {alpha : Type u} {beta : Type v}
    (ha : Enumerable alpha) (hb : Enumerable beta) :
    forall n : Nat, CountableSet (sumSide alpha beta n) := by
  intro n
  cases n with
  | zero =>
      exact countableSet_image_of_enumerable ha Sum.inl
  | succ n =>
      cases n with
      | zero =>
          exact countableSet_image_of_enumerable hb Sum.inr
      | succ n =>
          exact countableSet_empty

theorem sumSide_covers
    {alpha : Type u} {beta : Type v}
    (s : Sum alpha beta) :
    CountableUnion (sumSide alpha beta) s := by
  cases s with
  | inl a =>
      refine Exists.intro 0 ?_
      exact Exists.intro a (And.intro True.intro rfl)
  | inr b =>
      refine Exists.intro 1 ?_
      exact Exists.intro b (And.intro True.intro rfl)

theorem enumerable_sum
    {alpha : Type u} {beta : Type v}
    (ha : Enumerable alpha) (hb : Enumerable beta) :
    Enumerable (Sum alpha beta) := by
  have hUnion :
      CountableSet (CountableUnion (sumSide alpha beta)) :=
    countableSet_countableUnion (sumSide_countable ha hb)
  have hUniv :
      CountableSet (fun _ : Sum alpha beta => True) :=
    countableSet_mono hUnion
      (fun s _ => sumSide_covers s)
  exact enumerable_of_countableSet_univ hUniv

end Cardinal
end Foundation
end Tautology
