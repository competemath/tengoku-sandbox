/-!
# Comparing sizes by maps

The vocabulary the whole cardinality subtree is written in: injective,
surjective and bijective maps, `Equipotent` for the existence of a bijection,
and the four comparisons. Everything is universe polymorphic, so the two types
being compared may live in different universes -- which is what lets the same
statements apply to `Nat`, to a carrier of the reals, and to a type of
functions between them.

## `CardLE` and `CardGE` are two definitions, not one definition twice

`CardLE alpha beta` is the existence of an injection `alpha -> beta`;
`CardGE alpha beta` is the existence of a surjection `alpha -> beta`. Reading
the second as a mirror of the first is the standard way to misread this file.
They are separately defined, and nothing here relates them: turning a
surjection into an injection needs a right inverse, and that needs choice, so
those bridges live in `Tautology.Foundation.Cardinal.Choice` and carry a
nonemptiness hypothesis in one direction. **This module deliberately contains
only what is provable without choice** -- reflexivity, transitivity, and the
behaviour under composition and identity.

The strict forms are also worth reading carefully. `CardLT alpha beta` is
`CardLE alpha beta` together with the *failure* of `CardLE beta alpha`, not
"equipotent fails". That is the stronger and more usable form: it is what
Cantor's theorem produces and what the continuum results consume, and the
mixed transitivities (`cardLT_of_cardLT_of_cardLE` and its three siblings) are
stated in it.

## Position in the development

Root of the cardinality subtree, with no imports of any kind. Every
other module under `Foundation/Cardinal/` sits above it.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- Equal images force equal arguments. The two arguments are implicit binders,
so an equation `f x = f y` can be fed straight to `Injective f` without naming
them. -/
def Injective {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) : Prop :=
  forall {x y : alpha}, f x = f y -> x = y

/-- Every point of the target is the image of some point; the witness is
packed in an `Exists`, with the equation oriented `f x = y`. -/
def Surjective {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) : Prop :=
  forall y : beta, Exists (fun x : alpha => f x = y)

/-- Both at once, held as a conjunction: consumers take the halves apart with
`.left` and `.right` rather than unfolding. -/
def Bijective {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) : Prop :=
  And (Injective f) (Surjective f)

/-- Two types are equipotent when some bijection between them exists; the two
types may live in different universes. Symmetry is a theorem in
`Tautology.Foundation.Cardinal.Choice`, not a property of this definition. -/
def Equipotent (alpha : Type u) (beta : Type v) : Prop :=
  Exists (fun f : alpha -> beta => Bijective f)

/-- The weak comparison: some injection from `alpha` into `beta`, with the two
types allowed to live in different universes. -/
def CardLE (alpha : Type u) (beta : Type v) : Prop :=
  Exists (fun f : alpha -> beta => Injective f)

/-- The surjective counterpart of `CardLE`: some surjection from `alpha` onto
`beta`. A separately introduced notion rather than an order dual, and nothing
in this module relates it to `CardLE`; the bridges live in
`Tautology.Foundation.Cardinal.Choice` and are asymmetric. -/
def CardGE (alpha : Type u) (beta : Type v) : Prop :=
  Exists (fun f : alpha -> beta => Surjective f)

/-- Strict comparison, held as a conjunction: an injection one way together
with the failure of the reverse injection. A proof splits it with `.left` and
reassembles it with `cardLT_intro`. -/
def CardLT (alpha : Type u) (beta : Type v) : Prop :=
  And (CardLE alpha beta) (Not (CardLE beta alpha))

/-- The surjective version of `CardLT`: a surjection one way together with the
failure of the reverse surjection. -/
def CardGT (alpha : Type u) (beta : Type v) : Prop :=
  And (CardGE alpha beta) (Not (CardGE beta alpha))

theorem cardLT_intro
    {alpha : Type u} {beta : Type v}
    (hle : CardLE alpha beta)
    (hnle : Not (CardLE beta alpha)) :
    CardLT alpha beta :=
  And.intro hle hnle

theorem cardGT_intro
    {alpha : Type u} {beta : Type v}
    (hge : CardGE alpha beta)
    (hnge : Not (CardGE beta alpha)) :
    CardGT alpha beta :=
  And.intro hge hnge

theorem injective_id (alpha : Type u) :
    Injective (fun x : alpha => x) := by
  intro x y h
  exact h

theorem surjective_id (alpha : Type u) :
    Surjective (fun x : alpha => x) := by
  intro x
  exact Exists.intro x rfl

theorem bijective_id (alpha : Type u) :
    Bijective (fun x : alpha => x) :=
  And.intro (injective_id alpha) (surjective_id alpha)

theorem injective_comp
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    {f : alpha -> beta} {g : beta -> gamma}
    (hf : Injective f) (hg : Injective g) :
    Injective (fun x : alpha => g (f x)) := by
  intro x y h
  exact hf (hg h)

theorem surjective_comp
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    {f : alpha -> beta} {g : beta -> gamma}
    (hf : Surjective f) (hg : Surjective g) :
    Surjective (fun x : alpha => g (f x)) := by
  intro z
  cases hg z with
  | intro y hy =>
      cases hf y with
      | intro x hx =>
          exact Exists.intro x (by
            change g (f x) = z
            rw [hx, hy])

theorem bijective_comp
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    {f : alpha -> beta} {g : beta -> gamma}
    (hf : Bijective f) (hg : Bijective g) :
    Bijective (fun x : alpha => g (f x)) :=
  And.intro
    (injective_comp hf.left hg.left)
    (surjective_comp hf.right hg.right)

theorem cardLE_refl (alpha : Type u) :
    CardLE alpha alpha :=
  Exists.intro (fun x : alpha => x) (injective_id alpha)

theorem cardGE_refl (alpha : Type u) :
    CardGE alpha alpha :=
  Exists.intro (fun x : alpha => x) (surjective_id alpha)

theorem equipotent_refl (alpha : Type u) :
    Equipotent alpha alpha :=
  Exists.intro (fun x : alpha => x) (bijective_id alpha)

theorem cardLT_irrefl (alpha : Type u) :
    Not (CardLT alpha alpha) := by
  intro h
  exact h.right h.left

theorem cardGT_irrefl (alpha : Type u) :
    Not (CardGT alpha alpha) := by
  intro h
  exact h.right h.left

theorem cardLE_trans
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : CardLE alpha beta) (hbc : CardLE beta gamma) :
    CardLE alpha gamma := by
  cases hab with
  | intro f hf =>
      cases hbc with
      | intro g hg =>
          exact Exists.intro (fun x : alpha => g (f x))
            (injective_comp hf hg)

theorem cardLT_of_cardLT_of_cardLE
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : CardLT alpha beta) (hbc : CardLE beta gamma) :
    CardLT alpha gamma := by
  constructor
  · exact cardLE_trans hab.left hbc
  · intro hca
    exact hab.right (cardLE_trans hbc hca)

theorem cardLT_of_cardLE_of_cardLT
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : CardLE alpha beta) (hbc : CardLT beta gamma) :
    CardLT alpha gamma := by
  constructor
  · exact cardLE_trans hab hbc.left
  · intro hca
    exact hbc.right (cardLE_trans hca hab)

theorem cardGE_trans
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : CardGE alpha beta) (hbc : CardGE beta gamma) :
    CardGE alpha gamma := by
  cases hab with
  | intro f hf =>
      cases hbc with
      | intro g hg =>
          exact Exists.intro (fun x : alpha => g (f x))
            (surjective_comp hf hg)

theorem cardGT_of_cardGT_of_cardGE
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : CardGT alpha beta) (hbc : CardGE beta gamma) :
    CardGT alpha gamma := by
  constructor
  · exact cardGE_trans hab.left hbc
  · intro hca
    exact hab.right (cardGE_trans hbc hca)

theorem cardGT_of_cardGE_of_cardGT
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : CardGE alpha beta) (hbc : CardGT beta gamma) :
    CardGT alpha gamma := by
  constructor
  · exact cardGE_trans hab hbc.left
  · intro hca
    exact hbc.right (cardGE_trans hca hab)

theorem equipotent_trans
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (hab : Equipotent alpha beta) (hbc : Equipotent beta gamma) :
    Equipotent alpha gamma := by
  cases hab with
  | intro f hf =>
      cases hbc with
      | intro g hg =>
          exact Exists.intro (fun x : alpha => g (f x))
            (bijective_comp hf hg)

end Cardinal
end Foundation
end Tautology
