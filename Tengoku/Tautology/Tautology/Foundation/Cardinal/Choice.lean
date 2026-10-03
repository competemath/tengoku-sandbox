import Tengoku.Tautology.Tautology.Foundation.Cardinal.Maps

/-!
# Where choice enters the cardinality theory

`Tautology.Foundation.Cardinal.Maps` defines `CardLE` by injections and
`CardGE` by surjections and relates them not at all, because relating them
needs to invert a map. This module does the inverting, and every construction
in it is `noncomputable` and goes through `Classical.choose`. Isolating that in
one file is the point: a reader who wants to know what the size comparisons
cost in logical strength reads this module and no other.

Two constructions, and they are not symmetric.

`rightInverse` turns a surjection into an injection by choosing a preimage for
each point, and needs nothing else -- so `CardGE alpha beta` gives
`CardLE beta alpha` unconditionally. `leftProjectionOfInjection` goes the other
way, turning an injection into a surjection, and **it needs
`[Nonempty alpha]`**: a point of `beta` outside the image has to be sent
somewhere, and with `alpha` empty there is nowhere to send it. Hence
`cardLE_to_cardGE_swap_of_nonempty` and everything built on it carry that
hypothesis while their counterparts do not. Expecting the two directions to
look alike is the standard misreading here.

`equipotent_symm` belongs to the same story. Symmetry of equipotence looks
like it should be free, but a bijection is only given as a map with two
properties, and producing its inverse is again a choice of preimages.

## Position in the development

Directly above `Tautology.Foundation.Cardinal.Maps`, and below both
`Tautology.Foundation.Cardinal.CantorBernstein` and
`Tautology.Foundation.Cardinal.Cantor`, each of which needs to move between
injections and surjections.

## Role

Implementation, and the choice boundary of the subtree. `Classical.choice` is
one of the three axioms this library permits; this file is where the
cardinality results acquire it.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- For each point of the target, a chosen preimage under the surjection `f`.
One `Classical.choose` per point, which is why the definition is
`noncomputable`; its characterising equation is `rightInverse_spec`. -/
noncomputable def rightInverse
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta}
    (hf : Surjective f) : beta -> alpha := by
  classical
  exact fun y => Classical.choose (hf y)

/-- The chosen preimage really is a preimage: `f` sends it back to `y`.
Downstream arguments extract preimages through this equation instead of
touching the choice. -/
theorem rightInverse_spec
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta}
    (hf : Surjective f) (y : beta) :
    f (rightInverse hf y) = y := by
  classical
  unfold rightInverse
  exact Classical.choose_spec (hf y)

/-- The chosen preimages of distinct points are distinct, since each maps back
onto its own target. This is what turns a surjection into an injection running
the other way. -/
theorem injective_rightInverse_of_surjective
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta}
    (hf : Surjective f) :
    Injective (rightInverse hf) := by
  intro x y h
  have hx := rightInverse_spec hf x
  have hy := rightInverse_spec hf y
  rw [h] at hx
  rw [hy] at hx
  exact hx.symm

/-- A surjection `alpha -> beta` yields an injection `beta -> alpha`, namely
the chosen-preimage map. This direction carries no side condition; the
converse is `cardLE_to_cardGE_swap_of_nonempty`. -/
theorem cardGE_to_cardLE_swap
    {alpha : Type u} {beta : Type v}
    (h : CardGE alpha beta) :
    CardLE beta alpha := by
  cases h with
  | intro f hf =>
      exact Exists.intro (rightInverse hf)
        (injective_rightInverse_of_surjective hf)

/-- For a bijection `f` the right inverse reaches every point: each `x` is hit
at the index `f x`, and injectivity of `f` is what identifies the chosen
preimage of `f x` with `x`. -/
theorem rightInverse_surjective_of_bijective
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta}
    (hf : Bijective f) :
    Surjective (rightInverse hf.right) := by
  intro x
  refine Exists.intro (f x) ?_
  apply hf.left
  exact rightInverse_spec hf.right (f x)

theorem rightInverse_bijective_of_bijective
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta}
    (hf : Bijective f) :
    Bijective (rightInverse hf.right) :=
  And.intro
    (injective_rightInverse_of_surjective hf.right)
    (rightInverse_surjective_of_bijective hf)

/-- Symmetry of equipotence is not free: the flipped bijection is
`rightInverse` of the given one, so this is another passage through choice
rather than a property of the definition. -/
theorem equipotent_symm
    {alpha : Type u} {beta : Type v}
    (h : Equipotent alpha beta) :
    Equipotent beta alpha := by
  cases h with
  | intro f hf =>
      exact Exists.intro (rightInverse hf.right)
        (rightInverse_bijective_of_bijective hf)

theorem cardLE_of_equipotent
    {alpha : Type u} {beta : Type v}
    (h : Equipotent alpha beta) :
    CardLE alpha beta := by
  cases h with
  | intro f hf =>
      exact Exists.intro f hf.left

theorem cardGE_of_equipotent
    {alpha : Type u} {beta : Type v}
    (h : Equipotent alpha beta) :
    CardGE alpha beta := by
  cases h with
  | intro f hf =>
      exact Exists.intro f hf.right

theorem cardLE_symm_of_equipotent
    {alpha : Type u} {beta : Type v}
    (h : Equipotent alpha beta) :
    CardLE beta alpha :=
  cardLE_of_equipotent (equipotent_symm h)

theorem cardGE_symm_of_equipotent
    {alpha : Type u} {beta : Type v}
    (h : Equipotent alpha beta) :
    CardGE beta alpha :=
  cardGE_of_equipotent (equipotent_symm h)

/-- A left projection for an injection `f`: the preimage on the image of `f`,
and one fixed point of `alpha` everywhere else, supplied by `[Nonempty alpha]`.
Injectivity plays no part in the definition -- the hypothesis is carried for
the reading -- and enters only through `leftProjectionOfInjection_spec`. -/
noncomputable def leftProjectionOfInjection
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha]
    {f : alpha -> beta}
    (_hf : Injective f) : beta -> alpha := by
  classical
  exact fun y =>
    if h : Exists (fun x : alpha => f x = y) then
      Classical.choose h
    else
      Classical.choice ‹Nonempty alpha›

/-- On the image of `f` the projection undoes `f`. This is where injectivity
is used: it makes the chosen preimage the unique candidate, so the choice
cannot go wrong. -/
theorem leftProjectionOfInjection_spec
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha]
    {f : alpha -> beta}
    (hf : Injective f) (x : alpha) :
    leftProjectionOfInjection hf (f x) = x := by
  classical
  unfold leftProjectionOfInjection
  have hmem : Exists (fun z : alpha => f z = f x) :=
    Exists.intro x rfl
  simp [hmem, hf (Classical.choose_spec hmem)]

theorem surjective_leftProjection_of_injective
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha]
    {f : alpha -> beta}
    (hf : Injective f) :
    Surjective (leftProjectionOfInjection hf) := by
  intro x
  exact Exists.intro (f x) (leftProjectionOfInjection_spec hf x)

/-- The converse bridge: an injection `alpha -> beta` yields a surjection
`beta -> alpha`, the preimage on the image of `f` and the `[Nonempty alpha]`
witness off it. The side condition is unavoidable -- with `alpha` empty there
is nowhere for the rest of `beta` to go. -/
theorem cardLE_to_cardGE_swap_of_nonempty
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha]
    (h : CardLE alpha beta) :
    CardGE beta alpha := by
  cases h with
  | intro f hf =>
      exact Exists.intro (leftProjectionOfInjection hf)
        (surjective_leftProjection_of_injective hf)

theorem cardLE_iff_cardGE_swap_of_nonempty
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha] :
    CardLE alpha beta <-> CardGE beta alpha :=
  Iff.intro
    cardLE_to_cardGE_swap_of_nonempty
    cardGE_to_cardLE_swap

/-- The strict bridge, injection form. `[Nonempty alpha]` sits on the domain
of the injection being projected: the rest of `beta` must be sent into
`alpha`. -/
theorem cardLT_to_cardGT_swap_of_nonempty
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha]
    (h : CardLT alpha beta) :
    CardGT beta alpha := by
  constructor
  · exact cardLE_to_cardGE_swap_of_nonempty h.left
  · intro hsurj
    exact h.right (cardGE_to_cardLE_swap hsurj)

/-- The mirror of `cardLT_to_cardGT_swap_of_nonempty`, with the nonemptiness
on `beta`: there the projected injection runs from `beta`, so the points of
`alpha` outside its image need a place in `beta` to go. -/
theorem cardGT_to_cardLT_swap_of_nonempty
    {alpha : Type u} {beta : Type v}
    [Nonempty beta]
    (h : CardGT beta alpha) :
    CardLT alpha beta := by
  constructor
  · exact cardGE_to_cardLE_swap h.left
  · intro hinj
    exact h.right (cardLE_to_cardGE_swap_of_nonempty hinj)

theorem cardLT_iff_cardGT_swap_of_nonempty
    {alpha : Type u} {beta : Type v}
    [Nonempty alpha] [Nonempty beta] :
    CardLT alpha beta <-> CardGT beta alpha :=
  Iff.intro
    cardLT_to_cardGT_swap_of_nonempty
    cardGT_to_cardLT_swap_of_nonempty

end Cardinal
end Foundation
end Tautology
