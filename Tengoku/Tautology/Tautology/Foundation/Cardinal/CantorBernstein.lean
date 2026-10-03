import Tengoku.Tautology.Tautology.Foundation.Cardinal.Choice

/-!
# Cantor--Bernstein, by chains

Injections both ways give a bijection. The bijection is not obtained
abstractly, it is written down, and the whole file is the bookkeeping that
makes the definition legitimate.

The construction is the classical chain argument. Start from the points of
`alpha` outside the range of `g` -- those cannot have come from `beta` -- and
close that set under the round trip `g . f`. `Chain` is that sequence of sets,
`Core` is their union. On the `Core` the bijection uses `f`; off it, every
point is in the range of `g` and has a unique preimage there, so the bijection
uses `g` inverted. `core_predecessor_of_core_range` is the lemma that keeps
the two halves from colliding: a point of the `Core` whose `g`-preimage exists
came from a `Core` point one step earlier, so nothing is claimed twice.

`equipotent_iff_cardLE_both` is the statement most consumers want -- two types
are equipotent exactly when each injects into the other -- and it is what
makes `CardLE` behave like an order rather than a preorder with no
antisymmetry.

## What it costs

`preimageOfNotCore` is `noncomputable`: inverting `g` off the `Core` is a
choice of preimage, so this file inherits the choice boundary of
`Tautology.Foundation.Cardinal.Choice` rather than adding a new one. Everything
else here is explicit.

## Position in the development

Above `Tautology.Foundation.Cardinal.Choice`, and consumed by
`Tautology.Foundation.Cardinal.Continuum`, which needs antisymmetry to turn two
bounds into an equipotence.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

namespace CantorBernstein

/-- The image of `f` as a predicate: a point of the target reached from
somewhere in the source. Its complement is stage `0` of the chain below. -/
def Range {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) : beta -> Prop :=
  fun y => Exists (fun x : alpha => f x = y)

/-- One round of the closure: the image of `S` under the composite `g . f`,
that is, the points `g (f a)` for `a` in `S`. -/
def StepSet {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (g : beta -> alpha)
    (S : alpha -> Prop) : alpha -> Prop :=
  fun x => Exists (fun a : alpha => And (S a) (x = g (f a)))

/-- The stages of the closure: stage `0` is the part of `alpha` that `g`
does not reach, and each later stage is the round trip applied to the
previous one. -/
def Chain {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (g : beta -> alpha) :
    Nat -> alpha -> Prop
  | 0 => fun x => Not (Range g x)
  | n + 1 => StepSet f g (Chain f g n)

/-- The union of all stages of the chain: the part of `alpha` on which the
constructed bijection will follow `f`. -/
def Core {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (g : beta -> alpha) : alpha -> Prop :=
  fun x => Exists (fun n : Nat => Chain f g n x)

theorem core_of_chain
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha} {n : Nat}
    (h : Chain f g n x) :
    Core f g x :=
  Exists.intro n h

/-- The Core is closed under the round trip: `g (f x)` is back in it
whenever `x` is. This one-step fact is what convicts the mixed cases in the
injectivity proof. -/
theorem core_step
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha}
    (hx : Core f g x) :
    Core f g (g (f x)) := by
  cases hx with
  | intro n hn =>
      exact Exists.intro (n + 1)
        (Exists.intro x (And.intro hn rfl))

/-- Off the Core every point is reached by `g`. The contrapositive is
immediate from the construction: a point `g` misses would already sit in
stage `0` of the chain. -/
theorem range_of_not_core
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha}
    (hx : Not (Core f g x)) :
    Range g x := by
  classical
  by_cases hr : Range g x
  · exact hr
  · have h0 : Chain f g 0 x := hr
    exact False.elim (hx (Exists.intro 0 h0))

/-- For a point outside the Core, a chosen `g`-preimage. The one genuinely
selection-dependent step of the construction, hence `noncomputable`. -/
noncomputable def preimageOfNotCore
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha}
    (hx : Not (Core f g x)) : beta := by
  classical
  exact Classical.choose (range_of_not_core (f := f) (g := g) hx)

theorem preimageOfNotCore_spec
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha}
    (hx : Not (Core f g x)) :
    g (preimageOfNotCore (f := f) (g := g) hx) = x := by
  classical
  unfold preimageOfNotCore
  exact Classical.choose_spec (range_of_not_core (f := f) (g := g) hx)

/-- The Cantor--Bernstein bijection itself: follow `f` on the Core, and the
chosen `g`-preimage off it. -/
noncomputable def map
    {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (g : beta -> alpha) : alpha -> beta := by
  classical
  exact fun x =>
    if hx : Core f g x then
      f x
    else
      preimageOfNotCore (f := f) (g := g) hx

theorem map_of_core
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha}
    (hx : Core f g x) :
    map f g x = f x := by
  classical
  unfold map
  simp [hx]

theorem g_map_of_not_core
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    {x : alpha}
    (hx : Not (Core f g x)) :
    g (map f g x) = x := by
  classical
  unfold map
  simp [hx, preimageOfNotCore_spec (f := f) (g := g) hx]

/-- No target is claimed twice: if `g y` lies in the Core, then `y` was
already the `f`-image of a Core point one stage earlier, with injectivity of
`g` identifying the predecessor. This keeps the two halves of `map` from
colliding. -/
theorem core_predecessor_of_core_range
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    (hg : Injective g)
    {y : beta}
    (hy : Core f g (g y)) :
    Exists (fun x : alpha => And (Core f g x) (y = f x)) := by
  cases hy with
  | intro n hn =>
      cases n with
      | zero =>
          have hr : Range g (g y) := Exists.intro y rfl
          exact False.elim (hn hr)
      | succ n =>
          cases hn with
          | intro x hx =>
              have hxcore : Core f g x :=
                Exists.intro n hx.left
              have hyfx : y = f x :=
                hg hx.right
              exact Exists.intro x (And.intro hxcore hyfx)

/-- Injectivity by the cases of Core membership. Each mixed case convicts
itself: the round trip drags the off-Core point into the Core,
contradicting where it was assumed to sit. -/
theorem map_injective
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    (hf : Injective f) :
    Injective (map f g) := by
  intro x y hxy
  by_cases hx : Core f g x
  · by_cases hy : Core f g y
    · apply hf
      calc
        f x = map f g x := (map_of_core hx).symm
        _ = map f g y := hxy
        _ = f y := map_of_core hy
    · have hycore : Core f g y := by
        have hgy : g (map f g y) = y :=
          g_map_of_not_core hy
        rw [<- hgy, <- hxy, map_of_core hx]
        exact core_step hx
      exact False.elim (hy hycore)
  · by_cases hy : Core f g y
    · have hxcore : Core f g x := by
        have hgx : g (map f g x) = x :=
          g_map_of_not_core hx
        rw [<- hgx, hxy, map_of_core hy]
        exact core_step hy
      exact False.elim (hx hxcore)
    · have hgx : g (map f g x) = x :=
        g_map_of_not_core hx
      have hgy : g (map f g y) = y :=
        g_map_of_not_core hy
      calc
        x = g (map f g x) := hgx.symm
        _ = g (map f g y) := by rw [hxy]
        _ = y := hgy

/-- Every target is reached: when `g y` is in the Core the predecessor lemma
supplies `y` as an `f`-image, and off the Core the point `g y` maps back to
`y`. -/
theorem map_surjective
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    (hg : Injective g) :
    Surjective (map f g) := by
  intro y
  by_cases hgy : Core f g (g y)
  · cases core_predecessor_of_core_range hg hgy with
    | intro x hx =>
        refine Exists.intro x ?_
        rw [map_of_core hx.left, hx.right]
  · refine Exists.intro (g y) ?_
    apply hg
    exact g_map_of_not_core hgy

theorem map_bijective
    {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} {g : beta -> alpha}
    (hf : Injective f) (hg : Injective g) :
    Bijective (map f g) :=
  And.intro (map_injective hf) (map_surjective hg)

end CantorBernstein

/-- Injections both ways yield a bijection, and the bijection is written
down: `CantorBernstein.map f g` built from the two witnesses. No abstract
existence argument is involved. -/
theorem cantor_bernstein
    {alpha : Type u} {beta : Type v}
    (hab : CardLE alpha beta) (hba : CardLE beta alpha) :
    Equipotent alpha beta := by
  cases hab with
  | intro f hf =>
      cases hba with
      | intro g hg =>
          exact Exists.intro (CantorBernstein.map f g)
            (CantorBernstein.map_bijective hf hg)

/-- Antisymmetry of `CardLE` up to equipotence: each type injects into the
other exactly when the two are equipotent. The easy direction weakens a
bijection; the hard one is `cantor_bernstein`. -/
theorem equipotent_iff_cardLE_both
    {alpha : Type u} {beta : Type v} :
    Equipotent alpha beta <-> And (CardLE alpha beta) (CardLE beta alpha) :=
  Iff.intro
    (fun h => And.intro
      (cardLE_of_equipotent h)
      (cardLE_symm_of_equipotent h))
    (fun h => cantor_bernstein h.left h.right)

end Cardinal
end Foundation
end Tautology
