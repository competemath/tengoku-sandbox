import Tengoku.Tautology.Tautology.RealTopology.Basic
import Tengoku.Tautology.Tautology.RealBootstrap.RationalDensity
import Tengoku.Tautology.Tautology.RealBootstrap.InternalCountable

/-!
# A countable basis of rational-endpoint intervals

The countability strand of the region. An open interval is coded by a pair of
internal rationals `p.fst < p.snd`; the codes form a countable alphabet,
every open set is the union of the coded intervals it contains, and every
nonempty open set contains an internal rational.

The file splits cleanly along its two namespaces, and the split is exactly the
use of completeness. Over any ordered field one gets the countability of the
alphabet: the internal rationals are countable
(`Tautology.RealBootstrap.InternalCountable`), hence so are pairs of them,
hence so is the subtype cut out by `p.fst < p.snd`. The basis statements need
one further step -- fitting a whole coded interval inside an open set around a
given point -- and that rests on density of the internal rationals, which
`Tautology.RealBootstrap.RationalDensity` states for a Dedekind-complete field.
That is the only appeal to completeness here.

## Position and role

Implementation module. `Tautology.RealTopology.Lindelof` turns this basis into
countable subcovers, and `Tautology.RealCardinality.ContinuumUpper` reuses the
same alphabet to code points of the field by the intervals containing them --
which is why the cardinality region depends on this one.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- A code for an open interval: a pair of internal rationals `p.fst <
p.snd`. The internal rationals form a countable set in any ordered field,
so these codes are a countable family of intervals -- the parameter space
of the countable basis built below. -/
def InternalRatIntervalParam (p : Prod alpha alpha) : Prop :=
  And (InternalRat F p.fst)
    (And (InternalRat F p.snd) (F.lt p.fst p.snd))

/-- The open interval decoded from a code `p`. The theorems below spell
`OpenInterval p.fst p.snd` out directly rather than passing through this
name; it records the decoding as part of the vocabulary. -/
def InternalRatOpenInterval (p : Prod alpha alpha) : alpha -> Prop :=
  OpenInterval F p.fst p.snd

/-- The code space is countable over any ordered field: it is a subset of
the product of the countable set of internal rationals with itself. This
is the ordered-field half of the basis story, with no completeness in it. -/
theorem internalRatIntervalParam_countable :
    Foundation.Cardinal.CountableSet (InternalRatIntervalParam F) := by
  have hprod :
      Foundation.Cardinal.CountableSet
        (Foundation.Cardinal.SetProd
          (InternalRat F) (InternalRat F)) :=
    Foundation.Cardinal.countableSet_prod
      (internalRat_countable F)
      (internalRat_countable F)
  exact Foundation.Cardinal.countableSet_mono hprod
    (fun p hp => And.intro hp.left hp.right.left)

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- Between any two bounds `left < x < right` sits a whole coded interval:
internal rationals with `left < p.fst < x < p.snd < right`. This is where
completeness enters the file, through the density of the internal rationals
(`exists_internalRat_between` of `Tautology.RealBootstrap.RationalDensity`,
itself proved under Dedekind completeness). -/
theorem exists_internalRat_interval_inside {left x right : alpha}
    (hlx : C.field.lt left x)
    (hxr : C.field.lt x right) :
    Exists (fun p : Prod alpha alpha =>
      And (C.field.InternalRatIntervalParam p)
        (And (C.field.lt left p.fst)
          (And (C.field.lt p.fst x)
            (And (C.field.lt x p.snd)
              (C.field.lt p.snd right))))) := by
  cases exists_internalRat_between C hlx with
  | intro a ha =>
      cases exists_internalRat_between C hxr with
      | intro b hb =>
          refine Exists.intro (a, b) ?_
          have hab : C.field.lt a b :=
            IsOrderedFieldBaseLike.lt_trans C.field ha.right.right hb.right.left
          exact And.intro
            (And.intro ha.left (And.intro hb.left hab))
            (And.intro ha.right.left
              (And.intro ha.right.right
                (And.intro hb.right.left hb.right.right)))

/-- The pointwise basis property: every point `x` of an open set `U` lies in
a coded interval that is itself contained in `U`. Openness supplies an
interval around `x` inside `U`, and the density step above shrinks that
interval to a coded one. -/
theorem internalRatInterval_basis_at_open
    {U : alpha -> Prop}
    (hU : C.field.IsOpen U)
    {x : alpha}
    (hx : U x) :
    Exists (fun p : Prod alpha alpha =>
      And (C.field.InternalRatIntervalParam p)
        (And (C.field.OpenInterval p.fst p.snd x)
          (forall y : alpha,
            C.field.OpenInterval p.fst p.snd y -> U y))) := by
  cases hU x hx with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          cases hright with
          | intro hlx hrest =>
              cases hrest with
              | intro hxr hinside =>
                  cases exists_internalRat_interval_inside C hlx hxr with
                  | intro p hp =>
                      refine Exists.intro p ?_
                      have hpx :
                          C.field.OpenInterval p.fst p.snd x :=
                        And.intro hp.right.right.left
                          hp.right.right.right.left
                      have hsub :
                          forall y : alpha,
                            C.field.OpenInterval p.fst p.snd y -> U y := by
                        intro y hy
                        apply hinside y
                        exact And.intro
                          (IsOrderedFieldBaseLike.lt_trans C.field
                            hp.right.left hy.left)
                          (IsOrderedFieldBaseLike.lt_trans C.field
                            hy.right hp.right.right.right.right)
                      exact And.intro hp.left (And.intro hpx hsub)

/-- Every nonempty open set contains an internal rational -- density in the
form consumers want it, with no interval bookkeeping attached. This is the
statement `Tautology.RealConnectedness.ConnectedComponents` uses to place a
rational inside an open component. -/
theorem exists_internalRat_mem_of_open_nonempty
    {U : alpha -> Prop}
    (hU : C.field.IsOpen U)
    (hne : Exists (fun x : alpha => U x)) :
    Exists (fun q : alpha =>
      And (C.field.InternalRat q) (U q)) := by
  cases hne with
  | intro x hx =>
      cases internalRatInterval_basis_at_open C hU hx with
      | intro p hp =>
          cases exists_internalRat_between C hp.right.left.left with
          | intro q hq =>
              have hq_right : C.field.lt q p.snd :=
                IsOrderedFieldBaseLike.lt_trans C.field
                  hq.right.right hp.right.left.right
              have hq_interval :
                  C.field.OpenInterval p.fst p.snd q :=
                And.intro hq.right.left hq_right
              exact Exists.intro q
                (And.intro hq.left (hp.right.right q hq_interval))

/-- Every open set is a countable union of coded open intervals: the
countable-basis result. `J` collects the codes whose interval stays inside
`U`; it is countable as a subset of the code space, and the pointwise
equivalence is the basis lemma applied at each point. -/
theorem open_eq_countable_internalRatInterval_union
    {U : alpha -> Prop}
    (hU : C.field.IsOpen U) :
    Exists
      (fun J : Prod alpha alpha -> Prop =>
        And (Foundation.Cardinal.CountableSet J)
          (forall x : alpha,
            U x <->
              Exists
                (fun p : Prod alpha alpha =>
                  And (J p) (C.field.OpenInterval p.fst p.snd x)))) := by
  let J : Prod alpha alpha -> Prop :=
    fun p =>
      And (C.field.InternalRatIntervalParam p)
        (forall y : alpha,
          C.field.OpenInterval p.fst p.snd y -> U y)
  refine Exists.intro J ?_
  constructor
  · exact Foundation.Cardinal.countableSet_mono
      (C.field.internalRatIntervalParam_countable)
      (fun p hp => hp.left)
  · intro x
    constructor
    · intro hx
      cases C.internalRatInterval_basis_at_open hU hx with
      | intro p hp =>
          exact Exists.intro p
            (And.intro (And.intro hp.left hp.right.right) hp.right.left)
    · intro hx
      cases hx with
      | intro p hp =>
          exact hp.left.right x hp.right

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
