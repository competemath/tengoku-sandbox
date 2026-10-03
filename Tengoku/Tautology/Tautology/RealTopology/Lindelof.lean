import Tengoku.Tautology.Tautology.RealTopology.RationalBasis

/-!
# Every open cover has a countable subcover

The Lindelöf property for a Dedekind-complete ordered field, in the concrete
form the library needs: given any open cover of any set, the index predicate
`lindelofChoice` marks a countable subfamily that still covers.

The argument is bookkeeping on top of `Tautology.RealTopology.RationalBasis`
rather than a new idea. Call a code good when it is a genuine parameter and
some member of the cover contains its interval; choosing one such member per
good code, with a fallback so the choice is total, gives a family indexed by
good codes. That index set is the image of a countable set and so is countable,
and every covered point lands in some good code by the basis property. The
empty set is handled by the empty subfamily.

Completeness is not used directly here at all -- it arrives through the basis.

## Position and role

Implementation module, the top of the region. `RealCompactness` wraps
this theorem as `lindelofPrinciple` and feeds it into the route that derives
compactness of a closed interval from sequential compactness, selected in
`RealCompactness/ClosedInterval/Selected.lean`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable {iota : Type u}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The coded interval of `p` stays inside `U`. This is the relation the
subcover extraction turns into index choices. -/
def IntervalSubsets
    (p : Prod alpha alpha) (U : alpha -> Prop) : Prop :=
  forall x : alpha, OpenInterval F p.fst p.snd x -> U x

/-- A code `p` is good for the cover `U` when it is a genuine interval
parameter and some member of the cover contains its interval. Good codes
form a countable set, being a subset of the code space. -/
def LindelofGoodParam
    (U : iota -> alpha -> Prop) (p : Prod alpha alpha) : Prop :=
  And (InternalRatIntervalParam F p)
    (Exists (fun i : iota => IntervalSubsets F p (U i)))

/-- A total choice function on codes: for `p`, an index `i` with
`IntervalSubsets p (U i)` when one exists, and the caller's `fallback`
otherwise. The fallback index is what makes the function total, so the
countable image can be formed without case splitting; it is never
consulted on a good code. -/
noncomputable def lindelofChoice
    (fallback : iota) (U : iota -> alpha -> Prop)
    (p : Prod alpha alpha) : iota := by
  classical
  exact
    if h : Exists (fun i : iota => IntervalSubsets F p (U i)) then
      Classical.choose h
    else
      fallback

/-- The choice function chooses well: whenever a suitable index exists at
all, the chosen one is suitable. This is the only property the main proof
asks of `lindelofChoice`. -/
theorem lindelofChoice_spec
    (fallback : iota) (U : iota -> alpha -> Prop)
    (p : Prod alpha alpha)
    (h : Exists (fun i : iota => IntervalSubsets F p (U i))) :
    IntervalSubsets F p (U (lindelofChoice F fallback U p)) := by
  classical
  unfold lindelofChoice
  rw [dite_eq_left h]
  exact Classical.choose_spec h

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable {iota : Type u}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- Every open cover of every set has a countable subcover, over any
Dedekind-complete ordered field. The subcover's index set is the image of
the good codes under the choice function -- countable because the codes
are -- and completeness enters only through the basis lemma, never in the
extraction itself. An empty `S` is covered by the empty subfamily. This is
the Lindelof principle the closed-interval compactness routes of
`RealCompactness.ClosedInterval` are built on. -/
theorem lindelof
    {S : alpha -> Prop}
    {U : iota -> alpha -> Prop}
    (hopen : forall i : iota, C.field.IsOpen (U i))
    (hcover : IsOrderedFieldBaseLike.Covers U S) :
    IsOrderedFieldBaseLike.CountableSubcover U S := by
  classical
  by_cases hne : Exists S
  · cases hne with
    | intro x0 hx0 =>
        cases hcover x0 hx0 with
        | intro fallback _hfallback =>
            let GoodParam : Prod alpha alpha -> Prop :=
              C.field.LindelofGoodParam U
            let choose : Prod alpha alpha -> iota :=
              C.field.lindelofChoice fallback U
            refine Exists.intro
              (Foundation.Cardinal.Image choose GoodParam) ?_
            constructor
            · have hGoodCount :
                  Foundation.Cardinal.CountableSet GoodParam :=
                Foundation.Cardinal.countableSet_mono
                  (C.field.internalRatIntervalParam_countable)
                  (fun p hp => hp.left)
              exact Foundation.Cardinal.countableSet_image
                hGoodCount choose
            · intro x hx
              cases hcover x hx with
              | intro i hi =>
                  cases C.internalRatInterval_basis_at_open
                      (hopen i) hi with
                  | intro p hp =>
                      have hgood : GoodParam p :=
                        And.intro hp.left
                          (Exists.intro i hp.right.right)
                      have hchoice :
                          IsOrderedFieldBaseLike.IntervalSubsets C.field
                            p (U (choose p)) :=
                        C.field.lindelofChoice_spec fallback U p
                          (Exists.intro i hp.right.right)
                      refine Exists.intro (choose p) ?_
                      exact And.intro
                        (Exists.intro p (And.intro hgood rfl))
                        (hchoice x hp.right.left)
  · refine Exists.intro (fun _ : iota => False) ?_
    constructor
    · exact Foundation.Cardinal.countableSet_empty
    · intro x hx
      exact False.elim (hne (Exists.intro x hx))

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
