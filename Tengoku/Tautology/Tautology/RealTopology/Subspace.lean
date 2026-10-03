import Tengoku.Tautology.Tautology.RealTopology.Closed

/-!
# The topology a subset inherits

The whole of `Tautology.RealTopology.Closed` redone relative to a fixed set
`S`: relative open and closed sets, relative neighbourhoods, relative interior
and closure, and the trace of an ambient set on `S`. The proofs all work the
same way -- do the corresponding operation to the ambient witness and transport
the pointwise equivalence.

The definition to read carefully is `RelativeOpen`. It says there is an
ambient open `V` with `U x` equivalent to `S x` and `V x` at every point,
rather than asserting a set equation `U = S ∩ V`. The equivalence form pays
twice: no extensionality lemma is needed at use sites, and `U ⊆ S` falls out
for free. `OpenIn` and `RelativeOpen` are two names for the same predicate,
both in active use downstream -- not a deprecation.

The relative De Morgan pair is deliberately asymmetric. The complement of a
relative closed set is relative open with no side condition, while the converse
needs `U ⊆ S`, because a relative complement only sees points of `S`. That
asymmetry is the entire difference between the two statements.

## Position and role

Implementation module. `ClopenIn` is the shape
`Tautology.RealConnectedness.Connected` tests connectedness with, and the two
cover-transport theorems are what let a relative open cover be lifted to an
ambient one and cut back down. Stated over an arbitrary ordered field;
completeness plays no part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- `U` is open in `S` when it is the trace on `S` of some ambient open set:
some open `V` with, pointwise, `U x` if and only if `S x` and `V x`. Stated
as an iff rather than as a set equality, so applying it needs no
extensionality lemma; the shape also forces `U` to be a subset of `S`. -/
def RelativeOpen (S U : alpha -> Prop) : Prop :=
  Exists
    (fun V : alpha -> Prop =>
      And (IsOpen F V)
        (forall x : alpha, U x <-> And (S x) (V x)))

/-- `U` is closed in `S` when it is the trace on `S` of some ambient closed
set, in the same pointwise-iff shape as `RelativeOpen`. -/
def RelativeClosed (S U : alpha -> Prop) : Prop :=
  Exists
    (fun V : alpha -> Prop =>
      And (IsClosed F V)
        (forall x : alpha, U x <-> And (S x) (V x)))

/-- `RelativeOpen` under its second name, "open in `S`"; a definitional
restatement, with both vocabularies in use downstream. -/
def OpenIn (S U : alpha -> Prop) : Prop :=
  RelativeOpen F S U

/-- `RelativeClosed` restated as "closed in `S`", the companion of
`OpenIn`. -/
def ClosedIn (S U : alpha -> Prop) : Prop :=
  RelativeClosed F S U

/-- A subset of `S` both open and closed in `S`. This is the shape in which
connectedness is tested: `Tautology.RealConnectedness.Connected` proves a set
connected exactly when its clopen subsets are only the empty set and `S`
itself. -/
def ClopenIn (S U : alpha -> Prop) : Prop :=
  And (OpenIn F S U) (ClosedIn F S U)

/-- A relative neighbourhood of `x`: `x` is a point of `S` lying in a
relatively open `U`. Point, membership and openness bundled in one
predicate. -/
def RelativeNeighborhood (S U : alpha -> Prop) (x : alpha) : Prop :=
  And (S x) (And (U x) (RelativeOpen F S U))

/-- The relative form of `InteriorPoint`: `x` is a point of `S` with a
relatively open set around it, contained in `A`. -/
def InteriorPointIn (S A : alpha -> Prop) (x : alpha) : Prop :=
  And (S x)
    (Exists
      (fun U : alpha -> Prop =>
        And (RelativeOpen F S U)
          (And (U x) (SetPred.Subset U A))))

/-- The relative form of `ClosurePoint`: a point `x` of `S` such that every
relatively open set containing `x` also contains a point of `A`, the
encounter again happening inside the given set. -/
def ClosurePointIn (S A : alpha -> Prop) (x : alpha) : Prop :=
  And (S x)
    (forall U : alpha -> Prop,
      RelativeOpen F S U ->
        U x -> Exists (fun y : alpha => And (A y) (U y)))

/-- The closure of `A` inside `S`, aggregated pointwise from
`ClosurePointIn`; points outside `S` never belong to it. -/
def ClosureIn (S A : alpha -> Prop) : alpha -> Prop :=
  fun x => ClosurePointIn F S A x

/-- The trace of `V` on `S`, literally the intersection: the bridge along
which ambient open and closed sets become relative ones. -/
def Trace (S V : alpha -> Prop) : alpha -> Prop :=
  SetPred.Inter S V

theorem openIn_subset {S U : alpha -> Prop}
    (hU : OpenIn F S U) :
    SetPred.Subset U S := by
  cases hU with
  | intro V hV =>
      intro x hxU
      exact ((hV.right x).mp hxU).left

theorem closedIn_subset {S U : alpha -> Prop}
    (hU : ClosedIn F S U) :
    SetPred.Subset U S := by
  cases hU with
  | intro V hV =>
      intro x hxU
      exact ((hV.right x).mp hxU).left

/-- Relative openness is extensional in the set: it transfers along `Same`
with the ambient `S` untouched. -/
theorem relativeOpen_congr {S U V : alpha -> Prop}
    (hU : RelativeOpen F S U) (hsame : SetPred.Same U V) :
    RelativeOpen F S V := by
  cases hU with
  | intro W hW =>
      exact
        Exists.intro W
          (And.intro hW.left
            (fun x =>
              Iff.trans (Iff.symm (hsame x)) (hW.right x)))

/-- Extensionality of relative closedness, same shape as
`relativeOpen_congr`. -/
theorem relativeClosed_congr {S U V : alpha -> Prop}
    (hU : RelativeClosed F S U) (hsame : SetPred.Same U V) :
    RelativeClosed F S V := by
  cases hU with
  | intro W hW =>
      exact
        Exists.intro W
          (And.intro hW.left
            (fun x =>
              Iff.trans (Iff.symm (hsame x)) (hW.right x)))

theorem relativeOpen_trace {S V : alpha -> Prop}
    (hV : IsOpen F V) :
    RelativeOpen F S (Trace S V) :=
  Exists.intro V (And.intro hV (fun _ => Iff.rfl))

theorem openIn_trace {S V : alpha -> Prop}
    (hV : IsOpen F V) :
    OpenIn F S (Trace S V) :=
  relativeOpen_trace F hV

theorem relativeClosed_trace {S V : alpha -> Prop}
    (hV : IsClosed F V) :
    RelativeClosed F S (Trace S V) :=
  Exists.intro V (And.intro hV (fun _ => Iff.rfl))

theorem closedIn_trace {S V : alpha -> Prop}
    (hV : IsClosed F V) :
    ClosedIn F S (Trace S V) :=
  relativeClosed_trace F hV

theorem relativeOpen_empty (S : alpha -> Prop) :
    RelativeOpen F S (SetPred.Empty : alpha -> Prop) := by
  apply relativeOpen_congr F (relativeOpen_trace F (S := S) (open_empty F))
  intro x
  constructor
  · intro hx
    exact False.elim hx.right
  · intro hx
    exact False.elim hx

theorem relativeOpen_universal (S : alpha -> Prop) :
    RelativeOpen F S S := by
  apply relativeOpen_congr F
    (relativeOpen_trace F (S := S) (open_universal F))
  intro x
  constructor
  · intro hx
    exact hx.left
  · intro hx
    exact And.intro hx True.intro

theorem relativeClosed_empty (S : alpha -> Prop) :
    RelativeClosed F S (SetPred.Empty : alpha -> Prop) := by
  apply relativeClosed_congr F
    (relativeClosed_trace F (S := S) (closed_empty F))
  intro x
  constructor
  · intro hx
    exact False.elim hx.right
  · intro hx
    exact False.elim hx

theorem relativeClosed_universal (S : alpha -> Prop) :
    RelativeClosed F S S := by
  apply relativeClosed_congr F
    (relativeClosed_trace F (S := S) (closed_universal F))
  intro x
  constructor
  · intro hx
    exact hx.left
  · intro hx
    exact And.intro hx True.intro

theorem relativeOpen_union {S U V : alpha -> Prop}
    (hU : RelativeOpen F S U) (hV : RelativeOpen F S V) :
    RelativeOpen F S (SetPred.Union U V) := by
  cases hU with
  | intro A hA =>
      cases hV with
      | intro B hB =>
          refine Exists.intro (SetPred.Union A B) ?_
          refine And.intro (open_union F hA.left hB.left) ?_
          intro x
          constructor
          · intro hx
            cases hx with
            | inl hxU =>
                have h := (hA.right x).mp hxU
                exact And.intro h.left (Or.inl h.right)
            | inr hxV =>
                have h := (hB.right x).mp hxV
                exact And.intro h.left (Or.inr h.right)
          · intro hx
            cases hx.right with
            | inl hA' =>
                exact Or.inl ((hA.right x).mpr (And.intro hx.left hA'))
            | inr hB' =>
                exact Or.inr ((hB.right x).mpr (And.intro hx.left hB'))

theorem relativeOpen_inter {S U V : alpha -> Prop}
    (hU : RelativeOpen F S U) (hV : RelativeOpen F S V) :
    RelativeOpen F S (SetPred.Inter U V) := by
  cases hU with
  | intro A hA =>
      cases hV with
      | intro B hB =>
          refine Exists.intro (SetPred.Inter A B) ?_
          refine And.intro (open_inter F hA.left hB.left) ?_
          intro x
          constructor
          · intro hx
            have hAx := (hA.right x).mp hx.left
            have hBx := (hB.right x).mp hx.right
            exact And.intro hAx.left (And.intro hAx.right hBx.right)
          · intro hx
            exact And.intro
              ((hA.right x).mpr (And.intro hx.left hx.right.left))
              ((hB.right x).mpr (And.intro hx.left hx.right.right))

theorem relativeClosed_union {S U V : alpha -> Prop}
    (hU : RelativeClosed F S U) (hV : RelativeClosed F S V) :
    RelativeClosed F S (SetPred.Union U V) := by
  cases hU with
  | intro A hA =>
      cases hV with
      | intro B hB =>
          refine Exists.intro (SetPred.Union A B) ?_
          refine And.intro (closed_union F hA.left hB.left) ?_
          intro x
          constructor
          · intro hx
            cases hx with
            | inl hxU =>
                have h := (hA.right x).mp hxU
                exact And.intro h.left (Or.inl h.right)
            | inr hxV =>
                have h := (hB.right x).mp hxV
                exact And.intro h.left (Or.inr h.right)
          · intro hx
            cases hx.right with
            | inl hA' =>
                exact Or.inl ((hA.right x).mpr (And.intro hx.left hA'))
            | inr hB' =>
                exact Or.inr ((hB.right x).mpr (And.intro hx.left hB'))

theorem relativeClosed_inter {S U V : alpha -> Prop}
    (hU : RelativeClosed F S U) (hV : RelativeClosed F S V) :
    RelativeClosed F S (SetPred.Inter U V) := by
  cases hU with
  | intro A hA =>
      cases hV with
      | intro B hB =>
          refine Exists.intro (SetPred.Inter A B) ?_
          refine And.intro (closed_inter F hA.left hB.left) ?_
          intro x
          constructor
          · intro hx
            have hAx := (hA.right x).mp hx.left
            have hBx := (hB.right x).mp hx.right
            exact And.intro hAx.left (And.intro hAx.right hBx.right)
          · intro hx
            exact And.intro
              ((hA.right x).mpr (And.intro hx.left hx.right.left))
              ((hB.right x).mpr (And.intro hx.left hx.right.right))

/-- Relative De Morgan, the direction that is free: the complement of `U`
inside `S` is relatively open as soon as `U` is relatively closed,
witnessed by the ambient complement of `U`'s closed witness. No side
condition on `U` is needed. -/
theorem relativeOpen_diff_of_relativeClosed {S U : alpha -> Prop}
    (hU : RelativeClosed F S U) :
    RelativeOpen F S (SetPred.Diff S U) := by
  cases hU with
  | intro C hC =>
      refine Exists.intro (SetPred.Compl C) ?_
      refine And.intro hC.left ?_
      intro x
      constructor
      · intro hx
        exact And.intro hx.left
          (fun hCx => hx.right ((hC.right x).mpr (And.intro hx.left hCx)))
      · intro hx
        exact And.intro hx.left
          (fun hUx =>
            hx.right (((hC.right x).mp hUx).right))

/-- The converse direction, and it is not free: recovering `U` from its
relative complement requires `U` to be a subset of `S`, since the
complement only sees points of `S`. The closed witness is the complement of
the open one. -/
theorem relativeClosed_of_diff_relativeOpen {S U : alpha -> Prop}
    (hsub : SetPred.Subset U S)
    (hU : RelativeOpen F S (SetPred.Diff S U)) :
    RelativeClosed F S U := by
  cases hU with
  | intro V hV =>
      refine Exists.intro (SetPred.Compl V) ?_
      have hclosedComp : IsClosed F (SetPred.Compl V) := by
        apply open_congr F hV.left
        intro x
        constructor
        · intro hxV hxnotV
          exact hxnotV hxV
        · intro hxnotnotV
          classical
          by_cases hxV : V x
          · exact hxV
          · exact False.elim (hxnotnotV hxV)
      refine And.intro hclosedComp ?_
      intro x
      constructor
      · intro hxU
        exact And.intro (hsub x hxU)
          (fun hxV =>
            (((hV.right x).mpr (And.intro (hsub x hxU) hxV)).right) hxU)
      · intro hx
        classical
        by_cases hxU : U x
        · exact hxU
        · exact False.elim
            (hx.right (((hV.right x).mp (And.intro hx.left hxU)).right))

/-- A cover of `A` by relatively open sets lifts to a cover by ambient open
sets: choose each member's ambient witness `V i`, which agrees with `U i`
exactly on `S`. The lifted family still covers, because a point covered by
some `U i` is in particular a point of `S`. -/
theorem exists_ambient_open_cover_of_relative_cover {iota : Type u}
    {S A : alpha -> Prop} {U : iota -> alpha -> Prop}
    (hrel : forall i : iota, RelativeOpen F S (U i))
    (hcover : Covers U A) :
    Exists
      (fun V : iota -> alpha -> Prop =>
        And (forall i : iota, IsOpen F (V i))
          (And
            (forall i : iota,
              forall x : alpha, U i x <-> And (S x) (V i x))
            (Covers V A))) := by
  classical
  let V : iota -> alpha -> Prop :=
    fun i => Classical.choose (hrel i)
  have hV :
      forall i : iota,
        And (IsOpen F (V i))
          (forall x : alpha, U i x <-> And (S x) (V i x)) := by
    intro i
    exact Classical.choose_spec (hrel i)
  refine Exists.intro V ?_
  refine And.intro (fun i => (hV i).left) ?_
  refine And.intro (fun i x => (hV i).right x) ?_
  intro x hxA
  cases hcover x hxA with
  | intro i hi =>
      exact Exists.intro i (((hV i).right x).mp hi).right

theorem exists_relative_open_cover_of_ambient_cover {iota : Type u}
    {S A : alpha -> Prop} {V : iota -> alpha -> Prop}
    (hopen : forall i : iota, IsOpen F (V i))
    (hsub : SetPred.Subset A S)
    (hcover : Covers V A) :
    Exists
      (fun U : iota -> alpha -> Prop =>
        And (forall i : iota, RelativeOpen F S (U i))
          (And
            (forall i : iota,
              forall x : alpha, U i x <-> And (S x) (V i x))
            (Covers U A))) := by
  let U : iota -> alpha -> Prop :=
    fun i => Trace S (V i)
  refine Exists.intro U ?_
  refine And.intro (fun i => relativeOpen_trace F (S := S) (hopen i)) ?_
  refine And.intro (fun i x => Iff.rfl) ?_
  intro x hxA
  cases hcover x hxA with
  | intro i hix =>
      exact Exists.intro i (And.intro (hsub x hxA) hix)

end IsOrderedFieldBaseLike
end Tautology
