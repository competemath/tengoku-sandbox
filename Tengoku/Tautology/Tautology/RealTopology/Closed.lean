import Tengoku.Tautology.Tautology.RealTopology.Basic
import Tengoku.Tautology.Tautology.RealTopology.SetOps

/-!
# Closed sets and the interior, closure and boundary operators

Closedness is defined as openness of the complement, and from that single
choice everything in the file follows by moving the work to the complement:
finite unions and intersections, the two extremes, and the fact that a closed
interval is closed. The file also introduces the pointwise operators --
interior, closure, boundary -- and the neighbourhood and density vocabulary,
leaving their algebra to `Tautology.RealTopology.ClosureAlgebra`.

Two things are easy to misread. First, the extensional congruence lemmas
(`open_congr`, `closed_congr`) are not bookkeeping noise: sets here are
predicates, so De Morgan and double complement return sets that are only
extensionally equal to the originals, and these lemmas are what absorbs that
mismatch. Second, `closed_interval` needs no completeness -- a point outside
`[a, b]` is separated by a ray of unit span, which any ordered field supplies.

## Position and role

Implementation module. It builds on `Tautology.RealTopology.Basic` and the set
vocabulary of `Tautology.RealTopology.SetOps`, and is the base for
`Tautology.RealTopology.Subspace` and `Tautology.RealTopology.Intervals`.
Stated over an arbitrary ordered field; completeness plays no part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- A set is closed when its complement is open. This is the only notion of
closedness in the region: every closed-set statement is proved as an
openness statement about the complement. -/
def IsClosed (S : alpha -> Prop) : Prop :=
  IsOpen F (SetPred.Compl S)

/-- An open neighbourhood of `x`: an open set that actually contains `x`.
The containment is part of the predicate, so a neighbourhood can be handed
around as one object. -/
def IsNeighborhood (U : alpha -> Prop) (x : alpha) : Prop :=
  And (IsOpen F U) (U x)

/-- The closed interval `[left, right]` as a pointwise predicate,
`left ≤ x ≤ right`. Unlike its open companion it keeps the degenerate case:
with `left = right` it is a singleton, not empty. -/
def ClosedInterval (left right : alpha) : alpha -> Prop :=
  fun x => And (F.le left x) (F.le x right)

/-- `x` is an interior point of `S` when some open set containing `x` is
entirely contained in `S`. Kept as a predicate on the point so that
`Interior` can aggregate it pointwise. -/
def InteriorPoint (S : alpha -> Prop) (x : alpha) : Prop :=
  Exists
    (fun U : alpha -> Prop =>
      And (IsOpen F U)
        (And (U x) (SetPred.Subset U S)))

/-- The interior of `S`, pointwise: `x` belongs when some open
neighbourhood of `x` lies inside `S`. -/
def Interior (S : alpha -> Prop) : alpha -> Prop :=
  fun x => InteriorPoint F S x

/-- `x` is a closure point of `S` when every open set containing `x` also
contains a point of `S`. The encounter is required to happen inside the
given open set, which makes this the dual of `InteriorPoint`: an existential
inside against a universal outside. -/
def ClosurePoint (S : alpha -> Prop) (x : alpha) : Prop :=
  forall U : alpha -> Prop,
    IsOpen F U -> U x -> Exists (fun y : alpha => And (S y) (U y))

/-- The closure of `S`: the points every open neighbourhood of which meets
`S`, aggregated pointwise from `ClosurePoint`. -/
def Closure (S : alpha -> Prop) : alpha -> Prop :=
  fun x => ClosurePoint F S x

/-- `x` is a boundary point of `S` when open sets containing `x` meet both
sides: it is a closure point of `S` and of the complement of `S` alike. -/
def BoundaryPoint (S : alpha -> Prop) (x : alpha) : Prop :=
  And (ClosurePoint F S x) (ClosurePoint F (SetPred.Compl S) x)

/-- The boundary of `S`, the pointwise aggregation of `BoundaryPoint`. -/
def Boundary (S : alpha -> Prop) : alpha -> Prop :=
  fun x => BoundaryPoint F S x

/-- `S` is dense in `T` when every point of `T` is a closure point of `S`.
Unpacked: every open set that contains a point of `T` also meets `S`. -/
def DenseIn (S T : alpha -> Prop) : Prop :=
  forall x : alpha, T x -> ClosurePoint F S x

theorem lt_add_one (x : alpha) :
    F.lt x (F.add x F.one) := by
  have h := add_lt_add_left F (zero_lt_one F) x
  rwa [F.add_zero] at h

theorem sub_one_lt (x : alpha) :
    F.lt (F.sub x F.one) x :=
  sub_lt_self_of_pos F (zero_lt_one F)

/-- Openness is extensional: it transfers along `Same`, pointwise
if-and-only-if equality of sets. This is the tool that absorbs the
complement-arithmetic mismatches in the closed-set proofs below. -/
theorem open_congr {U V : alpha -> Prop}
    (hU : IsOpen F U) (hsame : SetPred.Same U V) :
    IsOpen F V := by
  intro x hx
  cases hU x ((hsame x).mpr hx) with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          exact
            Exists.intro left
              (Exists.intro right
                (And.intro hright.left
                  (And.intro hright.right.left
                    (fun y hy =>
                      (hsame y).mp (hright.right.right y hy)))))

theorem open_compl_of_closed {S : alpha -> Prop}
    (hS : IsClosed F S) :
    IsOpen F (SetPred.Compl S) :=
  hS

/-- The complement of an open set is closed. The companion direction is a
definitional unfold, this one is not: the complement of the complement
agrees with the original set only extensionally, and `open_congr` is what
absorbs that step. -/
theorem closed_compl_of_open {U : alpha -> Prop}
    (hU : IsOpen F U) :
    IsClosed F (SetPred.Compl U) := by
  apply open_congr F hU
  intro x
  constructor
  · intro hx hxnot
    exact hxnot hx
  · intro hxnotnot
    classical
    by_cases hx : U x
    · exact hx
    · exact False.elim (hxnotnot hx)

theorem open_empty : IsOpen F (SetPred.Empty : alpha -> Prop) := by
  intro x hx
  exact False.elim hx

theorem open_universal :
    IsOpen F (SetPred.Universal : alpha -> Prop) := by
  intro x hx
  exact
    Exists.intro (F.sub x F.one)
      (Exists.intro (F.add x F.one)
        (And.intro (sub_one_lt F x)
          (And.intro (lt_add_one F x)
            (fun y hy => True.intro))))

theorem open_interval (left right : alpha) :
    IsOpen F (OpenInterval F left right) := by
  intro x hx
  exact
    Exists.intro left
      (Exists.intro right
        (And.intro hx.left (And.intro hx.right (fun y hy => hy))))

theorem open_union {U V : alpha -> Prop}
    (hU : IsOpen F U) (hV : IsOpen F V) :
    IsOpen F (SetPred.Union U V) := by
  intro x hx
  cases hx with
  | inl hxU =>
      cases hU x hxU with
      | intro left hleft =>
          cases hleft with
          | intro right hright =>
              exact
                Exists.intro left
                  (Exists.intro right
                    (And.intro hright.left
                      (And.intro hright.right.left
                        (fun y hy => Or.inl (hright.right.right y hy)))))
  | inr hxV =>
      cases hV x hxV with
      | intro left hleft =>
          cases hleft with
          | intro right hright =>
              exact
                Exists.intro left
                  (Exists.intro right
                    (And.intro hright.left
                      (And.intro hright.right.left
                        (fun y hy => Or.inr (hright.right.right y hy)))))

theorem open_indexedUnion {iota : Type u}
    {U : iota -> alpha -> Prop}
    (hU : forall i : iota, IsOpen F (U i)) :
    IsOpen F (SetPred.IndexedUnion U) := by
  intro x hx
  cases hx with
  | intro i hxi =>
      cases hU i x hxi with
      | intro left hleft =>
          cases hleft with
          | intro right hright =>
              exact
                Exists.intro left
                  (Exists.intro right
                    (And.intro hright.left
                      (And.intro hright.right.left
                        (fun y hy =>
                          Exists.intro i (hright.right.right y hy)))))

/-- The intersection of two open sets is open. The witness interval at a
point common to both is assembled endpointwise from the two given
witnesses, larger left endpoint and smaller right endpoint, which is why
the proof is a four-way split on `F.le_total`. -/
theorem open_inter {U V : alpha -> Prop}
    (hU : IsOpen F U) (hV : IsOpen F V) :
    IsOpen F (SetPred.Inter U V) := by
  intro x hx
  cases hx with
  | intro hxU hxV =>
      cases hU x hxU with
      | intro a ha =>
          cases ha with
          | intro b hb =>
              cases hV x hxV with
              | intro c hc =>
                  cases hc with
                  | intro d hd =>
                      classical
                      by_cases hac : F.le a c
                      · by_cases hbd : F.le b d
                        · refine Exists.intro c ?_
                          refine Exists.intro b ?_
                          refine And.intro hd.left ?_
                          refine And.intro hb.right.left ?_
                          intro y hy
                          exact And.intro
                            (hb.right.right y
                              (And.intro
                                (lt_of_le_of_lt F hac hy.left)
                                hy.right))
                            (hd.right.right y
                              (And.intro hy.left
                                (lt_of_lt_of_le F hy.right hbd)))
                        · have hdb : F.le d b := by
                            cases F.le_total d b with
                            | inl h => exact h
                            | inr h => exact False.elim (hbd h)
                          refine Exists.intro c ?_
                          refine Exists.intro d ?_
                          refine And.intro hd.left ?_
                          refine And.intro hd.right.left ?_
                          intro y hy
                          exact And.intro
                            (hb.right.right y
                              (And.intro
                                (lt_of_le_of_lt F hac hy.left)
                                (lt_of_lt_of_le F hy.right hdb)))
                            (hd.right.right y hy)
                      · have hca : F.le c a := by
                          cases F.le_total c a with
                          | inl h => exact h
                          | inr h => exact False.elim (hac h)
                        by_cases hbd : F.le b d
                        · refine Exists.intro a ?_
                          refine Exists.intro b ?_
                          refine And.intro hb.left ?_
                          refine And.intro hb.right.left ?_
                          intro y hy
                          exact And.intro
                            (hb.right.right y hy)
                            (hd.right.right y
                              (And.intro
                                (lt_of_le_of_lt F hca hy.left)
                                (lt_of_lt_of_le F hy.right hbd)))
                        · have hdb : F.le d b := by
                            cases F.le_total d b with
                            | inl h => exact h
                            | inr h => exact False.elim (hbd h)
                          refine Exists.intro a ?_
                          refine Exists.intro d ?_
                          refine And.intro hb.left ?_
                          refine And.intro hd.right.left ?_
                          intro y hy
                          exact And.intro
                            (hb.right.right y
                              (And.intro hy.left
                                (lt_of_lt_of_le F hy.right hdb)))
                            (hd.right.right y
                              (And.intro
                                (lt_of_le_of_lt F hca hy.left)
                                hy.right))

/-- Closedness is extensional too, transferring along `Same`; proved as
`open_congr` on complements. -/
theorem closed_congr {A B : alpha -> Prop}
    (hA : IsClosed F A) (hsame : SetPred.Same A B) :
    IsClosed F B := by
  apply open_congr F hA
  intro x
  constructor
  · intro hx hB
    exact hx ((hsame x).mpr hB)
  · intro hx hA'
    exact hx ((hsame x).mp hA')

theorem closed_empty : IsClosed F (SetPred.Empty : alpha -> Prop) := by
  apply open_congr F (open_universal F)
  intro x
  constructor
  · intro hx hfalse
    exact hfalse
  · intro hx
    exact True.intro

theorem closed_universal :
    IsClosed F (SetPred.Universal : alpha -> Prop) := by
  apply open_congr F (open_empty F)
  intro x
  constructor
  · intro hx
    exact False.elim hx
  · intro hx
    exact hx True.intro

/-- The union of two closed sets is closed, by De Morgan from `open_inter`,
with `open_congr` absorbing the complement arithmetic. -/
theorem closed_union {A B : alpha -> Prop}
    (hA : IsClosed F A) (hB : IsClosed F B) :
    IsClosed F (SetPred.Union A B) := by
  apply open_congr F (open_inter F hA hB)
  intro x
  constructor
  · intro hx
    intro hAB
    cases hAB with
    | inl hA' => exact hx.left hA'
    | inr hB' => exact hx.right hB'
  · intro hx
    constructor
    · intro hA'
      exact hx (Or.inl hA')
    · intro hB'
      exact hx (Or.inr hB')

/-- The intersection of two closed sets is closed, dually from `open_union`. -/
theorem closed_inter {A B : alpha -> Prop}
    (hA : IsClosed F A) (hB : IsClosed F B) :
    IsClosed F (SetPred.Inter A B) := by
  apply open_congr F (open_union F hA hB)
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hnotA =>
        intro hAB
        exact hnotA hAB.left
    | inr hnotB =>
        intro hAB
        exact hnotB hAB.right
  · intro hx
    classical
    by_cases hA' : A x
    · exact Or.inr (fun hB' => hx (And.intro hA' hB'))
    · exact Or.inl hA'

/-- A closed interval is a closed set, over any ordered field; completeness
plays no part. A point outside is separated by a unit ray: lying to the
right of `right`, the witness is `(right, x + 1)`, every point of which is
also right of `right`; lying to the left of `left`, the mirror image
`(x - 1, left)`. -/
theorem closed_interval (left right : alpha) :
    IsClosed F (ClosedInterval F left right) := by
  intro x hx
  classical
  by_cases hleftx : F.le left x
  · have hxright_not : Not (F.le x right) := by
      intro hxright
      exact hx (And.intro hleftx hxright)
    have hrightx : F.le right x := by
      cases F.le_total right x with
      | inl h => exact h
      | inr hxright => exact False.elim (hxright_not hxright)
    have hright_lt_x : F.lt right x :=
      lt_of_le_of_not_le F hrightx hxright_not
    exact
      Exists.intro right
        (Exists.intro (F.add x F.one)
          (And.intro hright_lt_x
            (And.intro (lt_add_one F x)
              (fun y hy hclosed =>
                (not_le_of_lt F hy.left) hclosed.right))))
  · have hxleft : F.le x left := by
      cases F.le_total x left with
      | inl h => exact h
      | inr h => exact False.elim (hleftx h)
    have hx_lt_left : F.lt x left :=
      lt_of_le_of_not_le F hxleft hleftx
    exact
      Exists.intro (F.sub x F.one)
        (Exists.intro left
          (And.intro (sub_one_lt F x)
            (And.intro hx_lt_left
              (fun y hy hclosed =>
                (not_le_of_lt F hy.right) hclosed.left))))

end IsOrderedFieldBaseLike
end Tautology
