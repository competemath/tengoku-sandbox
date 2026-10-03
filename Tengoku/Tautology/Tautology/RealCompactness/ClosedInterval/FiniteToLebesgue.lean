import Tengoku.Tautology.Tautology.RealBootstrap.Lattice
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Order

/-!
# Edge: finite subcovers give a Lebesgue number

Purely a bookkeeping edge -- no completeness, no Archimedean principle, only
ordered-field algebra. Its one hypothesis beyond compactness is a universe
bump: the refinement family is indexed by its own entries, so it has to be
lifted into the universe the compactness principle quantifies over.

The refinement is the standard one made explicit. Around each point, take an
outer interval already inside some member of the cover, and an inner interval
cut at the midpoints so that a margin remains on both sides; the local radius
is half the smaller margin. Compactness picks finitely many inner intervals,
and the Lebesgue number is the least of their radii: any point of the interval
sits in one of those inner intervals, and the ball of that radius around it
stays inside the corresponding outer interval, hence inside a member of the
original cover.

## Position and role

Edge module implementing `FiniteSubcoverToLebesgue`, exporting `target`. The
selected route travels it, taking the Lebesgue number from finite subcovers
rather than the reverse;
`Tautology.RealCompactness.ClosedInterval.LebesgueToFinite` is the edge in the
other direction.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace FiniteToLebesgue

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The edge proved by this file: the finite-subcover principle yields a
Lebesgue number for every open cover of a closed interval. No Archimedean
hypothesis enters -- the argument is covering bookkeeping around a finite
subcover of a shrunk refinement. The one extra constraint is universes,
not mathematics: the hypothesis is the compactness principle at the
lifted universe `max u 1`, applied through `ULift` because the refinement
family is indexed by the type of refinement entries, which lives at
`Type u` while the hypothesis speaks at `Type (max u 1)`. -/
def Target : Prop :=
  IsOrderedFieldBaseLike.FiniteSubcoverToLebesgue.{u} F

/-- The pointwise minimum of two field elements, a local renaming of `min2`
from `Tautology.RealBootstrap.Lattice`; the three facts below forward to their
`min2` counterparts unchanged. -/
noncomputable def min (x y : alpha) : alpha :=
  min2 F x y

theorem min_le_left (x y : alpha) :
    F.le (min F x y) x :=
  min2_le_left F x y

theorem min_le_right (x y : alpha) :
    F.le (min F x y) y :=
  min2_le_right F x y

theorem min_pos {x y : alpha}
    (hx : F.lt F.zero x) (hy : F.lt F.zero y) :
    F.lt F.zero (min F x y) :=
  min2_pos F hx hy

theorem sub_lt_sub_right_of_lt {x y z : alpha}
    (hxy : F.lt x y) :
    F.lt (F.sub x z) (F.sub y z) := by
  have h := add_lt_add_right F hxy (F.neg z)
  rwa [<- F.sub_eq_add_neg x z, <- F.sub_eq_add_neg y z] at h

theorem sub_lt_sub_left_of_lt {x y z : alpha}
    (hxy : F.lt x y) :
    F.lt (F.sub z y) (F.sub z x) := by
  have hneg : F.lt (F.neg y) (F.neg x) := by
    have h := add_lt_add_right F hxy (F.neg y)
    have hleft : F.add x (F.neg y) = F.sub x y := by
      rw [F.sub_eq_add_neg]
    have hright : F.add y (F.neg y) = F.zero := F.add_neg y
    have hsub_neg : F.lt (F.sub x y) F.zero := by
      rwa [hleft, hright] at h
    have h' := add_lt_add_right F hsub_neg (F.neg x)
    have hL :
        F.add (F.sub x y) (F.neg x) = F.neg y := by
      rw [F.sub_eq_add_neg]
      calc
        F.add (F.add x (F.neg y)) (F.neg x) =
            F.add (F.add (F.neg y) x) (F.neg x) := by
              rw [F.add_comm x (F.neg y)]
        _ = F.neg y := add_neg_cancel_right F (F.neg y) x
    have hR : F.add F.zero (F.neg x) = F.neg x := F.zero_add (F.neg x)
    rwa [hL, hR] at h'
  have h := add_lt_add_left F hneg z
  rwa [<- F.sub_eq_add_neg z y, <- F.sub_eq_add_neg z x] at h

theorem lt_sub_of_add_lt_right {a eps x : alpha}
    (h : F.lt (F.add a eps) x) :
    F.lt a (F.sub x eps) := by
  have h' := add_lt_add_right F h (F.neg eps)
  have hleft : F.add (F.add a eps) (F.neg eps) = a :=
    add_neg_cancel_right F a eps
  have hright : F.add x (F.neg eps) = F.sub x eps := by
    rw [F.sub_eq_add_neg]
  rwa [hleft, hright] at h'

theorem add_lt_of_lt_sub_right {x eps b : alpha}
    (h : F.lt x (F.sub b eps)) :
    F.lt (F.add x eps) b := by
  have h' := add_lt_add_right F h eps
  have hleft : F.add x eps = F.add x eps := rfl
  have hright : F.add (F.sub b eps) eps = b :=
    sub_add_cancel F b eps
  rwa [hleft, hright] at h'

/-- One member of the shrunk refinement of the cover: an original index
`i`, the outer open interval lying inside `U i`, and an inner interval
strictly inside it. The gap between inner and outer is where the Lebesgue
radius lives. -/
structure LocalIndex {iota : Type u}
    (U : iota -> alpha -> Prop) where
  i : iota
  outerLeft : alpha
  outerRight : alpha
  innerLeft : alpha
  innerRight : alpha
  outerLeft_lt_innerLeft : F.lt outerLeft innerLeft
  innerRight_lt_outerRight : F.lt innerRight outerRight
  contained :
    forall y : alpha,
      F.OpenInterval outerLeft outerRight y -> U i y

/-- The inner interval of a refinement entry; the refinement cover is built
from exactly these. -/
def LocalSet {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) : alpha -> Prop :=
  F.OpenInterval p.innerLeft p.innerRight

theorem localSet_open {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) :
    F.IsOpen (LocalSet F p) := by
  intro x hx
  refine Exists.intro p.innerLeft ?_
  refine Exists.intro p.innerRight ?_
  constructor
  · exact hx.left
  · constructor
    · exact hx.right
    · intro y hy
      exact hy

/-- The refinement step: every point of the closed interval lies inside the
inner interval of some refinement entry. Around the point, take a covering
member and an open interval inside it straddling the point, then cut the
inner interval at the two midpoints so that it stays clear of both outer
endpoints. -/
theorem localCover {iota : Type u}
    {left right : alpha} {U : iota -> alpha -> Prop}
    (hopen : forall i : iota, F.IsOpen (U i))
    (hcover : Covers U (F.ClosedInterval left right)) :
    Covers (fun p : LocalIndex F U => LocalSet F p)
      (F.ClosedInterval left right) := by
  intro x hx
  cases hcover x hx with
  | intro i hi =>
      cases hopen i x hi with
      | intro a ha =>
          cases ha with
          | intro b hb =>
              let il := midpoint F a x
              let ir := midpoint F x b
              have hail : F.lt a il :=
                left_lt_midpoint F hb.left
              have hilx : F.lt il x :=
                midpoint_lt_right F hb.left
              have hxir : F.lt x ir :=
                left_lt_midpoint F hb.right.left
              have hirb : F.lt ir b :=
                midpoint_lt_right F hb.right.left
              let p : LocalIndex F U := {
                i := i
                outerLeft := a
                outerRight := b
                innerLeft := il
                innerRight := ir
                outerLeft_lt_innerLeft := hail
                innerRight_lt_outerRight := hirb
                contained := hb.right.right
              }
              refine Exists.intro p ?_
              exact And.intro hilx hxir

/-- The gap from the inner interval's left endpoint out to the outer one. -/
def leftMargin {iota : Type u} {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) : alpha :=
  F.sub p.innerLeft p.outerLeft

/-- The gap from the inner interval's right endpoint out to the outer one,
the companion of `leftMargin`. -/
def rightMargin {iota : Type u} {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) : alpha :=
  F.sub p.outerRight p.innerRight

/-- The working radius of an entry: half the smaller of its two margins,
hence strictly inside both. Balls of this radius around points of the
inner interval cannot reach past the outer interval. -/
noncomputable def localRadius {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) : alpha :=
  half F (min F (leftMargin F p) (rightMargin F p))

theorem leftMargin_pos {iota : Type u} {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) :
    F.lt F.zero (leftMargin F p) :=
  sub_pos_of_lt F p.outerLeft_lt_innerLeft

theorem rightMargin_pos {iota : Type u} {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) :
    F.lt F.zero (rightMargin F p) :=
  sub_pos_of_lt F p.innerRight_lt_outerRight

theorem localRadius_pos {iota : Type u} {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) :
    F.lt F.zero (localRadius F p) :=
  half_pos F
    (min_pos F (leftMargin_pos F p) (rightMargin_pos F p))

theorem localRadius_lt_leftMargin {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) :
    F.lt (localRadius F p) (leftMargin F p) := by
  have hmin_pos :
      F.lt F.zero (min F (leftMargin F p) (rightMargin F p)) :=
    min_pos F (leftMargin_pos F p) (rightMargin_pos F p)
  exact lt_of_lt_of_le F
    (half_lt_self F hmin_pos)
    (min_le_left F (leftMargin F p) (rightMargin F p))

theorem localRadius_lt_rightMargin {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) :
    F.lt (localRadius F p) (rightMargin F p) := by
  have hmin_pos :
      F.lt F.zero (min F (leftMargin F p) (rightMargin F p)) :=
    min_pos F (leftMargin_pos F p) (rightMargin_pos F p)
  exact lt_of_lt_of_le F
    (half_lt_self F hmin_pos)
    (min_le_right F (leftMargin F p) (rightMargin F p))

/-- The minimum of the radii of a list of entries, with `1` for the empty
list so that it stays positive. A finite minimum of positive quantities is
positive, which is all the positivity this edge needs. -/
noncomputable def listRadius {iota : Type u}
    {U : iota -> alpha -> Prop} :
    List (LocalIndex F U) -> alpha
  | [] => F.one
  | p :: ps => min F (localRadius F p) (listRadius ps)

theorem listRadius_pos {iota : Type u}
    {U : iota -> alpha -> Prop} :
    forall ps : List (LocalIndex F U),
      F.lt F.zero (listRadius F ps)
  | [] => zero_lt_one F
  | p :: ps =>
      min_pos F (localRadius_pos F p) (listRadius_pos ps)

theorem listRadius_le_of_mem {iota : Type u}
    {U : iota -> alpha -> Prop} :
    forall {ps : List (LocalIndex F U)} {p : LocalIndex F U},
      List.Mem p ps -> F.le (listRadius F ps) (localRadius F p)
  | [], p, h => by cases h
  | q :: ps, p, h => by
      cases h with
      | head =>
          exact min_le_left F (localRadius F q) (listRadius F ps)
      | tail _ htail =>
          exact F.le_trans
            (min_le_right F (localRadius F q) (listRadius F ps))
            (listRadius_le_of_mem htail)

/-- The same minimum after the universe lift; the subcover that the lifted
hypothesis returns is a list of lifted entries, and this is its radius. -/
noncomputable def liftedListRadius {iota : Type u}
    {U : iota -> alpha -> Prop} :
    List (ULift (LocalIndex F U)) -> alpha
  | [] => F.one
  | p :: ps => min F (localRadius F p.down) (liftedListRadius ps)

theorem liftedListRadius_pos {iota : Type u}
    {U : iota -> alpha -> Prop} :
    forall ps : List (ULift (LocalIndex F U)),
      F.lt F.zero (liftedListRadius F ps)
  | [] => zero_lt_one F
  | p :: ps =>
      min_pos F (localRadius_pos F p.down) (liftedListRadius_pos ps)

theorem liftedListRadius_le_of_mem {iota : Type u}
    {U : iota -> alpha -> Prop} :
    forall {ps : List (ULift (LocalIndex F U))}
      {p : ULift (LocalIndex F U)},
      List.Mem p ps -> F.le (liftedListRadius F ps) (localRadius F p.down)
  | [], p, h => by cases h
  | q :: ps, p, h => by
      cases h with
      | head =>
          exact min_le_left F (localRadius F q.down) (liftedListRadius F ps)
      | tail _ htail =>
          exact F.le_trans
            (min_le_right F (localRadius F q.down) (liftedListRadius F ps))
            (liftedListRadius_le_of_mem htail)

theorem liftedLocalCover {iota : Type u}
    {left right : alpha} {U : iota -> alpha -> Prop}
    (hopen : forall i : iota, F.IsOpen (U i))
    (hcover : Covers U (F.ClosedInterval left right)) :
    Covers.{max u 1}
      (fun p : ULift (LocalIndex F U) => LocalSet F p.down)
      (F.ClosedInterval left right) := by
  intro x hx
  cases localCover F hopen hcover x hx with
  | intro p hp =>
      exact Exists.intro (ULift.up p) hp

theorem liftedLocalSet_open {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : ULift (LocalIndex F U)) :
    F.IsOpen (LocalSet F p.down) :=
  localSet_open F p.down

/-- A point of an entry's inner interval draws its whole ball into `U i`, as
long as the radius is at most the entry's own: that radius clears both
margins, so the ball stays inside the outer interval, which `U i`
contains. The Lebesgue property checked on a single entry. -/
theorem local_ball_subset {iota : Type u}
    {U : iota -> alpha -> Prop}
    (p : LocalIndex F U) {x y : alpha}
    (hx : LocalSet F p x)
    (hclose : F.lt (dist F y x) (localRadius F p)) :
    U p.i y := by
  have hleft_margin :
      F.lt (localRadius F p) (F.sub x p.outerLeft) := by
    exact lt_trans F (localRadius_lt_leftMargin F p)
      (sub_lt_sub_right_of_lt F hx.left)
  have hright_margin :
      F.lt (localRadius F p) (F.sub p.outerRight x) := by
    exact lt_trans F (localRadius_lt_rightMargin F p)
      (sub_lt_sub_left_of_lt F hx.right)
  have hclose_left :
      F.lt (dist F y x) (F.sub x p.outerLeft) :=
    lt_trans F hclose hleft_margin
  have hclose_right :
      F.lt (dist F y x) (F.sub p.outerRight x) :=
    lt_trans F hclose hright_margin
  have hy_left0 :
      F.lt (F.sub x (F.sub x p.outerLeft)) y := by
    exact abs_sub_lt_left F hclose_left
  have hy_left : F.lt p.outerLeft y := by
    rwa [sub_self_sub F x p.outerLeft] at hy_left0
  have hy_right0 :
      F.lt y (F.add x (F.sub p.outerRight x)) := by
    exact abs_sub_lt_right F hclose_right
  have hy_right : F.lt y p.outerRight := by
    have hsum :
        F.add x (F.sub p.outerRight x) = p.outerRight := by
      rw [F.add_comm x (F.sub p.outerRight x)]
      exact sub_add_cancel F p.outerRight x
    rwa [hsum] at hy_right0
  exact p.contained y (And.intro hy_left hy_right)

/-- The edge as a principle: refine the cover, extract a finite subcover of
the refinement at the lifted universe, and take the minimum radius of the
selected entries. Every point of the interval lies in some selected inner
interval, and the minimum radius is small enough for that entry, so the
ball it commands lands inside a single member of the original cover. -/
theorem lebesguePrinciple
    (hcompact :
      ClosedIntervalCompactnessPrinciple.{max u 1} F) :
    ClosedIntervalLebesguePrinciple.{u} F where
  lebesgue_number := by
    intro iota left right U hle hopen hcover
    have hlocalCover :
        Covers.{max u 1}
          (fun p : ULift (LocalIndex F U) => LocalSet F p.down)
          (F.ClosedInterval left right) :=
      liftedLocalCover F hopen hcover
    have hlocalOpen :
        forall p : ULift (LocalIndex F U),
          F.IsOpen (LocalSet F p.down) :=
      liftedLocalSet_open F
    cases hcompact.finite_subcover left right
        (fun p : ULift (LocalIndex F U) => LocalSet F p.down)
        hle hlocalOpen hlocalCover with
    | intro ps hps =>
        refine Exists.intro (liftedListRadius F ps) ?_
        constructor
        · exact liftedListRadius_pos F ps
        · intro x hx
          cases hps x hx with
          | intro p hp =>
              refine Exists.intro p.down.i ?_
              intro y hy hdist
              have hdelta_le :
                  F.le (liftedListRadius F ps) (localRadius F p.down) :=
                liftedListRadius_le_of_mem F hp.left
              have hdist_local :
                  F.lt (dist F y x) (localRadius F p.down) :=
                lt_of_lt_of_le F hdist hdelta_le
              exact local_ball_subset F p.down hp.right hdist_local

/-- The exported edge `FiniteSubcoverToLebesgue`, hypothesis at the lifted
universe `max u 1` included; `Routes` applies it directly to the
compactness the sequential route produces. -/
theorem target : Target.{u} F := by
  intro hcompact
  exact lebesguePrinciple F hcompact

end FiniteToLebesgue
end Compactness
end IsOrderedFieldBaseLike
end Tautology
