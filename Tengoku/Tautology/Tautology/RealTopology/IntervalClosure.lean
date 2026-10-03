import Tengoku.Tautology.Tautology.RealTopology.Sequential
import Tengoku.Tautology.Tautology.RealTopology.Intervals

/-!
# What the operators do to an interval

Three exact computations: the interior of a closed interval is the
corresponding open interval, the closure of an open interval is the
corresponding closed interval, and the boundary of an open interval is its pair
of endpoints.

The hypotheses are not uniform, and that is not an oversight. The interior
computation needs nothing -- when the endpoints coincide both sides are empty.
The closure computation demands `left < right`, because a degenerate open
interval is empty and has empty closure while the closed interval is not.
Anyone tidying these statements into a common shape will write a false one.

The engine underneath is a trio of "every open neighbourhood must hit"
arguments: an open set containing a point also contains points to its left and
to its right, witnessed by midpoints, and at an endpoint the witness is the
midpoint against whichever far bound is tighter.

## Position and role

Implementation module, the last of the topology strand, built on
`Tautology.RealTopology.Sequential` and `Tautology.RealTopology.Intervals`.
Stated over an arbitrary ordered field; completeness plays no part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- An open set containing `x` also contains points strictly to the left of
`x`. Openness hands back an interval around `x`, and the midpoint between
that interval's left end and `x` serves as the witness. This
order-theoretic fact -- open sets have no isolated one-sided point -- is
what excludes endpoints from interiors below. -/
theorem open_neighborhood_hits_left_of_point
    {U : alpha -> Prop} {x : alpha}
    (hUopen : IsOpen F U) (hxU : U x) :
    Exists (fun y : alpha => And (F.lt y x) (U y)) := by
  cases hUopen x hxU with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          let y := midpoint F left x
          have hleft_y : F.lt left y :=
            left_lt_midpoint F hright.left
          have hy_x : F.lt y x :=
            midpoint_lt_right F hright.left
          have hy_right : F.lt y right :=
            lt_trans F hy_x hright.right.left
          exact Exists.intro y
            (And.intro hy_x
              (hright.right.right y (And.intro hleft_y hy_right)))

/-- The right-side companion of `open_neighborhood_hits_left_of_point`, the
witness now the midpoint between `x` and the interval's right end. -/
theorem open_neighborhood_hits_right_of_point
    {U : alpha -> Prop} {x : alpha}
    (hUopen : IsOpen F U) (hxU : U x) :
    Exists (fun y : alpha => And (F.lt x y) (U y)) := by
  cases hUopen x hxU with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          let y := midpoint F x right
          have hx_y : F.lt x y :=
            left_lt_midpoint F hright.right.left
          have hy_right : F.lt y right :=
            midpoint_lt_right F hright.right.left
          have hleft_y : F.lt left y :=
            lt_trans F hright.left hx_y
          exact Exists.intro y
            (And.intro hx_y
              (hright.right.right y (And.intro hleft_y hy_right)))

/-- Any open neighborhood of any point of a nondegenerate closed interval
meets the interval's interior. For an interior point this is immediate; at
the endpoints, which is the whole content of the lemma, the witness is the
midpoint between the endpoint and the tighter of the interval's and the
neighborhood's far bounds. -/
theorem open_neighborhood_hits_openInterval_of_closedInterval_mem
    {left right x : alpha} {U : alpha -> Prop}
    (hlr : F.lt left right)
    (hx : ClosedInterval F left right x)
    (hUopen : IsOpen F U) (hxU : U x) :
    Exists
      (fun y : alpha =>
        And (OpenInterval F left right y) (U y)) := by
  cases hUopen x hxU with
  | intro a ha =>
      cases ha with
      | intro b hb =>
          classical
          by_cases hleftx : F.lt left x
          · by_cases hxright : F.lt x right
            · exact Exists.intro x
                (And.intro (And.intro hleftx hxright) hxU)
            · have hrightx : F.le right x := le_of_not_lt F hxright
              have hx_eq_right : x = right :=
                F.le_antisymm hx.right hrightx
              let s := max2 F left a
              let y := midpoint F s right
              have ha_right : F.lt a right := by
                rw [<- hx_eq_right]
                exact hb.left
              have hs_right : F.lt s right :=
                max2_lt F hlr ha_right
              have hs_y : F.lt s y :=
                left_lt_midpoint F hs_right
              have hy_right : F.lt y right :=
                midpoint_lt_right F hs_right
              have hleft_y : F.lt left y :=
                lt_of_le_of_lt F (le_max2_left F left a) hs_y
              have ha_y : F.lt a y :=
                lt_of_le_of_lt F (le_max2_right F left a) hs_y
              have hy_b : F.lt y b := by
                have hy_x : F.lt y x := by
                  rw [hx_eq_right]
                  exact hy_right
                exact lt_trans F hy_x hb.right.left
              exact Exists.intro y
                (And.intro
                  (And.intro hleft_y hy_right)
                  (hb.right.right y (And.intro ha_y hy_b)))
          · have hxleft : F.le x left := le_of_not_lt F hleftx
            have hx_eq_left : x = left :=
              F.le_antisymm hxleft hx.left
            by_cases hxright : F.lt x right
            · let t := min2 F right b
              have hleft_b : F.lt left b := by
                rw [<- hx_eq_left]
                exact hb.right.left
              have hleft_t : F.lt left t :=
                lt_min2 F hlr hleft_b
              let y := midpoint F left t
              have hleft_y : F.lt left y :=
                left_lt_midpoint F hleft_t
              have hy_t : F.lt y t :=
                midpoint_lt_right F hleft_t
              have hy_right : F.lt y right :=
                lt_of_lt_of_le F hy_t (min2_le_left F right b)
              have hy_b : F.lt y b :=
                lt_of_lt_of_le F hy_t (min2_le_right F right b)
              have ha_y : F.lt a y := by
                have ha_left : F.lt a left := by
                  rw [<- hx_eq_left]
                  exact hb.left
                exact lt_trans F ha_left hleft_y
              exact Exists.intro y
                (And.intro
                  (And.intro hleft_y hy_right)
                  (hb.right.right y (And.intro ha_y hy_b)))
            · have hrightx : F.le right x := le_of_not_lt F hxright
              have hx_eq_right : x = right :=
                F.le_antisymm hx.right hrightx
              have hbad : left = right := by
                rw [<- hx_eq_left, <- hx_eq_right]
              exact False.elim (ne_of_lt F hlr hbad)

/-- The interior of a closed interval is the open interval with the same
endpoints, exactly. No strictness hypothesis is needed: for degenerate
intervals both sides are empty. Endpoint exclusion is precisely the two
one-sided neighborhood lemmas above. -/
theorem interior_closedInterval_same (left right : alpha) :
    SetPred.Same
      (Interior F (ClosedInterval F left right))
      (OpenInterval F left right) := by
  intro x
  constructor
  · intro hxInt
    have hxClosed :
        ClosedInterval F left right x :=
      interior_subset F (ClosedInterval F left right) x hxInt
    cases hxInt with
    | intro U hU =>
        have hleft : F.lt left x := by
          apply lt_of_le_of_not_le F hxClosed.left
          intro hxle
          have hx_eq_left : x = left :=
            F.le_antisymm hxle hxClosed.left
          cases open_neighborhood_hits_left_of_point F hU.left hU.right.left with
          | intro y hy =>
              have hyClosed : ClosedInterval F left right y :=
                hU.right.right y hy.right
              have hy_left : F.lt y left := by
                rw [<- hx_eq_left]
                exact hy.left
              exact (not_le_of_lt F hy_left) hyClosed.left
        have hright : F.lt x right := by
          apply lt_of_le_of_not_le F hxClosed.right
          intro hrightle
          have hx_eq_right : x = right :=
            F.le_antisymm hxClosed.right hrightle
          cases open_neighborhood_hits_right_of_point F hU.left hU.right.left with
          | intro y hy =>
              have hyClosed : ClosedInterval F left right y :=
                hU.right.right y hy.right
              have hright_y : F.lt right y := by
                rw [<- hx_eq_right]
                exact hy.left
              exact (not_le_of_lt F hright_y) hyClosed.right
        exact And.intro hleft hright
  · intro hx
    exact
      open_subset_interior F
        (open_interval F left right)
        (openInterval_subset_closedInterval F left right)
        x hx

/-- The closure of an open interval is the closed interval with the same
endpoints. Here the strictness hypothesis is essential, unlike in the
interior statement: at `left ≥ right` the open interval is empty and so is
its closure, while the closed interval need not be. -/
theorem closure_openInterval_same {left right : alpha}
    (hlr : F.lt left right) :
    SetPred.Same
      (Closure F (OpenInterval F left right))
      (ClosedInterval F left right) := by
  intro x
  constructor
  · intro hx
    exact closure_minimal_closed F
      (closed_interval F left right)
      (openInterval_subset_closedInterval F left right)
      x hx
  · intro hx U hUopen hxU
    exact open_neighborhood_hits_openInterval_of_closedInterval_mem
      F hlr hx hUopen hxU

/-- The boundary of a nondegenerate open interval is its two endpoints,
`SetPred.Pair`. An endpoint lies in the closure of the interval by
`closure_openInterval_same`, and in the closure of the complement because
every neighborhood of it reaches past the endpoint, into the rays outside. -/
theorem boundary_openInterval_same {left right : alpha}
    (hlr : F.lt left right) :
    SetPred.Same
      (Boundary F (OpenInterval F left right))
      (SetPred.Pair left right) := by
  intro x
  constructor
  · intro hx
    have hxClosed :
        ClosedInterval F left right x :=
      (closure_openInterval_same F hlr x).mp hx.left
    classical
    by_cases hleftx : F.lt left x
    · by_cases hxright : F.lt x right
      · have hhit :=
          hx.right
            (OpenInterval F left right)
            (open_interval F left right)
            (And.intro hleftx hxright)
        cases hhit with
        | intro y hy =>
            exact False.elim (hy.left hy.right)
      · have hrightx : F.le right x := le_of_not_lt F hxright
        have hx_eq_right : x = right :=
          F.le_antisymm hxClosed.right hrightx
        exact Or.inr hx_eq_right
    · have hxleft : F.le x left := le_of_not_lt F hleftx
      have hx_eq_left : x = left :=
        F.le_antisymm hxleft hxClosed.left
      exact Or.inl hx_eq_left
  · intro hxPair
    cases hxPair with
    | inl hxleft =>
        have hxClosed : ClosedInterval F left right x := by
          rw [hxleft]
          exact closedInterval_left_mem F (le_of_lt F hlr)
        refine And.intro ?_ ?_
        · exact (closure_openInterval_same F hlr x).mpr hxClosed
        · intro U hUopen hxU
          cases open_neighborhood_hits_left_of_point F hUopen hxU with
          | intro y hy =>
              refine Exists.intro y ?_
              refine And.intro ?_ hy.right
              intro hyOpen
              have hy_left : F.lt y left := by
                rw [<- hxleft]
                exact hy.left
              exact (not_le_of_lt F hy_left) (le_of_lt F hyOpen.left)
    | inr hxright =>
        have hxClosed : ClosedInterval F left right x := by
          rw [hxright]
          exact closedInterval_right_mem F (le_of_lt F hlr)
        refine And.intro ?_ ?_
        · exact (closure_openInterval_same F hlr x).mpr hxClosed
        · intro U hUopen hxU
          cases open_neighborhood_hits_right_of_point F hUopen hxU with
          | intro y hy =>
              refine Exists.intro y ?_
              refine And.intro ?_ hy.right
              intro hyOpen
              have hright_y : F.lt right y := by
                rw [<- hxright]
                exact hy.left
              exact (not_le_of_lt F hright_y) (le_of_lt F hyOpen.right)

end IsOrderedFieldBaseLike
end Tautology
