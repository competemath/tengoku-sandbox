import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Shared facts about nested chains

The small toolkit every route through the nested-interval node uses: that the
endpoints of a nested chain are ordered across stages, that a gap common to all
stages is bounded by every length, and that lengths tending to zero force such
a gap to vanish.

Nothing here is an edge; it is the vocabulary the edges share, which is why
several of them hold same-named forwarding lemmas pointing back at this file.

## Position and role

Support module for `RealSequence/Principles/`, at ordered-field level.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace NestedBasic

theorem limit_ge_of_eventually_ge {u : Nat -> alpha} {l c : alpha}
    (hu : F.SeqTendsto u l)
    (h : Eventually (fun n : Nat => F.le c (u n))) :
    F.le c l :=
  seqTendsto_le_of_eventually_le F
    (seqTendsto_const F c) hu h

theorem limit_le_of_eventually_le {u : Nat -> alpha} {l c : alpha}
    (hu : F.SeqTendsto u l)
    (h : Eventually (fun n : Nat => F.le (u n) c)) :
    F.le l c :=
  seqTendsto_le_of_eventually_le F
    hu (seqTendsto_const F c) h

/-- When the left endpoints of a nested family converge, their limit is a
common point of the whole family. This is how both producers of the node that
avoid the supremum get their point -- the one arriving from monotone
convergence, the one from the Cauchy criterion -- each feeding the two
monotonicities of the nesting in as eventual bounds on `l`. -/
theorem lower_limit_in_interval {a b : Nat -> alpha} {l : alpha}
    (hnest : F.NestedClosedIntervals a b)
    (ha : F.SeqTendsto a l)
    (n : Nat) :
    And (F.le (a n) l) (F.le l (b n)) := by
  refine And.intro ?_ ?_
  · apply limit_ge_of_eventually_ge F ha
    refine Exists.intro n ?_
    intro m hnm
    exact hnest.right.left n m hnm
  · apply limit_le_of_eventually_le F ha
    refine Exists.intro n ?_
    intro m hnm
    have ham_bm : F.le (a m) (b m) :=
      hnest.left m
    have hbm_bn : F.le (b m) (b n) :=
      hnest.right.right n m hnm
    exact F.le_trans ham_bm hbm_bn

/-- Unwraps one step of `IntervalLengthsToZero`: the tendsto statement is
phrased through `abs` of a subtraction of zero, and what every consumer
needs is the bare inequality on lengths, available because the nesting makes
them nonnegative. -/
theorem length_lt_of_close_to_zero {a b : Nat -> alpha} {eps : alpha}
    (hnest : F.NestedClosedIntervals a b)
    {n : Nat}
    (hclose :
      F.lt
        (abs F (F.sub (F.sub (b n) (a n)) F.zero))
        eps) :
    F.lt (F.sub (b n) (a n)) eps := by
  have hlen_nonneg : F.le F.zero (F.sub (b n) (a n)) :=
    sub_nonneg_of_le F (hnest.left n)
  rwa [sub_zero F (F.sub (b n) (a n)),
    abs_of_nonneg F hlen_nonneg] at hclose

/-- Two points of one interval of length below `eps` lie within `eps` of
each other. No triangle inequality is involved: each ordering of the pair is
bounded by `b - a` directly, and the sign of `x - y` decides which one to
take. -/
theorem interval_points_close {a b x y eps : alpha}
    (hx : And (F.le a x) (F.le x b))
    (hy : And (F.le a y) (F.le y b))
    (hlen : F.lt (F.sub b a) eps) :
    F.lt (abs F (F.sub x y)) eps := by
  have hxy_le : F.le (F.sub x y) (F.sub b a) :=
    sub_le_sub_of_le_of_le F hx.right hy.left
  have hyx_le : F.le (F.sub y x) (F.sub b a) :=
    sub_le_sub_of_le_of_le F hy.right hx.left
  by_cases h0 : F.le F.zero (F.sub x y)
  · rw [abs_of_nonneg F h0]
    exact lt_of_le_of_lt F hxy_le hlen
  · have hnonpos : F.le (F.sub x y) F.zero :=
      nonpos_of_not_nonneg F h0
    rw [abs_of_nonpos F hnonpos]
    rw [<- sub_rev_eq_neg_sub F x y]
    exact lt_of_le_of_lt F hyx_le hlen

theorem common_gap_le_length {a b : Nat -> alpha} {x y : alpha}
    (hx : forall n : Nat, And (F.le (a n) x) (F.le x (b n)))
    (hy : forall n : Nat, And (F.le (a n) y) (F.le y (b n)))
    (n : Nat) :
    F.le (F.sub x y) (F.sub (b n) (a n)) :=
  sub_le_sub_of_le_of_le F (hx n).right (hy n).left

/-- Half of uniqueness, the half that carries the argument: if the lengths
shrink to zero, a common point `x` cannot sit strictly above a common point
`y`. The gap `x - y` undercuts every interval length while those lengths
eventually fall below the gap itself, which is only consistent when `x ≤ y`. -/
theorem common_point_le {a b : Nat -> alpha} {x y : alpha}
    (hnest : F.NestedClosedIntervals a b)
    (hlen : F.IntervalLengthsToZero a b)
    (hx : forall n : Nat, And (F.le (a n) x) (F.le x (b n)))
    (hy : forall n : Nat, And (F.le (a n) y) (F.le y (b n))) :
    F.le x y := by
  by_cases hxy : F.le x y
  · exact hxy
  · have hyx_le : F.le y x := by
      cases F.le_total y x with
      | inl hyx => exact hyx
      | inr hxy' => exact False.elim (hxy hxy')
    have hyx_lt : F.lt y x :=
      lt_of_le_of_not_le F hyx_le hxy
    let eps := F.sub x y
    have heps : F.lt F.zero eps :=
      sub_pos_of_lt F hyx_lt
    cases hlen eps heps with
    | intro N hN =>
        have hlength_lt :
            F.lt (F.sub (b N) (a N)) eps :=
          length_lt_of_close_to_zero F hnest (hN N (Nat.le_refl N))
        have hgap_le :
            F.le eps (F.sub (b N) (a N)) := by
          change F.le (F.sub x y) (F.sub (b N) (a N))
          exact common_gap_le_length F hx hy N
        have hbad : F.lt eps eps :=
          lt_of_le_of_lt F hgap_le hlength_lt
        exact False.elim (lt_irrefl F eps hbad)

/-- Uniqueness proper, by antisymmetrizing `common_point_le`. Every entry
and edge that produces the node's uniqueness field closes with this lemma,
so the argument is written once at ordered-field level. -/
theorem common_points_equal {a b : Nat -> alpha} {x y : alpha}
    (hnest : F.NestedClosedIntervals a b)
    (hlen : F.IntervalLengthsToZero a b)
    (hx : forall n : Nat, And (F.le (a n) x) (F.le x (b n)))
    (hy : forall n : Nat, And (F.le (a n) y) (F.le y (b n))) :
    y = x := by
  have hxy : F.le x y :=
    common_point_le F hnest hlen hx hy
  have hyx : F.le y x :=
    common_point_le F hnest hlen hy hx
  exact F.le_antisymm hyx hxy

end NestedBasic

end IsOrderedFieldBaseLike
end Tautology
