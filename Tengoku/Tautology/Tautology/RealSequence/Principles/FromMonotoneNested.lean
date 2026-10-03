import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic

/-!
# Edge: monotone convergence gives the nested-interval principle

Four declarations, no hypothesis -- the cheapest edge in the graph. The left
endpoints of a nested chain increase and are bounded above by any right
endpoint, so monotone convergence hands over their limit, which lies in every
stage; when the lengths tend to zero that point is also unique.

## Position and role

Edge module exporting `nestedIntervalPrinciple`. It is how both
`RealSequence.Principles.Routes.fromMonotone` and `...fromCauchy` reach the
nested node -- the latter because the direct edge from the Cauchy criterion,
`Tautology.RealSequence.Principles.FromCauchyNested`, only delivers half of it.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace FromMonotoneNested

/-- The left endpoints of a nested family are bounded above by `b 0`: each
`a n` lies below `b n`, and every `b n` lies below `b 0`. This is the
boundedness the monotone node needs, available before any convergence
exists. -/
theorem lower_endpoints_bounded_above {a b : Nat -> alpha}
    (hnest : F.NestedClosedIntervals a b) :
    F.SeqBoundedAbove a := by
  refine Exists.intro (b 0) ?_
  intro n
  have hb : F.le (b n) (b 0) :=
    hnest.right.right 0 n (Nat.zero_le n)
  exact F.le_trans (hnest.left n) hb

/-- The monotone node converges the left endpoints of the family, and their
limit is a common point; the two membership inequalities are read off by
`NestedBasic.lower_limit_in_interval`. No vanishing of lengths is needed
for this clause. -/
theorem exists_point
    (hmono : F.MonotoneConvergencePrinciple)
    {a b : Nat -> alpha}
    (hnest : F.NestedClosedIntervals a b) :
    Exists
      (fun x : alpha =>
        forall n : Nat,
          And (F.le (a n) x) (F.le x (b n))) := by
  have hinc : F.MonotoneIncreasing a :=
    hnest.right.left
  have hbdd : F.SeqBoundedAbove a :=
    lower_endpoints_bounded_above F hnest
  cases hmono.increasing a hinc hbdd with
  | intro l hl =>
      exact Exists.intro l (NestedBasic.lower_limit_in_interval F hnest hl)

/-- With lengths tending to zero the common point is unique: two common
points share every interval and so every width, which forces them equal,
by `NestedBasic.common_points_equal`. -/
theorem unique_point_of_lengths_zero
    (hmono : F.MonotoneConvergencePrinciple)
    {a b : Nat -> alpha}
    (hnest : F.NestedClosedIntervals a b)
    (hlen : F.IntervalLengthsToZero a b) :
    Exists
      (fun x : alpha =>
        And
          (forall n : Nat,
            And (F.le (a n) x) (F.le x (b n)))
          (forall y : alpha,
            (forall n : Nat,
              And (F.le (a n) y) (F.le y (b n))) ->
                y = x)) := by
  cases exists_point F hmono hnest with
  | intro x hx =>
      refine Exists.intro x ?_
      refine And.intro hx ?_
      intro y hy
      exact NestedBasic.common_points_equal F hnest hlen hx hy

/-- The edge from the monotone-convergence node to the nested-interval
node. It carries no extra hypothesis: the left endpoints of any nested
family are increasing and bounded above by `b 0`, so the monotone node
applies to them directly, and uniqueness asks nothing beyond the vanishing
lengths the clause already assumes. -/
theorem nestedIntervalPrinciple
    (hmono : F.MonotoneConvergencePrinciple) :
    F.NestedIntervalPrinciple where
  exists_point := by
    intro a b hnest
    exact exists_point F hmono hnest
  unique_point_of_lengths_zero := by
    intro a b hnest hlen
    exact unique_point_of_lengths_zero F hmono hnest hlen

end FromMonotoneNested
end IsOrderedFieldBaseLike
end Tautology
