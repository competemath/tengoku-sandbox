import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic

/-!
# Edge: the Cauchy criterion gives only half the nested-interval principle

Two declarations, and the important thing about this module is what it does
*not* contain. It proves that the left endpoints of a nested chain whose
lengths tend to zero form a Cauchy sequence, and hence that such a chain has a
unique common point. It does not prove the other field of
`NestedIntervalPrinciple` -- that *any* nested chain, with no condition on its
lengths, has a common point at all.

So this edge cannot deliver the node, and no assembly pretends otherwise:
`RealSequence.Principles.Routes.fromCauchy` reaches the nested principle by
going through monotone convergence instead. A graph drawn only from file names
would show an edge here; reading what the file actually exports shows a half
edge. That is the kind of thing laying the graph out explicitly is meant to
make visible.

## Position and role

Partial edge module, at ordered-field level, taking the Cauchy criterion as an
explicit hypothesis.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace FromCauchyNested

/-- When the lengths tend to zero, the left endpoints of a nested family
form a Cauchy sequence: past stage `N` both endpoints under comparison lie
inside `[a N, b N]`, an interval whose width the hypothesis makes small.
This is the one place the vanishing lengths do analytic work here. -/
theorem lower_endpoints_seqCauchy {a b : Nat -> alpha}
    (hnest : F.NestedClosedIntervals a b)
    (hlen : F.IntervalLengthsToZero a b) :
    F.SeqCauchy a := by
  intro eps heps
  cases hlen eps heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n m hn hm
      have hlenN :
          F.lt (F.sub (b N) (a N)) eps :=
        NestedBasic.length_lt_of_close_to_zero F hnest
          (hN N (Nat.le_refl N))
      have hnmem :
          And (F.le (a N) (a n)) (F.le (a n) (b N)) := by
        constructor
        · exact hnest.right.left N n hn
        · exact F.le_trans (hnest.left n)
            (hnest.right.right N n hn)
      have hmmem :
          And (F.le (a N) (a m)) (F.le (a m) (b N)) := by
        constructor
        · exact hnest.right.left N m hm
        · exact F.le_trans (hnest.left m)
            (hnest.right.right N m hm)
      exact NestedBasic.interval_points_close F hnmem hmmem hlenN

/-- The Cauchy node converges the left endpoints, their limit is a common
point by `NestedBasic.lower_limit_in_interval`, and uniqueness is
`NestedBasic.common_points_equal`. Note the reach of this module: what is
proved is the vanishing-length clause of the nested node only, the plain
common-point clause making no such demand on lengths, and `Routes` builds
the nested node of its Cauchy route through `FromMonotoneNested`
instead. -/
theorem unique_point_of_lengths_zero
    (hcauchy : F.CauchyCriterionPrinciple)
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
  have ha_cauchy : F.SeqCauchy a :=
    lower_endpoints_seqCauchy F hnest hlen
  cases hcauchy.converges a ha_cauchy with
  | intro l hl =>
      refine Exists.intro l ?_
      have hlmem :
          forall n : Nat,
            And (F.le (a n) l) (F.le l (b n)) :=
        NestedBasic.lower_limit_in_interval F hnest hl
      refine And.intro hlmem ?_
      intro y hy
      exact NestedBasic.common_points_equal F hnest hlen hlmem hy

end FromCauchyNested
end IsOrderedFieldBaseLike
end Tautology
