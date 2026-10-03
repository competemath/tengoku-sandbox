import Tengoku.Tautology.Tautology.RealBootstrap.Supremum
import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Entry: the supremum property gives nested intervals

The entry the selected route takes, and the shortest of the three. The left
endpoints of a nested chain are bounded above by any right endpoint, so their
supremum exists; it lies in every stage, and when the lengths tend to zero it
is the only such point.

Completeness is spent once, on that supremum.

## Position and role

Entry module of the completeness route graph, exporting
`nestedIntervalPrinciple`. Besides the assemblies in
`Tautology.RealSequence.Principles.Routes` and the choice in
`Tautology.RealSequence.Principles.Selected`, it has direct consumers:
`Tautology.RealCardinality.ContinuumLower` and
`Tautology.RealCardinality.Uncountable` apply it to a complete field themselves
rather than going through the selected route.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

namespace FromSupNested

/-- The ordered-field reduct of `C`; the supremum property of `C` is used
only through `exists_lub`, in the construction below. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The set of values taken by the sequence -- the set the supremum is taken
over. An independent twin of `FromSupMonotone.Range`; neither file imports
the other. -/
def Range (u : Nat -> alpha) (x : alpha) : Prop :=
  Exists (fun n : Nat => x = u n)

theorem range_nonempty (u : Nat -> alpha) :
    Exists (Range u) :=
  Exists.intro (u 0) (Exists.intro 0 rfl)

/-- The order-theoretic fact the entry runs on: nesting makes every right
endpoint an upper bound of the entire range of left endpoints. Whichever of
`m`, `n` comes first, one of the two monotonicities supplies the chain from
`a m` up to `b n`. -/
theorem upper_endpoint_upperBound {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b)
    (n : Nat) :
    IsUpperBound (F C).le (Range a) (b n) := by
  intro x hx
  cases hx with
  | intro m hm =>
      rw [hm]
      cases Nat.le_total m n with
      | inl hmn =>
          exact (F C).le_trans (hnest.right.left m n hmn)
            (hnest.left n)
      | inr hnm =>
          exact (F C).le_trans (hnest.left m)
            (hnest.right.right n m hnm)

theorem range_bounded_above {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b) :
    Exists (IsUpperBound (F C).le (Range a)) :=
  Exists.intro (b 0) (upper_endpoint_upperBound C hnest 0)

/-- The candidate common point: the least upper bound of the range of the
left endpoints, extracted by choice from `exists_lub`, whose nonemptiness and
boundedness hypotheses the two lemmas above discharge. -/
noncomputable def supLowerEndpoints {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b) : alpha :=
  Classical.choose
    (C.exists_lub (Range a) (range_nonempty a)
      (range_bounded_above C hnest))

theorem supLowerEndpoints_is_lub {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b) :
    IsLeastUpperBound (F C).le (Range a)
      (supLowerEndpoints C hnest) :=
  Classical.choose_spec
    (C.exists_lub (Range a) (range_nonempty a)
      (range_bounded_above C hnest))

/-- The construction lands in every interval at once: each `a n` is a member
of the range and so sits below the supremum, while each `b n` is an upper
bound of the range and so sits above it. This is the entire existence
argument. -/
theorem supLowerEndpoints_in_interval {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b)
    (n : Nat) :
    And
      ((F C).le (a n) (supLowerEndpoints C hnest))
      ((F C).le (supLowerEndpoints C hnest) (b n)) := by
  have hs : IsLeastUpperBound (F C).le (Range a)
      (supLowerEndpoints C hnest) :=
    supLowerEndpoints_is_lub C hnest
  constructor
  · exact IsOrderedFieldBaseLike.le_lub_of_mem (F C) hs
      (Exists.intro n rfl)
  · exact IsOrderedFieldBaseLike.lub_le_of_upper (F C) hs
      (upper_endpoint_upperBound C hnest n)

theorem sub_le_sub_of_le_of_le {x y a b : alpha}
    (hxb : (F C).le x b)
    (hay : (F C).le a y) :
    (F C).le ((F C).sub x y) ((F C).sub b a) :=
  IsOrderedFieldBaseLike.sub_le_sub_of_le_of_le (F C) hxb hay

theorem common_gap_le_length {a b : Nat -> alpha} {x y : alpha}
    (hx : forall n : Nat, And ((F C).le (a n) x) ((F C).le x (b n)))
    (hy : forall n : Nat, And ((F C).le (a n) y) ((F C).le y (b n)))
    (n : Nat) :
    (F C).le ((F C).sub x y) ((F C).sub (b n) (a n)) :=
  IsOrderedFieldBaseLike.NestedBasic.common_gap_le_length
    (F C) hx hy n

theorem length_lt_of_close_to_zero {a b : Nat -> alpha} {eps : alpha}
    (hnest : (F C).NestedClosedIntervals a b)
    {n : Nat}
    (hclose :
      (F C).lt
        (IsOrderedFieldBaseLike.abs (F C)
          ((F C).sub ((F C).sub (b n) (a n)) (F C).zero))
        eps) :
    (F C).lt ((F C).sub (b n) (a n)) eps :=
  IsOrderedFieldBaseLike.NestedBasic.length_lt_of_close_to_zero
    (F C) hnest hclose

theorem common_point_le {a b : Nat -> alpha} {x y : alpha}
    (hnest : (F C).NestedClosedIntervals a b)
    (hlen : (F C).IntervalLengthsToZero a b)
    (hx : forall n : Nat, And ((F C).le (a n) x) ((F C).le x (b n)))
    (hy : forall n : Nat, And ((F C).le (a n) y) ((F C).le y (b n))) :
    (F C).le x y :=
  IsOrderedFieldBaseLike.NestedBasic.common_point_le
    (F C) hnest hlen hx hy

theorem common_points_equal {a b : Nat -> alpha} {x y : alpha}
    (hnest : (F C).NestedClosedIntervals a b)
    (hlen : (F C).IntervalLengthsToZero a b)
    (hx : forall n : Nat, And ((F C).le (a n) x) ((F C).le x (b n)))
    (hy : forall n : Nat, And ((F C).le (a n) y) ((F C).le y (b n))) :
    y = x :=
  IsOrderedFieldBaseLike.NestedBasic.common_points_equal
    (F C) hnest hlen hx hy

theorem exists_point {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b) :
    Exists
      (fun x : alpha =>
        forall n : Nat,
          And ((F C).le (a n) x) ((F C).le x (b n))) :=
  Exists.intro (supLowerEndpoints C hnest)
    (supLowerEndpoints_in_interval C hnest)

theorem unique_point_of_lengths_zero {a b : Nat -> alpha}
    (hnest : (F C).NestedClosedIntervals a b)
    (hlen : (F C).IntervalLengthsToZero a b) :
    Exists
      (fun x : alpha =>
        And
          (forall n : Nat,
            And ((F C).le (a n) x) ((F C).le x (b n)))
          (forall y : alpha,
            (forall n : Nat,
              And ((F C).le (a n) y) ((F C).le y (b n))) ->
                y = x)) := by
  refine Exists.intro (supLowerEndpoints C hnest) ?_
  constructor
  · exact supLowerEndpoints_in_interval C hnest
  · intro y hy
    exact common_points_equal C hnest hlen
      (supLowerEndpoints_in_interval C hnest) hy

/-- The first entry of the graph: from the supremum property alone, the
nested-interval node. Existence is the construction above; uniqueness
forwards to `NestedBasic.common_points_equal` and needs no completeness.
`RealCardinality` reaches for this entry directly rather than through the
selected route. -/
theorem nestedIntervalPrinciple :
    (F C).NestedIntervalPrinciple where
  exists_point := by
    intro a b hnest
    exact exists_point C hnest
  unique_point_of_lengths_zero := by
    intro a b hnest hlen
    exact unique_point_of_lengths_zero C hnest hlen

end FromSupNested

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
