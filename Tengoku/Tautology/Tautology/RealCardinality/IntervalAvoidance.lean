import Tengoku.Tautology.Tautology.RealSequence.Algebra

/-!
# Avoiding a point by shrinking an interval

The single step both cardinality arguments of this region are built from: given
a closed interval and an optional point, produce a strictly smaller closed
subinterval that misses the point.

The interval is cut at two places, `firstMidpoint` (the midpoint of `[a, b]`)
and `secondMidpoint` (the midpoint of `[firstMidpoint a b, b]`), leaving the
children `[a, firstMidpoint a b]` and `[secondMidpoint a b, b]` with an open
gap between them. That the children are a half and a quarter rather than two
halves is the design decision of the file: the gap keeps them disjoint as
closed intervals, so whichever child the point falls into, the other avoids it,
and two chains that diverge at some stage can never meet again. Nothing here
keeps a length budget -- avoidance is exact, and no length is ever asked to
tend to zero.

## Position and role

Implementation module, and the base of the region. `BinaryIntervals` wraps the
two children as a bit selector, `Uncountable` iterates the step against an
enumeration, and `ContinuumLower` iterates it against a bit sequence; every
other file here stands on this vocabulary.

Everything is stated over `(F : IsOrderedFieldBaseLike alpha)` -- an arbitrary
ordered field, threaded through as an explicit parameter because the project
uses no typeclasses. Completeness is not used anywhere in this file, and no
result here is about the selected real line.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Membership in the closed interval `[a, b]`, stated pointwise as
`a ≤ x ≤ b`. The ordered-field structure is an explicit argument throughout
this file, so nothing here is specific to the selected real line: any
ordered field will do. -/
def ClosedIntervalMem (a b x : alpha) : Prop :=
  And (F.le a x) (F.le x b)

/-- The optional point `p` lies outside `[a, b]`. A `none` is vacuously
avoided, which is what lets the shrinking step below be driven directly by the
`Nat -> Option alpha` enumerations of `Tautology.Foundation.Cardinal`: an
unused slot costs nothing. -/
def OptionPointAvoided (p : Option alpha) (a b : alpha) : Prop :=
  match p with
  | none => True
  | some x => Not (ClosedIntervalMem F a b x)

/-- The first of the two cut points that split an interval in this region:
the midpoint of the endpoints. -/
def firstMidpoint (a b : alpha) : alpha :=
  midpoint F a b

/-- The second cut point: the midpoint of `[firstMidpoint a b, b]`. Because
the two cut points sit strictly apart, the left child `[a, firstMidpoint a b]`
and the right child `[secondMidpoint a b, b]` are disjoint closed intervals,
not two halves sharing a midpoint. -/
def secondMidpoint (a b : alpha) : alpha :=
  midpoint F (firstMidpoint F a b) b

/-- Shrink `[a, b]` to whichever child the optional point `p` does not lie
in: if `p` is inside the left child, cross the gap to the right one,
otherwise keep the left one. The answer is a pair of endpoints rather than a
predicate, because the consumers iterate the step and read off endpoint
sequences. -/
noncomputable def shrinkAvoidingPoint
    (a b : alpha) (p : Option alpha) : Prod alpha alpha := by
  classical
  let c := firstMidpoint F a b
  let d := secondMidpoint F a b
  exact
    match p with
    | none => (a, c)
    | some x =>
        if h : ClosedIntervalMem F a c x then
          (d, b)
        else
          (a, c)

/-- With `a < b`, the left child `[a, firstMidpoint a b]` is a genuine
interval. -/
theorem firstMidpoint_left_lt {a b : alpha}
    (hab : F.lt a b) :
    F.lt a (firstMidpoint F a b) :=
  left_lt_midpoint F hab

theorem firstMidpoint_lt_right {a b : alpha}
    (hab : F.lt a b) :
    F.lt (firstMidpoint F a b) b :=
  midpoint_lt_right F hab

theorem firstMidpoint_left_le {a b : alpha}
    (hab : F.lt a b) :
    F.le a (firstMidpoint F a b) :=
  le_of_lt F (firstMidpoint_left_lt F hab)

/-- The first cut point never passes `b`; this weak form is what the
containment of the left child inside its parent runs on. -/
theorem firstMidpoint_le_right {a b : alpha}
    (hab : F.lt a b) :
    F.le (firstMidpoint F a b) b :=
  le_of_lt F (firstMidpoint_lt_right F hab)

/-- The two cut points are strictly ordered, leaving an open gap between the
children. Every disjointness and avoidance argument in this region rests on
that gap. -/
theorem first_lt_secondMidpoint {a b : alpha}
    (hab : F.lt a b) :
    F.lt (firstMidpoint F a b) (secondMidpoint F a b) := by
  unfold secondMidpoint
  exact left_lt_midpoint F (firstMidpoint_lt_right F hab)

/-- With `a < b`, the right child `[secondMidpoint a b, b]` is a genuine
interval. -/
theorem secondMidpoint_lt_right {a b : alpha}
    (hab : F.lt a b) :
    F.lt (secondMidpoint F a b) b := by
  unfold secondMidpoint
  exact midpoint_lt_right F (firstMidpoint_lt_right F hab)

/-- The second cut point never falls below `a`, so the right child stays
inside its parent. -/
theorem secondMidpoint_left_le {a b : alpha}
    (hab : F.lt a b) :
    F.le a (secondMidpoint F a b) :=
  F.le_trans
    (firstMidpoint_left_le F hab)
    (le_of_lt F (first_lt_secondMidpoint F hab))

theorem secondMidpoint_le_right {a b : alpha}
    (hab : F.lt a b) :
    F.le (secondMidpoint F a b) b :=
  le_of_lt F (secondMidpoint_lt_right F hab)

/-- The shrunken interval is still nondegenerate, so the shrinking can be
iterated without end: every interval along such a run is a genuine closed
interval. -/
theorem shrinkAvoidingPoint_strict {a b : alpha} {p : Option alpha}
    (hab : F.lt a b) :
    F.lt
      (shrinkAvoidingPoint F a b p).fst
      (shrinkAvoidingPoint F a b p).snd := by
  classical
  cases p with
  | none =>
      unfold shrinkAvoidingPoint
      simp [firstMidpoint_left_lt F hab]
  | some x =>
      unfold shrinkAvoidingPoint
      by_cases hx : ClosedIntervalMem F a (firstMidpoint F a b) x
      · simp [hx, secondMidpoint_lt_right F hab]
      · simp [hx, firstMidpoint_left_lt F hab]

/-- Both endpoints of the answer stay between `a` and `b`, which is what
makes repeated shrinking produce nested intervals. -/
theorem shrinkAvoidingPoint_inside {a b : alpha} {p : Option alpha}
    (hab : F.lt a b) :
    And
      (F.le a (shrinkAvoidingPoint F a b p).fst)
      (F.le (shrinkAvoidingPoint F a b p).snd b) := by
  classical
  cases p with
  | none =>
      unfold shrinkAvoidingPoint
      exact And.intro
        (F.le_refl a)
        (firstMidpoint_le_right F hab)
  | some x =>
      unfold shrinkAvoidingPoint
      by_cases hx : ClosedIntervalMem F a (firstMidpoint F a b) x
      · simp [hx]
        exact And.intro
          (secondMidpoint_left_le F hab)
          (F.le_refl b)
      · simp [hx]
        exact And.intro
          (F.le_refl a)
          (firstMidpoint_le_right F hab)

/-- The step keeps its promise: `p` lies outside the interval it returns --
when `p` is a point of the left child, the chosen right child excludes it
because the gap separates the two children, and a `none` is avoided
vacuously. This one-step avoidance is the engine of the uncountability
argument in `Tautology.RealCardinality.Uncountable`. -/
theorem shrinkAvoidingPoint_avoids {a b : alpha} {p : Option alpha}
    (hab : F.lt a b) :
    OptionPointAvoided F p
      (shrinkAvoidingPoint F a b p).fst
      (shrinkAvoidingPoint F a b p).snd := by
  classical
  cases p with
  | none =>
      unfold OptionPointAvoided
      trivial
  | some x =>
      unfold shrinkAvoidingPoint
      by_cases hx : ClosedIntervalMem F a (firstMidpoint F a b) x
      · simp [hx]
        intro hbad
        have hdc : F.le (secondMidpoint F a b) (firstMidpoint F a b) :=
          F.le_trans hbad.left hx.right
        exact
          (not_le_of_lt F (first_lt_secondMidpoint F hab)) hdc
      · simp [hx]
        exact hx

end IsOrderedFieldBaseLike
end Tautology
