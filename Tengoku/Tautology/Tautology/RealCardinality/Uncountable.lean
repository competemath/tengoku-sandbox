import Tengoku.Tautology.Tautology.Foundation.Cardinal.Continuum
import Tengoku.Tautology.Tautology.RealCardinality.IntervalAvoidance
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements
import Tengoku.Tautology.Tautology.RealSequence.Principles.FromSupNested
import Init.Data.Nat.Lemmas

/-!
# No enumeration exhausts a complete ordered field

Cantor's argument in its nested-interval form. Starting from `[0, 1]`, the
chain `avoidingInterval e` shrinks at step `n` to the child avoiding the `n`-th
value offered by an enumeration `e : Nat -> Option alpha`, so interval `n + 1`
misses `e n`. Any point common to the whole chain is therefore missed by every
slot of the enumeration, which is exactly `every_option_enum_misses`, and
`uncountable` restates it in the vocabulary of `Tautology.Foundation.Cardinal`.

The shrinking step itself is not defined here: it comes from
`Tautology.RealCardinality.IntervalAvoidance`, which cuts a closed interval
into a half and a quarter with a gap between them and hands back whichever
child misses a given optional point. Read that module first -- it is the
engine, and every property used below (`shrinkAvoidingPoint_strict`, `_inside`,
`_avoids`) is proved there. "Avoids" there means the point is outside the
closed child, endpoints included.

Enumerations are partial, `Nat -> Option alpha` rather than `Nat -> alpha`,
because that is the shape countability takes in
`Tautology.Foundation.Cardinal`. An empty slot is vacuously avoided, so the
step needs no special case for it, and a total enumeration embeds through
`some`, which makes the conclusion the stronger of the two.

## Where completeness enters, and by which route

The file falls into two halves. Everything up to and including nestedness lives
under `IsOrderedFieldBaseLike` and holds over any ordered field: the chain, its
endpoint projections, and the avoidance property are all built from the exact
cut of `IntervalAvoidance`, with no limit and no length estimate. Completeness
is used at one point only -- extracting a point common to the chain, through
`RealSequence.Principles.FromSupNested.nestedIntervalPrinciple`, and only its
existence half. Which principle is available there is a route decision recorded
in `RealSequence/Principles/Selected.lean`; this file consumes the selected
route rather than the completeness axiom directly.

Because avoidance is exact, the argument never needs interval lengths to tend
to zero, and so never needs the uniqueness half of the nested-interval
principle.

## Position and role

Implementation module. Its two public results are consumed only by
`Tautology.RealTheory.Cardinality`, which specialises them to the selected
carrier as `RealTheory.uncountable` and `RealTheory.every_option_enum_misses`.
Everything here is a statement about an arbitrary Dedekind-complete ordered
field, not about the real line as constructed in this library.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The run of closed intervals that starts at `[0, 1]` and, at step `n`,
shrinks so as to push the optional point `e n` outside: interval `n + 1`
avoids `e n`. Only the ordered-field structure is used here; completeness
waits until the two theorems at the end of this file. -/
noncomputable def avoidingInterval
    (e : Nat -> Option alpha) : Nat -> Prod alpha alpha
  | 0 => (F.zero, F.one)
  | n + 1 =>
      shrinkAvoidingPoint F
        (avoidingInterval e n).fst
        (avoidingInterval e n).snd
        (e n)

/-- Left endpoint of the `n`-th avoiding interval; with its companion it
turns the run of intervals into the pair of endpoint sequences that the
nested interval principle consumes. -/
noncomputable def avoidingLeft
    (e : Nat -> Option alpha) (n : Nat) : alpha :=
  (avoidingInterval F e n).fst

/-- Right endpoint of the `n`-th avoiding interval, the companion of
`avoidingLeft`. -/
noncomputable def avoidingRight
    (e : Nat -> Option alpha) (n : Nat) : alpha :=
  (avoidingInterval F e n).snd

theorem avoidingInterval_strict
    (e : Nat -> Option alpha) :
    forall n : Nat,
      F.lt (avoidingLeft F e n) (avoidingRight F e n) := by
  intro n
  induction n with
  | zero =>
      exact zero_lt_one F
  | succ n ih =>
      change
        F.lt
          (shrinkAvoidingPoint F
            (avoidingInterval F e n).fst
            (avoidingInterval F e n).snd
            (e n)).fst
          (shrinkAvoidingPoint F
            (avoidingInterval F e n).fst
            (avoidingInterval F e n).snd
            (e n)).snd
      exact shrinkAvoidingPoint_strict F ih

theorem avoidingInterval_step_inside
    (e : Nat -> Option alpha) (n : Nat) :
    And
      (F.le (avoidingLeft F e n) (avoidingLeft F e (n + 1)))
      (F.le (avoidingRight F e (n + 1)) (avoidingRight F e n)) := by
  change
    And
      (F.le
        (avoidingInterval F e n).fst
        (shrinkAvoidingPoint F
          (avoidingInterval F e n).fst
          (avoidingInterval F e n).snd
          (e n)).fst)
      (F.le
        (shrinkAvoidingPoint F
          (avoidingInterval F e n).fst
          (avoidingInterval F e n).snd
          (e n)).snd
        (avoidingInterval F e n).snd)
  exact shrinkAvoidingPoint_inside F (avoidingInterval_strict F e n)

theorem avoidingLeft_mono
    (e : Nat -> Option alpha) :
    forall n m : Nat,
      n <= m ->
        F.le (avoidingLeft F e n) (avoidingLeft F e m) := by
  exact monotoneIncreasing_of_step F
    (fun k : Nat => (avoidingInterval_step_inside F e k).left)

theorem avoidingRight_antitone
    (e : Nat -> Option alpha) :
    forall n m : Nat,
      n <= m ->
        F.le (avoidingRight F e m) (avoidingRight F e n) := by
  exact monotoneDecreasing_of_step F
    (fun k : Nat => (avoidingInterval_step_inside F e k).right)

/-- The avoiding chain is a nested chain of closed intervals, in the form the
nested-interval principle consumes. It holds over any ordered field; nothing
here asks the lengths to shrink to zero, and nothing here needs completeness.
-/
theorem avoidingIntervals_nested
    (e : Nat -> Option alpha) :
    NestedClosedIntervals F
      (avoidingLeft F e)
      (avoidingRight F e) := by
  exact And.intro
    (fun n => le_of_lt F (avoidingInterval_strict F e n))
    (And.intro
      (avoidingLeft_mono F e)
      (avoidingRight_antitone F e))

/-- Interval `n + 1` avoids the `n`-th enumerated point -- note the offset,
which is what lets stage `0` be the starting interval. Together with nestedness
this is the whole diagonal argument: every point offered by the enumeration is
excluded from some stage, hence from anything common to all stages. -/
theorem avoidingInterval_avoids
    (e : Nat -> Option alpha) (n : Nat) :
    OptionPointAvoided F (e n)
      (avoidingLeft F e (n + 1))
      (avoidingRight F e (n + 1)) := by
  change
    OptionPointAvoided F (e n)
      (shrinkAvoidingPoint F
        (avoidingInterval F e n).fst
        (avoidingInterval F e n).snd
        (e n)).fst
      (shrinkAvoidingPoint F
        (avoidingInterval F e n).fst
        (avoidingInterval F e n).snd
        (e n)).snd
  exact shrinkAvoidingPoint_avoids F (avoidingInterval_strict F e n)

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}

/-- Every enumeration `e : Nat -> Option alpha` of a Dedekind-complete ordered
field misses a point. The avoiding intervals of the ordered-field part above
are nested, and completeness enters exactly here, through the nested interval
principle of `Tautology.RealSequence.Principles.FromSupNested`: the common
point lies in the interval that avoids `e n` for every `n`, so no slot of `e`
can hold it. Avoidance is exact at each step, so no control of interval lengths
is needed. -/
theorem every_option_enum_misses
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha) :
    forall e : Nat -> Option alpha,
      Exists (fun x : alpha =>
        forall n : Nat, Not (e n = some x)) := by
  intro e
  let F := IsDedekindCompleteOrderedFieldBaseLike.field C
  let nested :=
    FromSupNested.nestedIntervalPrinciple C
  have hnest :
      F.NestedClosedIntervals
        (F.avoidingLeft e)
        (F.avoidingRight e) :=
    F.avoidingIntervals_nested e
  cases nested.exists_point
      (F.avoidingLeft e) (F.avoidingRight e) hnest with
  | intro x hx =>
      refine Exists.intro x ?_
      intro n hen
      have hmem :
          F.ClosedIntervalMem
            (F.avoidingLeft e (n + 1))
            (F.avoidingRight e (n + 1))
            x :=
        hx (n + 1)
      have havoid :=
        F.avoidingInterval_avoids e n
      rw [hen] at havoid
      exact havoid hmem

/-- Any Dedekind-complete ordered field is uncountable, in the enumeration
sense of `Tautology.Foundation.Cardinal`; `Tautology.RealTheory.Cardinality`
specializes it to the library's selected real line. -/
theorem uncountable
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha) :
    Foundation.Cardinal.Uncountable alpha :=
  Foundation.Cardinal.uncountable_of_every_option_enum_misses
    (every_option_enum_misses C)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
