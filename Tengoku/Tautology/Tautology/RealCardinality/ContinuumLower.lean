import Tengoku.Tautology.Tautology.RealCardinality.BinaryIntervals
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements
import Tengoku.Tautology.Tautology.RealSequence.Principles.FromSupNested
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Continuum

/-!
# At least continuum many points

The lower half of the cardinality computation: a Dedekind-complete ordered
field admits an injection from the binary sequences, so it has at least
continuum many points.

A bit sequence is read as a route through the tree of `BinaryIntervals`,
producing the nested chain `binaryInterval bits` with endpoint projections
`binaryLeft` and `binaryRight`. Completeness turns the chain into a point,
`binaryPoint`, and the assignment is injective because two codes that first
differ at some position drive their chains into the two disjoint children of a
common parent -- the gap left by the asymmetric cut is doing the work.

## Why uniqueness is never needed

The chosen point is picked classically out of the nested-interval principle and
nothing pins it down inside its chain. That costs nothing here: injectivity is
proved by separating the two chains, not by identifying the points. This is why
the file never establishes that the interval lengths tend to zero, and never
touches the uniqueness half of the nested-interval principle.

## Position and role

Implementation module. Everything before `binaryPoint` lives under
`IsOrderedFieldBaseLike` and holds over any ordered field; from `binaryPoint`
on the namespace is `IsDedekindCompleteOrderedFieldBaseLike`, and completeness
enters through `RealSequence.Principles.FromSupNested.nestedIntervalPrinciple`.
Note that this is the generic entry point of the completeness route graph
applied directly to a complete field, not the principle exported by
`Tautology.RealSequence.Principles.Selected`; this module does not go through
the selected route.

`continuumLowerBound` is consumed by `Continuum` in this region and by
`Tautology.RealTheory.Cardinality`, which specialises it to the selected
carrier.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Endpoint pair of the dyadic interval chain coded by the bit sequence
`bits`: level `0` is `(0, 1)`, and level `n + 1` is the child of level `n`
selected by `bits n`, where `True` keeps the upper quarter and `False` the
lower half. The two children of an interval are separated by a gap, so two
bit sequences that first differ at `n` determine disjoint intervals at
level `n + 1`. Everything here is available in any ordered field;
completeness is not needed to build the chains. -/
noncomputable def binaryInterval
    (bits : Nat -> Prop) : Nat -> Prod alpha alpha
  | 0 => (F.zero, F.one)
  | n + 1 =>
      binaryChildInterval F
        (binaryInterval bits n).fst
        (binaryInterval bits n).snd
        (bits n)

/-- Left endpoint of the dyadic interval coded by `bits` at level `n`. The
endpoint projections let the chain enter the nested-interval principle,
which is stated on a pair of endpoint sequences rather than on interval
chains. -/
noncomputable def binaryLeft
    (bits : Nat -> Prop) (n : Nat) : alpha :=
  (binaryInterval F bits n).fst

/-- Right endpoint of the dyadic interval coded by `bits` at level `n`; the
companion of `binaryLeft`. -/
noncomputable def binaryRight
    (bits : Nat -> Prop) (n : Nat) : alpha :=
  (binaryInterval F bits n).snd

theorem binaryInterval_strict
    (bits : Nat -> Prop) :
    forall n : Nat,
      F.lt (binaryLeft F bits n) (binaryRight F bits n) := by
  intro n
  induction n with
  | zero =>
      exact zero_lt_one F
  | succ n ih =>
      change
        F.lt
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            (bits n)).fst
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            (bits n)).snd
      exact binaryChildInterval_strict F ih

theorem binaryInterval_step_inside
    (bits : Nat -> Prop) (n : Nat) :
    And
      (F.le (binaryLeft F bits n) (binaryLeft F bits (n + 1)))
      (F.le (binaryRight F bits (n + 1)) (binaryRight F bits n)) := by
  change
    And
      (F.le
        (binaryInterval F bits n).fst
        (binaryChildInterval F
          (binaryInterval F bits n).fst
          (binaryInterval F bits n).snd
          (bits n)).fst)
      (F.le
        (binaryChildInterval F
          (binaryInterval F bits n).fst
          (binaryInterval F bits n).snd
          (bits n)).snd
        (binaryInterval F bits n).snd)
  exact binaryChildInterval_inside F (binaryInterval_strict F bits n)

theorem binaryLeft_mono
    (bits : Nat -> Prop) :
    forall n m : Nat,
      n <= m ->
        F.le (binaryLeft F bits n) (binaryLeft F bits m) := by
  exact monotoneIncreasing_of_step F
    (fun k : Nat => (binaryInterval_step_inside F bits k).left)

theorem binaryRight_antitone
    (bits : Nat -> Prop) :
    forall n m : Nat,
      n <= m ->
        F.le (binaryRight F bits m) (binaryRight F bits n) := by
  exact monotoneDecreasing_of_step F
    (fun k : Nat => (binaryInterval_step_inside F bits k).right)

/-- The chain coded by `bits` is a nested chain of closed intervals. This
packages the ordering facts above into the exact hypothesis the nested-interval
principle consumes, and it holds over any ordered field -- no completeness and
no statement about lengths shrinking to zero. -/
theorem binaryIntervals_nested
    (bits : Nat -> Prop) :
    NestedClosedIntervals F
      (binaryLeft F bits)
      (binaryRight F bits) := by
  exact And.intro
    (fun n => le_of_lt F (binaryInterval_strict F bits n))
    (And.intro
      (binaryLeft_mono F bits)
      (binaryRight_antitone F bits))

theorem binaryInterval_eq_of_prefix
    (bits bits' : Nat -> Prop) :
    forall n : Nat,
      (forall k : Nat, k < n -> bits k = bits' k) ->
        binaryInterval F bits n = binaryInterval F bits' n := by
  intro n
  induction n with
  | zero =>
      intro _h
      rfl
  | succ n ih =>
      intro h
      have hprev :
          forall k : Nat, k < n -> bits k = bits' k := by
        intro k hk
        exact h k (by omega)
      have hbit : bits n = bits' n :=
        h n (Nat.lt_succ_self n)
      change
        binaryChildInterval F
          (binaryInterval F bits n).fst
          (binaryInterval F bits n).snd
          (bits n) =
        binaryChildInterval F
          (binaryInterval F bits' n).fst
          (binaryInterval F bits' n).snd
          (bits' n)
      rw [ih hprev, hbit]

/-- Two codes that first differ at position `n` have no point in common at
stage `n + 1`: the shared prefix drives both chains into the same parent, and
the differing bit then sends them into the two children, which the gap between
the cutting points keeps apart. This is the separation the whole lower bound
rests on, and it is why the children are a half and a quarter rather than two
halves. -/
theorem binaryIntervals_no_common_of_diff
    {bits bits' : Nat -> Prop} {n : Nat} {x : alpha}
    (hprefix : forall k : Nat, k < n -> bits k = bits' k)
    (hdiff : Not (bits n = bits' n))
    (hx :
      ClosedIntervalMem F
        (binaryLeft F bits (n + 1))
        (binaryRight F bits (n + 1))
        x)
    (hy :
      ClosedIntervalMem F
        (binaryLeft F bits' (n + 1))
        (binaryRight F bits' (n + 1))
        x) :
    False := by
  classical
  have hparent :
      binaryInterval F bits n = binaryInterval F bits' n :=
    binaryInterval_eq_of_prefix F bits bits' n hprefix
  change
    ClosedIntervalMem F
      (binaryChildInterval F
        (binaryInterval F bits n).fst
        (binaryInterval F bits n).snd
        (bits n)).fst
      (binaryChildInterval F
        (binaryInterval F bits n).fst
        (binaryInterval F bits n).snd
        (bits n)).snd
      x at hx
  change
    ClosedIntervalMem F
      (binaryChildInterval F
        (binaryInterval F bits' n).fst
        (binaryInterval F bits' n).snd
        (bits' n)).fst
      (binaryChildInterval F
        (binaryInterval F bits' n).fst
        (binaryInterval F bits' n).snd
        (bits' n)).snd
      x at hy
  rw [<- hparent] at hy
  by_cases hb : bits n
  · by_cases hb' : bits' n
    · have heq : bits n = bits' n := propext
        (Iff.intro (fun _ => hb') (fun _ => hb))
      exact hdiff heq
    · have hxTrue :
        ClosedIntervalMem F
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            True).fst
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            True).snd
          x := by
          simpa [hb] using hx
      have hfalse : bits' n = False := propext
        (Iff.intro (fun h => False.elim (hb' h)) (fun h => False.elim h))
      have hyFalse :
        ClosedIntervalMem F
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            False).fst
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            False).snd
          x := by
          simpa [hfalse] using hy
      exact binaryChildIntervals_disjoint F
        (binaryInterval_strict F bits n) hyFalse hxTrue
  · by_cases hb' : bits' n
    · have hfalse : bits n = False := propext
        (Iff.intro (fun h => False.elim (hb h)) (fun h => False.elim h))
      have hxFalse :
        ClosedIntervalMem F
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            False).fst
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            False).snd
          x := by
          simpa [hfalse] using hx
      have hyTrue :
        ClosedIntervalMem F
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            True).fst
          (binaryChildInterval F
            (binaryInterval F bits n).fst
            (binaryInterval F bits n).snd
            True).snd
          x := by
          simpa [hb'] using hy
      exact binaryChildIntervals_disjoint F
        (binaryInterval_strict F bits n) hxFalse hyTrue
    · have heq : bits n = bits' n := propext
        (Iff.intro (fun h => False.elim (hb h))
          (fun h => False.elim (hb' h)))
      exact hdiff heq

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}

/-- A point common to every interval of the chain coded by `bits`, taken from
the nested-interval principle `FromSupNested.nestedIntervalPrinciple`. This
is the first place where Dedekind completeness is used: the chains exist in
any ordered field, but only completeness guarantees a point inside every
chain. The point is chosen classically; injectivity of the assignment comes
from disjoint chains, not from uniqueness of the chosen point. -/
noncomputable def binaryPoint
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha)
    (bits : Foundation.Cardinal.BinarySequences) : alpha := by
  classical
  let F := IsDedekindCompleteOrderedFieldBaseLike.field C
  let nested := FromSupNested.nestedIntervalPrinciple C
  exact Classical.choose
    (nested.exists_point
      (F.binaryLeft bits)
      (F.binaryRight bits)
      (F.binaryIntervals_nested bits))

/-- The chosen point lies in every interval of its own chain, which is what
lets the separation lemma be applied to it. -/
theorem binaryPoint_mem
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha)
    (bits : Foundation.Cardinal.BinarySequences)
    (n : Nat) :
    let F := IsDedekindCompleteOrderedFieldBaseLike.field C
    F.ClosedIntervalMem
      (F.binaryLeft bits n)
      (F.binaryRight bits n)
      (binaryPoint C bits) := by
  classical
  let F := IsDedekindCompleteOrderedFieldBaseLike.field C
  let nested := FromSupNested.nestedIntervalPrinciple C
  have hspec :=
    Classical.choose_spec
      (nested.exists_point
        (F.binaryLeft bits)
        (F.binaryRight bits)
        (F.binaryIntervals_nested bits))
  exact hspec n

/-- Distinct codes give distinct points, so the assignment is injective. The
argument is by contradiction on the first position where two codes differ: both
points would then have to lie in the two separated children at once. Note that
uniqueness of the point in a chain is never needed. -/
theorem binaryPoint_injective
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha) :
    Foundation.Cardinal.Injective (binaryPoint C) := by
  classical
  intro bits bits' hpoint
  let F := IsDedekindCompleteOrderedFieldBaseLike.field C
  have hprefix :
      forall n : Nat,
        forall k : Nat, k < n -> bits k = bits' k := by
    intro n
    induction n with
    | zero =>
        intro k hk
        exact False.elim (Nat.not_lt_zero k hk)
    | succ n ih =>
        intro k hk
        by_cases hkn : k < n
        · exact ih k hkn
        · have hk_eq : k = n := by omega
          rw [hk_eq]
          by_cases hsame : bits n = bits' n
          · exact hsame
          · have hx :
                F.ClosedIntervalMem
                  (F.binaryLeft bits (n + 1))
                  (F.binaryRight bits (n + 1))
                  (binaryPoint C bits') := by
              have hmem := binaryPoint_mem C bits (n + 1)
              rw [hpoint] at hmem
              exact hmem
            have hy :
                F.ClosedIntervalMem
                  (F.binaryLeft bits' (n + 1))
                  (F.binaryRight bits' (n + 1))
                  (binaryPoint C bits') :=
              binaryPoint_mem C bits' (n + 1)
            exact False.elim
              (F.binaryIntervals_no_common_of_diff
                (bits := bits) (bits' := bits') (n := n)
                (x := binaryPoint C bits')
                ih hsame hx hy)
  apply funext
  intro n
  exact hprefix (n + 1) n (Nat.lt_succ_self n)

/-- Any Dedekind-complete ordered field admits an injection of binary
sequences, and therefore has at least continuum many points. The witness is
`binaryPoint`: bit sequences that first differ at `n` determine disjoint
level `n + 1` intervals, so distinct sequences get distinct points. This is
a statement about every complete field, not about the reals specifically;
`Tautology.RealTheory.Cardinality` specialises it to the carrier in use. -/
theorem continuumLowerBound
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha) :
    Foundation.Cardinal.ContinuumLowerBound alpha :=
  Exists.intro (binaryPoint C) (binaryPoint_injective C)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
