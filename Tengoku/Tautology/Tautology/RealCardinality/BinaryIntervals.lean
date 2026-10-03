import Tengoku.Tautology.Tautology.RealCardinality.IntervalAvoidance

/-!
# Binary choice between the two children

A thin layer over `IntervalAvoidance`: `binaryChildInterval` selects the right
child when a bit holds and the left child otherwise, and the three facts a
consumer needs are proved -- either child is a genuine interval, either is
contained in the parent, and the two are disjoint.

The selector takes a bare `Prop` rather than a `Bool`, so that a decision
sequence `Nat -> Prop` can drive the iteration without any conversion; that is
the shape `Foundation.Cardinal.BinarySequences` arrives in.

## Position and role

Implementation module, sitting between `IntervalAvoidance` and
`ContinuumLower`, which iterates this step once per bit. Disjointness of the
two children is what later turns "two codes first differ at position `n`" into
"their intervals at stage `n + 1` share no point", so the lower bound needs no
uniqueness statement about points in a chain.

Stated over an arbitrary ordered field `(F : IsOrderedFieldBaseLike alpha)`;
completeness plays no part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The child of `[a, b]` selected by the proposition `bit`: the right child
`[secondMidpoint a b, b]` when `bit` holds, the left child
`[a, firstMidpoint a b]` when it fails. The selector is a bare `Prop` rather
than a boolean, so a whole decision sequence `Nat -> Prop` can drive the
iteration one step at a time, as the continuum lower bound does. -/
noncomputable def binaryChildInterval
    (F : IsOrderedFieldBaseLike alpha)
    (a b : alpha) (bit : Prop) : Prod alpha alpha := by
  classical
  exact
    if bit then
      (secondMidpoint F a b, b)
    else
      (a, firstMidpoint F a b)

theorem binaryChildInterval_false (a b : alpha) :
    binaryChildInterval F a b False = (a, firstMidpoint F a b) := by
  unfold binaryChildInterval
  simp

theorem binaryChildInterval_true (a b : alpha) :
    binaryChildInterval F a b True = (secondMidpoint F a b, b) := by
  unfold binaryChildInterval
  simp

/-- Either child of a genuine interval is again a genuine interval, so the
selection can be iterated forever. -/
theorem binaryChildInterval_strict {a b : alpha} {bit : Prop}
    (hab : F.lt a b) :
    F.lt
      (binaryChildInterval F a b bit).fst
      (binaryChildInterval F a b bit).snd := by
  classical
  by_cases hbit : bit
  · unfold binaryChildInterval
    simp [hbit, secondMidpoint_lt_right F hab]
  · unfold binaryChildInterval
    simp [hbit, firstMidpoint_left_lt F hab]

/-- Either child stays inside its parent, so iterating the selection
produces nested intervals. -/
theorem binaryChildInterval_inside {a b : alpha} {bit : Prop}
    (hab : F.lt a b) :
    And
      (F.le a (binaryChildInterval F a b bit).fst)
      (F.le (binaryChildInterval F a b bit).snd b) := by
  classical
  by_cases hbit : bit
  · unfold binaryChildInterval
    simp [hbit]
    exact And.intro
      (secondMidpoint_left_le F hab)
      (F.le_refl b)
  · unfold binaryChildInterval
    simp [hbit]
    exact And.intro
      (F.le_refl a)
      (firstMidpoint_le_right F hab)

/-- No point lies in both children: the gap between the cut points separates
them. This is what keeps distinct decision sequences apart once they are coded
into points, as `Tautology.RealCardinality.ContinuumLower` does -- two
sequences that first differ at some index send their points into disjoint
children. -/
theorem binaryChildIntervals_disjoint {a b x : alpha}
    (hab : F.lt a b)
    (hleft :
      ClosedIntervalMem F
        (binaryChildInterval F a b False).fst
        (binaryChildInterval F a b False).snd
        x)
    (hright :
      ClosedIntervalMem F
        (binaryChildInterval F a b True).fst
        (binaryChildInterval F a b True).snd
        x) :
    False := by
  rw [binaryChildInterval_false F a b] at hleft
  rw [binaryChildInterval_true F a b] at hright
  have hdc : F.le (secondMidpoint F a b) (firstMidpoint F a b) :=
    F.le_trans hright.left hleft.right
  exact (not_le_of_lt F (first_lt_secondMidpoint F hab)) hdc

end IsOrderedFieldBaseLike
end Tautology
