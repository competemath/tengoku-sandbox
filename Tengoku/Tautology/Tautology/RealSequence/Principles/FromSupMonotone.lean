import Tengoku.Tautology.Tautology.RealBootstrap.Supremum
import Tengoku.Tautology.Tautology.RealSequence.Algebra
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Entry: the supremum property gives monotone convergence

The second way into the graph. An increasing sequence bounded above has a
supremum, and the sequence converges to it -- shown with a single epsilon and a
two-sided squeeze rather than a halving argument. The decreasing case is
obtained by negation.

Completeness is spent once, on the supremum of the range.

## Position and role

Entry module exporting `monotoneConvergence`. It feeds
`RealSequence.Principles.Routes.fromMonotone`; the selected route enters
through `Tautology.RealSequence.Principles.FromSupNested` instead, so this
entry is proved and not travelled.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

namespace FromSupMonotone

/-- The ordered-field reduct of `C`; the supremum property of `C` is used
only through `exists_lub`, in the construction below. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The set of values taken by the sequence -- the set the supremum is taken
over. An independent twin of `FromSupNested.Range`; neither file imports
the other. -/
def Range (u : Nat -> alpha) (x : alpha) : Prop :=
  Exists (fun n : Nat => x = u n)

theorem range_nonempty (u : Nat -> alpha) :
    Exists (Range u) :=
  Exists.intro (u 0) (Exists.intro 0 rfl)

theorem range_bounded_above {u : Nat -> alpha}
    (hbdd : (F C).SeqBoundedAbove u) :
    Exists (IsUpperBound (F C).le (Range u)) := by
  cases hbdd with
  | intro B hB =>
      refine Exists.intro B ?_
      intro x hx
      cases hx with
      | intro n hn =>
          rw [hn]
          exact hB n

/-- The limit of a bounded increasing sequence, before anything is proved
about it: the least upper bound of the range, extracted by choice from
`exists_lub`. For an increasing sequence the range already climbs toward
this bound, which is what the convergence proof cashes in. -/
noncomputable def supRange {u : Nat -> alpha}
    (hbdd : (F C).SeqBoundedAbove u) : alpha :=
  Classical.choose
    (C.exists_lub (Range u) (range_nonempty u)
      (range_bounded_above C hbdd))

theorem supRange_is_lub {u : Nat -> alpha}
    (hbdd : (F C).SeqBoundedAbove u) :
    IsLeastUpperBound (F C).le (Range u) (supRange C hbdd) :=
  Classical.choose_spec
    (C.exists_lub (Range u) (range_nonempty u)
      (range_bounded_above C hbdd))

/-- The increasing half of the node, proved directly: `s - eps` falls
strictly below the least upper bound, so some term `u N` of the range
already exceeds it; monotonicity carries every later term above it as well,
and the bound itself keeps all terms below `s < s + eps`. One `eps` on each
side, no halving. -/
theorem monotone_increasing_tendsto_sup {u : Nat -> alpha}
    (hmono : (F C).MonotoneIncreasing u)
    (hbdd : (F C).SeqBoundedAbove u) :
    (F C).SeqTendsto u (supRange C hbdd) := by
  intro eps heps
  let s := supRange C hbdd
  have hs : IsLeastUpperBound (F C).le (Range u) s :=
    supRange_is_lub C hbdd
  have hbelow : (F C).lt ((F C).sub s eps) s :=
    IsOrderedFieldBaseLike.sub_lt_self_of_pos (F C) heps
  cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub (F C) hs hbelow with
  | intro x hx =>
      cases hx.left with
      | intro N hxN =>
          refine Exists.intro N ?_
          intro n hn
          rw [hxN] at hx
          have hleft : (F C).lt ((F C).sub s eps) (u n) :=
            IsOrderedFieldBaseLike.lt_of_lt_of_le (F C)
              hx.right (hmono N n hn)
          have hle_s : (F C).le (u n) s :=
            IsOrderedFieldBaseLike.le_lub_of_mem (F C) hs
              (Exists.intro n rfl)
          have hs_lt_s_eps : (F C).lt s ((F C).add s eps) := by
            have h := (F C).add_lt_add_left heps s
            rwa [(F C).add_zero] at h
          have hright : (F C).lt (u n) ((F C).add s eps) :=
            IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
              hle_s hs_lt_s_eps
          exact IsOrderedFieldBaseLike.abs_sub_lt_of_bounds (F C)
            hleft hright

theorem neg_monotone_increasing_of_decreasing {u : Nat -> alpha}
    (hmono : (F C).MonotoneDecreasing u) :
    (F C).MonotoneIncreasing (fun n : Nat => (F C).neg (u n)) :=
  IsOrderedFieldBaseLike.FromCauchyMonotone.neg_monotone_increasing_of_decreasing
    (F C) hmono

theorem neg_bounded_above_of_bounded_below {u : Nat -> alpha}
    (hbdd : (F C).SeqBoundedBelow u) :
    (F C).SeqBoundedAbove (fun n : Nat => (F C).neg (u n)) :=
  IsOrderedFieldBaseLike.FromCauchyMonotone.neg_boundedAbove_of_boundedBelow
    (F C) hbdd

/-- The decreasing half, by negation duality: `-u` is increasing and bounded
above, so it converges to the supremum of its range, and negating the limit
back gives a limit for `u` itself. -/
theorem monotone_decreasing_converges {u : Nat -> alpha}
    (hmono : (F C).MonotoneDecreasing u)
    (hbdd : (F C).SeqBoundedBelow u) :
    Exists (fun l : alpha => (F C).SeqTendsto u l) := by
  let v : Nat -> alpha := fun n => (F C).neg (u n)
  have hvmono : (F C).MonotoneIncreasing v :=
    neg_monotone_increasing_of_decreasing C hmono
  have hvbdd : (F C).SeqBoundedAbove v :=
    neg_bounded_above_of_bounded_below C hbdd
  let L := supRange C hvbdd
  have hvL : (F C).SeqTendsto v L :=
    monotone_increasing_tendsto_sup C hvmono hvbdd
  refine Exists.intro ((F C).neg L) ?_
  have hneg := IsOrderedFieldBaseLike.seqTendsto_neg (F C) hvL
  intro eps heps
  apply Eventually.mono ?_ (hneg eps heps)
  intro n hn
  simpa [v, IsOrderedFieldBaseLike.neg_neg (F C) (u n)] using hn

/-- The second entry of the graph: from the supremum property alone, the
monotone-convergence node, with `exists_lub` spent on the range of the
sequence itself rather than on endpoints. -/
theorem monotoneConvergence :
    (F C).MonotoneConvergencePrinciple where
  increasing := by
    intro u hmono hbdd
    exact Exists.intro (supRange C hbdd)
      (monotone_increasing_tendsto_sup C hmono hbdd)
  decreasing := by
    intro u hmono hbdd
    exact monotone_decreasing_converges C hmono hbdd

end FromSupMonotone

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
