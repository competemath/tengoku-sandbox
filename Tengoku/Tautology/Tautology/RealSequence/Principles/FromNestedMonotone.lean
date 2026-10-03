import Tengoku.Tautology.Tautology.RealSequence.Principles.Dyadic
import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic

/-!
# Edge: nested intervals give monotone convergence

The first crossing on the selected route. Given an increasing sequence bounded
above, bisection produces a nested chain: keep the half that still has a term
above its lower end, and the sequence is eventually trapped in every stage.

The hypothesis is a `DyadicArchimedeanPrinciple`, spent once, on driving the
stage widths `(right - left) / 2 ^ n` to zero. Widths are available in closed
form here, which is why the dyadic form of the Archimedean property is the one
that fits.

## Position and role

Edge module exporting `monotoneConvergence`.
`Tautology.RealSequence.Principles.Selected` travels it, feeding in the
nested-interval principle obtained at the entry and the dyadic principle
derived from completeness; the same edge is used by
`Tautology.RealCompactness.ClosedInterval.FromNestedSequential` in the same
spirit.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace FromNestedMonotone

/-- The unbundled form of boundedness above: every term of `u` lies below
`B`. The bisection below must start from a concrete bound, whereas
`SeqBoundedAbove` keeps its bound inside an existential, so the hypothesis
is stated in this shape and unpacked once, in `increasing_converges`. -/
def IsUpperBoundSeq (u : Nat -> alpha) (B : alpha) : Prop :=
  forall n : Nat, F.le (u n) B

/-- Some term of `u` rises strictly above `x`. This is the question every
bisection step asks of the midpoint, and its answer selects which half is
kept. -/
def HasTermAbove (u : Nat -> alpha) (x : alpha) : Prop :=
  Exists (fun n : Nat => F.lt x (u n))

/-- One bisection step: keep the right half when some term rises above the
midpoint, and the left half otherwise. The case split is decided classically,
which is what makes the endpoint sequences below noncomputable.
-/
noncomputable def stepInterval (u : Nat -> alpha)
    (I : alpha × alpha) : alpha × alpha := by
  classical
  let a := I.fst
  let b := I.snd
  let m := midpoint F a b
  exact if HasTermAbove F u m then (m, b) else (a, m)

/-- The bisection iterated `n` times from the interval `[u 0, B]` between the
first term and the bound. -/
noncomputable def bisectInterval (u : Nat -> alpha) (B : alpha) :
    Nat -> alpha × alpha
  | 0 => (u 0, B)
  | n + 1 => stepInterval F u (bisectInterval u B n)

/-- The left endpoint of the bisected interval at stage `n`, read off the
pair the iteration produces. -/
noncomputable def lower (u : Nat -> alpha) (B : alpha) (n : Nat) :
    alpha :=
  (bisectInterval F u B n).fst

/-- The right endpoint at stage `n`, the other component of the same
pair. -/
noncomputable def upper (u : Nat -> alpha) (B : alpha) (n : Nat) :
    alpha :=
  (bisectInterval F u B n).snd

theorem lower_zero (u : Nat -> alpha) (B : alpha) :
    lower F u B 0 = u 0 :=
  rfl

theorem upper_zero (u : Nat -> alpha) (B : alpha) :
    upper F u B 0 = B :=
  rfl

theorem lower_succ_right {u : Nat -> alpha} {B : alpha} {n : Nat}
    (h :
      HasTermAbove F u
        (midpoint F (lower F u B n) (upper F u B n))) :
    lower F u B (n + 1) =
      midpoint F (lower F u B n) (upper F u B n) := by
  classical
  have h' :
      HasTermAbove F u
        (midpoint F (bisectInterval F u B n).fst
          (bisectInterval F u B n).snd) := by
    simpa [lower, upper] using h
  simp [lower, upper, bisectInterval, stepInterval, h']

theorem upper_succ_right {u : Nat -> alpha} {B : alpha} {n : Nat}
    (h :
      HasTermAbove F u
        (midpoint F (lower F u B n) (upper F u B n))) :
    upper F u B (n + 1) = upper F u B n := by
  classical
  have h' :
      HasTermAbove F u
        (midpoint F (bisectInterval F u B n).fst
          (bisectInterval F u B n).snd) := by
    simpa [lower, upper] using h
  simp [upper, bisectInterval, stepInterval, h']

theorem lower_succ_left {u : Nat -> alpha} {B : alpha} {n : Nat}
    (h :
      Not
        (HasTermAbove F u
          (midpoint F (lower F u B n) (upper F u B n)))) :
    lower F u B (n + 1) = lower F u B n := by
  classical
  have h' :
      Not
        (HasTermAbove F u
          (midpoint F (bisectInterval F u B n).fst
            (bisectInterval F u B n).snd)) := by
    simpa [lower, upper] using h
  simp [lower, bisectInterval, stepInterval, h']

theorem upper_succ_left {u : Nat -> alpha} {B : alpha} {n : Nat}
    (h :
      Not
        (HasTermAbove F u
          (midpoint F (lower F u B n) (upper F u B n)))) :
    upper F u B (n + 1) =
      midpoint F (lower F u B n) (upper F u B n) := by
  classical
  have h' :
      Not
        (HasTermAbove F u
          (midpoint F (bisectInterval F u B n).fst
            (bisectInterval F u B n).snd)) := by
    simpa [lower, upper] using h
  simp [lower, upper, bisectInterval, stepInterval, h']

/-- The bisected interval is genuinely ordered at every stage. Stage zero is
the hypothesis `u 0 <= B` itself, and each further step inherits ordering
from the midpoint lying between the endpoints; monotonicity is not used at
this point. -/
theorem interval_order {u : Nat -> alpha} {B : alpha}
    (_hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B) :
    forall n : Nat, F.le (lower F u B n) (upper F u B n) := by
  intro n
  induction n with
  | zero =>
      rw [lower_zero, upper_zero]
      exact hbdd 0
  | succ n ih =>
      by_cases h :
        HasTermAbove F u
          (midpoint F (lower F u B n) (upper F u B n))
      · rw [lower_succ_right F h, upper_succ_right F h]
        exact midpoint_le_right F ih
      · rw [lower_succ_left F h, upper_succ_left F h]
        exact left_le_midpoint F ih

theorem lower_step_le {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    (n : Nat) :
    F.le (lower F u B n) (lower F u B (n + 1)) := by
  by_cases h :
    HasTermAbove F u
      (midpoint F (lower F u B n) (upper F u B n))
  · rw [lower_succ_right F h]
    exact left_le_midpoint F (interval_order F hmono hbdd n)
  · rw [lower_succ_left F h]
    exact F.le_refl (lower F u B n)

theorem upper_step_le {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    (n : Nat) :
    F.le (upper F u B (n + 1)) (upper F u B n) := by
  by_cases h :
    HasTermAbove F u
      (midpoint F (lower F u B n) (upper F u B n))
  · rw [upper_succ_right F h]
    exact F.le_refl (upper F u B n)
  · rw [upper_succ_left F h]
    exact midpoint_le_right F (interval_order F hmono hbdd n)

/-- The left endpoints increase with the stage, one monotonicity clause of
nesting, by induction along `n <= m` from the one-step behaviour of
bisection. -/
theorem lower_mono {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    {n m : Nat} (hnm : n <= m) :
    F.le (lower F u B n) (lower F u B m) := by
  induction hnm with
  | refl =>
      exact F.le_refl (lower F u B n)
  | step h ih =>
      exact F.le_trans ih (lower_step_le F hmono hbdd _)

/-- The right endpoints decrease with the stage, the other monotonicity
clause of nesting, by the same induction. -/
theorem upper_antitone {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    {n m : Nat} (hnm : n <= m) :
    F.le (upper F u B m) (upper F u B n) := by
  induction hnm with
  | refl =>
      exact F.le_refl (upper F u B n)
  | step h ih =>
      exact F.le_trans (upper_step_le F hmono hbdd _) ih

/-- For each stage `k` there is a threshold beyond which every term of `u`
lies in the stage-`k` interval. In the right-half branch the term above the
midpoint drags all later terms above the new left endpoint, by
monotonicity; in the left-half branch no term ever rises above the
midpoint, so the midpoint itself bounds the tail above. -/
theorem tail_in_interval {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B) :
    forall k : Nat,
      Exists
        (fun N : Nat =>
          forall n : Nat,
            N <= n ->
              And
                (F.le (lower F u B k) (u n))
                (F.le (u n) (upper F u B k))) := by
  intro k
  induction k with
  | zero =>
      refine Exists.intro 0 ?_
      intro n hn
      constructor
      · rw [lower_zero]
        exact hmono 0 n hn
      · rw [upper_zero]
        exact hbdd n
  | succ k ih =>
      cases ih with
      | intro N hN =>
          by_cases h :
            HasTermAbove F u
              (midpoint F (lower F u B k) (upper F u B k))
          · cases h with
            | intro M hM =>
                refine Exists.intro (Nat.max N M) ?_
                intro n hn
                have hNn : N <= n :=
                  Nat.le_trans (Nat.le_max_left N M) hn
                have hMn : M <= n :=
                  Nat.le_trans (Nat.le_max_right N M) hn
                constructor
                · rw [lower_succ_right F (Exists.intro M hM)]
                  exact F.le_trans (le_of_lt F hM)
                    (hmono M n hMn)
                · rw [upper_succ_right F (Exists.intro M hM)]
                  exact (hN n hNn).right
          · refine Exists.intro N ?_
            intro n hn
            constructor
            · rw [lower_succ_left F h]
              exact (hN n hn).left
            · rw [upper_succ_left F h]
              apply le_of_not_lt F
              intro hmn
              exact h (Exists.intro n hmn)

/-- The width of the stage-`n` bisected interval. -/
noncomputable def length (u : Nat -> alpha) (B : alpha) (n : Nat) : alpha :=
  F.sub (upper F u B n) (lower F u B n)

theorem length_zero (u : Nat -> alpha) (B : alpha) :
    length F u B 0 = F.sub B (u 0) := by
  unfold length
  rw [lower_zero, upper_zero]

/-- Each bisection step halves the width, whichever half is kept. -/
theorem length_succ {u : Nat -> alpha} {B : alpha}
    (_hmono : F.MonotoneIncreasing u)
    (_hbdd : IsUpperBoundSeq F u B)
    (n : Nat) :
    length F u B (n + 1) =
      half F (length F u B n) := by
  unfold length
  by_cases h :
    HasTermAbove F u
      (midpoint F (lower F u B n) (upper F u B n))
  · rw [lower_succ_right F h, upper_succ_right F h]
    exact right_sub_midpoint F (lower F u B n) (upper F u B n)
  · rw [lower_succ_left F h, upper_succ_left F h]
    exact midpoint_sub_left F (lower F u B n) (upper F u B n)

/-- The closed form after `n` steps: the width is the initial width
`B - u 0` divided by the `n`-th dyadic unit. The powers of two enter the
edge here, which is why its Archimedean price is stated dyadically. -/
theorem length_formula {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    (n : Nat) :
    length F u B n =
      F.mul (F.sub B (u 0)) (F.inv (dyadic F n)) := by
  induction n with
  | zero =>
      rw [length_zero, dyadic_zero, inv_one F, F.mul_one]
  | succ n ih =>
      rw [length_succ F hmono hbdd n, ih]
      unfold half
      rw [dyadic_succ]
      have hdne : Not (dyadic F n = F.zero) :=
        dyadic_ne_zero F n
      have htwo_ne : Not (two F = F.zero) :=
        two_ne_zero F
      rw [inv_mul F hdne htwo_ne]
      calc
        F.mul (F.mul (F.sub B (u 0)) (F.inv (dyadic F n)))
            (F.inv (two F)) =
            F.mul (F.sub B (u 0))
              (F.mul (F.inv (dyadic F n)) (F.inv (two F))) := by
              rw [F.mul_assoc]
        _ = F.mul (F.sub B (u 0))
              (F.mul (F.inv (two F)) (F.inv (dyadic F n))) := by
              rw [F.mul_comm (F.inv (dyadic F n)) (F.inv (two F))]

/-- The bisected endpoints form a nested family of closed intervals, the
first of the two inputs the nested node is applied to. -/
theorem nested_intervals {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B) :
    F.NestedClosedIntervals (lower F u B) (upper F u B) := by
  constructor
  · exact interval_order F hmono hbdd
  · constructor
    · intro n m hnm
      exact lower_mono F hmono hbdd hnm
    · intro n m hnm
      exact upper_antitone F hmono hbdd hnm

/-- Under the dyadic Archimedean principle the widths tend to zero: widths
only shrink as stages advance, and the closed form leaves them a fixed
multiple of the reciprocal of a dyadic unit, which that principle forces
below any given bound. This is the single place where the edge's extra
hypothesis enters. -/
theorem length_tendsto_zero {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    (hdyadic : F.DyadicArchimedeanPrinciple) :
    F.IntervalLengthsToZero (lower F u B) (upper F u B) := by
  intro eps heps
  let L := F.sub B (u 0)
  have hL_nonneg : F.le F.zero L :=
    sub_nonneg_of_le F (hbdd 0)
  cases hdyadic.small_mul_inv hL_nonneg heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hlen_le :
          F.le (length F u B n) (length F u B N) := by
        unfold length
        exact sub_le_sub_of_le_of_le F
          (upper_antitone F hmono hbdd hn)
          (lower_mono F hmono hbdd hn)
      have hlenN :
          F.lt (length F u B N) eps := by
        rwa [length_formula F hmono hbdd N]
      have hlen_lt : F.lt (length F u B n) eps :=
        lt_of_le_of_lt F hlen_le hlenN
      have hlen_nonneg : F.le F.zero (length F u B n) := by
        unfold length
        exact sub_nonneg_of_le F (interval_order F hmono hbdd n)
      change
        F.lt (abs F (F.sub (length F u B n) F.zero)) eps
      rwa [sub_zero F (length F u B n),
        abs_of_nonneg F hlen_nonneg]

theorem interval_points_close {a b x y eps : alpha}
    (hx : And (F.le a x) (F.le x b))
    (hy : And (F.le a y) (F.le y b))
    (hlen : F.lt (F.sub b a) eps) :
    F.lt (abs F (F.sub x y)) eps :=
  NestedBasic.interval_points_close F hx hy hlen

/-- Any point common to all the bisected intervals is the limit of `u`:
past a stage-dependent threshold the terms and the point share an interval
of width below `eps`. Unlike in the Cauchy setting the tail threshold
depends on the stage, so the two indices are combined with a maximum. -/
theorem increasing_tendsto_nested_point {u : Nat -> alpha} {B l : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : IsUpperBoundSeq F u B)
    (hdyadic : F.DyadicArchimedeanPrinciple)
    (hl :
      forall n : Nat,
        And
          (F.le (lower F u B n) l)
          (F.le l (upper F u B n))) :
    F.SeqTendsto u l := by
  intro eps heps
  have hlen := length_tendsto_zero F hmono hbdd hdyadic eps heps
  cases hlen with
  | intro K hK =>
      cases tail_in_interval F hmono hbdd K with
      | intro N hN =>
          refine Exists.intro (Nat.max K N) ?_
          intro n hn
          have hKn : K <= n :=
            Nat.le_trans (Nat.le_max_left K N) hn
          have hNn : N <= n :=
            Nat.le_trans (Nat.le_max_right K N) hn
          have htail := hN n hNn
          have hlenK_close := hK K (Nat.le_refl K)
          have hlenK : F.lt (length F u B K) eps := by
            have hlen_nonneg : F.le F.zero (length F u B K) := by
              unfold length
              exact sub_nonneg_of_le F (interval_order F hmono hbdd K)
            change
              F.lt (abs F (F.sub (length F u B K) F.zero)) eps
              at hlenK_close
            rwa [sub_zero F (length F u B K),
              abs_of_nonneg F hlen_nonneg] at hlenK_close
          exact interval_points_close F htail (hl K) hlenK

/-- A bounded increasing sequence converges, given the nested node and the
dyadic principle: the bisection of `[u 0, B]` produces a nested family with
vanishing widths, the node returns a common point, and that point is the
limit. -/
theorem increasing_converges
    (hnested : F.NestedIntervalPrinciple)
    (hdyadic : F.DyadicArchimedeanPrinciple)
    {u : Nat -> alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : F.SeqBoundedAbove u) :
    Exists (fun l : alpha => F.SeqTendsto u l) := by
  cases hbdd with
  | intro B hB =>
      have hnest : F.NestedClosedIntervals (lower F u B) (upper F u B) :=
        nested_intervals F hmono hB
      have hlen : F.IntervalLengthsToZero (lower F u B) (upper F u B) :=
        length_tendsto_zero F hmono hB hdyadic
      cases hnested.unique_point_of_lengths_zero
          (lower F u B) (upper F u B) hnest hlen with
      | intro l hl =>
          exact Exists.intro l
            (increasing_tendsto_nested_point F hmono hB hdyadic hl.left)

/-- The decreasing case, by negation: the negated sequence is increasing
and bounded above, and negation carries convergence back. The two negation
lemmas are those of `Tautology.RealSequence.Basic`. -/
theorem decreasing_converges
    (hnested : F.NestedIntervalPrinciple)
    (hdyadic : F.DyadicArchimedeanPrinciple)
    {u : Nat -> alpha}
    (hmono : F.MonotoneDecreasing u)
    (hbdd : F.SeqBoundedBelow u) :
    Exists (fun l : alpha => F.SeqTendsto u l) := by
  let v : Nat -> alpha := fun n => F.neg (u n)
  have hvmono : F.MonotoneIncreasing v :=
    FromCauchyMonotone.neg_monotone_increasing_of_decreasing F hmono
  have hvbdd : F.SeqBoundedAbove v :=
    FromCauchyMonotone.neg_boundedAbove_of_boundedBelow F hbdd
  cases increasing_converges F hnested hdyadic hvmono hvbdd with
  | intro L hL =>
      refine Exists.intro (F.neg L) ?_
      have hneg := seqTendsto_neg F hL
      intro eps heps
      apply Eventually.mono ?_ (hneg eps heps)
      intro n hn
      simpa [v, neg_neg F (u n)] using hn

/-- The edge from the nested-interval node to the monotone-convergence
node, with the dyadic Archimedean principle as its price. Bisection turns a
bounded monotone sequence into a nested family whose widths decay
geometrically, and that hypothesis is what makes the decay a null sequence;
it is the only extra assumption the edge needs. -/
theorem monotoneConvergence
    (hnested : F.NestedIntervalPrinciple)
    (hdyadic : F.DyadicArchimedeanPrinciple) :
    F.MonotoneConvergencePrinciple where
  increasing := by
    intro u hmono hbdd
    exact increasing_converges F hnested hdyadic hmono hbdd
  decreasing := by
    intro u hmono hbdd
    exact decreasing_converges F hnested hdyadic hmono hbdd

end FromNestedMonotone
end IsOrderedFieldBaseLike
end Tautology
