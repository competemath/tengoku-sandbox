import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements
import Tengoku.Tautology.Tautology.RealSequence.Principles.Dyadic
import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic

/-!
# Entry: nested intervals give sequential Bolzano-Weierstrass

The entry the selected route actually takes, and the one that keeps the whole
argument at ordered-field level: both forms of completeness it needs -- the
nested-interval principle and a dyadic Archimedean principle -- arrive as
explicit hypotheses rather than being derived here.

Bisection is steered by frequency: of the two halves of an interval, at least
one is visited by the sequence at arbitrarily large indices, and that half is
kept. The endpoints form a nested chain whose lengths are exactly
`(right - left) / 2 ^ n`, the nested-interval principle supplies a common
point, and picking one term per stage gives an increasing index sequence
squeezed onto it. The dyadic hypothesis is used once, to drive those lengths
below any tolerance.

Where do the hypotheses come from? Not from here. At the selected carrier
`Tautology.RealCompactness.ClosedInterval.Selected` feeds in the
nested-interval principle chosen in
`Tautology.RealSequence.Principles.Selected` together with the dyadic principle
derived from completeness -- which is how a choice made in another region
cascades into this one.

One detail, recorded because it is easy to misread: the proof consumes the
`unique_point_of_lengths_zero` field of the principle but only uses its
existence half, so the weaker `exists_point` would have sufficed.

## Position and role

Entry module, exporting `Target`. Consumed by
`Tautology.RealCompactness.ClosedInterval.BolzanoWeierstrass`, by
`Tautology.RealCompactness.ClosedInterval.Routes`, and directly by
`Tautology.RealCompactness.ClosedInterval.Selected`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace FromNestedSequential

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The promise of this entry point, in the form that keeps it at the
ordered-field level: the nested-interval principle and the dyadic
Archimedean principle, both taken as explicit hypotheses, together imply
the sequential Bolzano-Weierstrass node. Neither is derived here, which is
what distinguishes this entry from `FromSupSequential`, where both are
read out of a completeness bundle. -/
def Target : Prop :=
  F.NestedIntervalPrinciple ->
    F.DyadicArchimedeanPrinciple ->
      F.BolzanoWeierstrassSequentialPrinciple

/-- The sequence `u` visits `[left, right]` arbitrarily late: beyond any
stage there is a later term inside. This notion, rather than convergence,
is what steers the bisection below, because at each split at least one
half inherits it from the whole. -/
def FrequentlyInInterval (u : Nat -> alpha) (left right : alpha) : Prop :=
  forall N : Nat,
    Exists
      (fun n : Nat =>
        And (N <= n) (F.ClosedInterval left right (u n)))

theorem eventually_not_of_not_frequently {P : Nat -> Prop}
    (h :
      Not
        (forall N : Nat,
          Exists (fun n : Nat => And (N <= n) (P n)))) :
    Exists (fun N : Nat => forall n : Nat, N <= n -> Not (P n)) := by
  classical
  by_cases hex :
      Exists (fun N : Nat => forall n : Nat, N <= n -> Not (P n))
  · exact hex
  · have hfreq :
        forall N : Nat,
          Exists (fun n : Nat => And (N <= n) (P n)) := by
      intro N
      by_cases hN : Exists (fun n : Nat => And (N <= n) (P n))
      · exact hN
      · have hbad :
            Exists
              (fun N0 : Nat => forall n : Nat, N0 <= n -> Not (P n)) := by
          refine Exists.intro N ?_
          intro n hn hp
          exact hN (Exists.intro n (And.intro hn hp))
        exact False.elim (hex hbad)
    exact False.elim (h hfreq)

/-- The dichotomy the bisection runs on: if `u` visits `[left, right]`
frequently but not `[left, mid]`, then it visits `[mid, right]`
frequently -- any late term of the whole window that misses the left half
has landed in the right one. -/
theorem frequent_right_of_not_frequent_left
    {u : Nat -> alpha} {left right mid : alpha}
    (hfreq : FrequentlyInInterval F u left right)
    (hnot : Not (FrequentlyInInterval F u left mid)) :
    FrequentlyInInterval F u mid right := by
  classical
  cases
      eventually_not_of_not_frequently
        (P := fun n : Nat => F.ClosedInterval left mid (u n))
        hnot with
  | intro N0 hN0 =>
      intro N
      cases hfreq (Nat.max N N0) with
      | intro n hn =>
          have hNn : N <= n :=
            Nat.le_trans (Nat.le_max_left N N0) hn.left
          have hN0n : N0 <= n :=
            Nat.le_trans (Nat.le_max_right N N0) hn.left
          have hnot_left : Not (F.ClosedInterval left mid (u n)) :=
            hN0 n hN0n
          have hnot_le_mid : Not (F.le (u n) mid) := by
            intro hum
            exact hnot_left (And.intro hn.right.left hum)
          have hmid_le : F.le mid (u n) := by
            cases F.le_total mid (u n) with
            | inl h => exact h
            | inr h => exact False.elim (hnot_le_mid h)
          exact Exists.intro n
            (And.intro hNn (And.intro hmid_le hn.right.right))

/-- One bisection step: from the closed interval `I`, keep the left half
when `u` still visits it frequently, and otherwise the right half. The
branch tests a `Prop` under classical choice, hence the noncomputable
marker. -/
noncomputable def stepInterval (u : Nat -> alpha)
    (I : Prod alpha alpha) : Prod alpha alpha := by
  classical
  let a := I.fst
  let b := I.snd
  let m := midpoint F a b
  exact if FrequentlyInInterval F u a m then (a, m) else (m, b)

/-- The bisection run: `bisectInterval n` applies `stepInterval` `n`
times starting from `[left, right]`. -/
noncomputable def bisectInterval (u : Nat -> alpha)
    (left right : alpha) : Nat -> Prod alpha alpha
  | 0 => (left, right)
  | n + 1 => stepInterval F u (bisectInterval u left right n)

/-- The left endpoints of the bisection run; with `upper` it forms the
pair of sequences the nested-interval principle is applied to. -/
noncomputable def lower (u : Nat -> alpha)
    (left right : alpha) (n : Nat) : alpha :=
  (bisectInterval F u left right n).fst

/-- The right endpoints of the bisection run, companion of `lower`. -/
noncomputable def upper (u : Nat -> alpha)
    (left right : alpha) (n : Nat) : alpha :=
  (bisectInterval F u left right n).snd

theorem lower_zero (u : Nat -> alpha) (left right : alpha) :
    lower F u left right 0 = left :=
  rfl

theorem upper_zero (u : Nat -> alpha) (left right : alpha) :
    upper F u left right 0 = right :=
  rfl

theorem lower_succ_left {u : Nat -> alpha} {left right : alpha} {n : Nat}
    (h :
      FrequentlyInInterval F u
        (lower F u left right n)
        (midpoint F (lower F u left right n) (upper F u left right n))) :
    lower F u left right (n + 1) = lower F u left right n := by
  classical
  have h' :
      FrequentlyInInterval F u
        (bisectInterval F u left right n).fst
        (midpoint F (bisectInterval F u left right n).fst
          (bisectInterval F u left right n).snd) := by
    simpa [lower, upper] using h
  simp [lower, bisectInterval, stepInterval, h']

theorem upper_succ_left {u : Nat -> alpha} {left right : alpha} {n : Nat}
    (h :
      FrequentlyInInterval F u
        (lower F u left right n)
        (midpoint F (lower F u left right n) (upper F u left right n))) :
    upper F u left right (n + 1) =
      midpoint F (lower F u left right n) (upper F u left right n) := by
  classical
  have h' :
      FrequentlyInInterval F u
        (bisectInterval F u left right n).fst
        (midpoint F (bisectInterval F u left right n).fst
          (bisectInterval F u left right n).snd) := by
    simpa [lower, upper] using h
  simp [upper, lower, bisectInterval, stepInterval, h']

theorem lower_succ_right {u : Nat -> alpha} {left right : alpha} {n : Nat}
    (h :
      Not
        (FrequentlyInInterval F u
          (lower F u left right n)
          (midpoint F (lower F u left right n) (upper F u left right n)))) :
    lower F u left right (n + 1) =
      midpoint F (lower F u left right n) (upper F u left right n) := by
  classical
  have h' :
      Not
        (FrequentlyInInterval F u
          (bisectInterval F u left right n).fst
          (midpoint F (bisectInterval F u left right n).fst
            (bisectInterval F u left right n).snd)) := by
    simpa [lower, upper] using h
  simp [lower, upper, bisectInterval, stepInterval, h']

theorem upper_succ_right {u : Nat -> alpha} {left right : alpha} {n : Nat}
    (h :
      Not
        (FrequentlyInInterval F u
          (lower F u left right n)
          (midpoint F (lower F u left right n) (upper F u left right n)))) :
    upper F u left right (n + 1) = upper F u left right n := by
  classical
  have h' :
      Not
        (FrequentlyInInterval F u
          (bisectInterval F u left right n).fst
          (midpoint F (bisectInterval F u left right n).fst
            (bisectInterval F u left right n).snd)) := by
    simpa [lower, upper] using h
  simp [upper, bisectInterval, stepInterval, h']

theorem interval_order {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right) :
    forall n : Nat, F.le (lower F u left right n) (upper F u left right n) := by
  intro n
  induction n with
  | zero =>
      rw [lower_zero, upper_zero]
      exact h0
  | succ n ih =>
      by_cases h :
        FrequentlyInInterval F u
          (lower F u left right n)
          (midpoint F (lower F u left right n) (upper F u left right n))
      · rw [lower_succ_left F h, upper_succ_left F h]
        exact left_le_midpoint F ih
      · rw [lower_succ_right F h, upper_succ_right F h]
        exact midpoint_le_right F ih

theorem lower_step_le {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right)
    (n : Nat) :
    F.le (lower F u left right n) (lower F u left right (n + 1)) := by
  by_cases h :
    FrequentlyInInterval F u
      (lower F u left right n)
      (midpoint F (lower F u left right n) (upper F u left right n))
  · rw [lower_succ_left F h]
    exact F.le_refl (lower F u left right n)
  · rw [lower_succ_right F h]
    exact left_le_midpoint F (interval_order F h0 n)

theorem upper_step_le {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right)
    (n : Nat) :
    F.le (upper F u left right (n + 1)) (upper F u left right n) := by
  by_cases h :
    FrequentlyInInterval F u
      (lower F u left right n)
      (midpoint F (lower F u left right n) (upper F u left right n))
  · rw [upper_succ_left F h]
    exact midpoint_le_right F (interval_order F h0 n)
  · rw [upper_succ_right F h]
    exact F.le_refl (upper F u left right n)

theorem lower_mono {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right)
    {n m : Nat} (hnm : n <= m) :
    F.le (lower F u left right n) (lower F u left right m) := by
  exact monotoneIncreasing_of_step F (lower_step_le F h0) n m hnm

theorem upper_antitone {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right)
    {n m : Nat} (hnm : n <= m) :
    F.le (upper F u left right m) (upper F u left right n) := by
  exact monotoneDecreasing_of_step F (upper_step_le F h0) n m hnm

/-- The bisection run is a nested chain of closed intervals, in exactly
the shape `NestedClosedIntervals` demands. Nestedness needs only
`left ≤ right`; which half is kept at each step is immaterial to it. -/
theorem nested_intervals {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right) :
    F.NestedClosedIntervals
      (lower F u left right) (upper F u left right) := by
  constructor
  · exact interval_order F h0
  · constructor
    · intro n m hnm
      exact lower_mono F h0 hnm
    · intro n m hnm
      exact upper_antitone F h0 hnm

/-- The length `upper n - lower n` of the `n`-th bisection stage. That
this halves at every step, and so is eventually below every positive
bound under the dyadic Archimedean hypothesis, is the quantitative half
of the argument. -/
noncomputable def length (u : Nat -> alpha)
    (left right : alpha) (n : Nat) : alpha :=
  F.sub (upper F u left right n) (lower F u left right n)

theorem length_zero (u : Nat -> alpha) (left right : alpha) :
    length F u left right 0 = F.sub right left := by
  unfold length
  rw [lower_zero, upper_zero]

theorem length_succ {u : Nat -> alpha} {left right : alpha}
    (n : Nat) :
    length F u left right (n + 1) =
      half F (length F u left right n) := by
  unfold length
  by_cases h :
    FrequentlyInInterval F u
      (lower F u left right n)
      (midpoint F (lower F u left right n) (upper F u left right n))
  · rw [lower_succ_left F h, upper_succ_left F h]
    exact midpoint_sub_left F (lower F u left right n) (upper F u left right n)
  · rw [lower_succ_right F h, upper_succ_right F h]
    exact right_sub_midpoint F (lower F u left right n) (upper F u left right n)

/-- The closed form of the stage lengths: after `n` halvings the stage has
length exactly `(right - left) / 2^n`, `dyadic n` being `2^n`. No estimate
is lost along the run, because every step halves exactly. -/
theorem length_formula {u : Nat -> alpha} {left right : alpha}
    (n : Nat) :
    length F u left right n =
      F.mul (F.sub right left) (F.inv (dyadic F n)) := by
  induction n with
  | zero =>
      rw [length_zero, dyadic_zero, inv_one F, F.mul_one]
  | succ n ih =>
      rw [length_succ F n, ih]
      unfold half
      rw [dyadic_succ]
      have hdne : Not (dyadic F n = F.zero) :=
        dyadic_ne_zero F n
      have htwo_ne : Not (two F = F.zero) :=
        two_ne_zero F
      rw [inv_mul F hdne htwo_ne]
      calc
        F.mul (F.mul (F.sub right left) (F.inv (dyadic F n)))
            (F.inv (two F)) =
            F.mul (F.sub right left)
              (F.mul (F.inv (dyadic F n)) (F.inv (two F))) := by
              rw [F.mul_assoc]
        _ = F.mul (F.sub right left)
              (F.mul (F.inv (two F)) (F.inv (dyadic F n))) := by
              rw [F.mul_comm (F.inv (dyadic F n)) (F.inv (two F))]

/-- The stage lengths tend to zero. This is the only place the dyadic
Archimedean hypothesis enters: it makes the nonnegative quantity
`L / 2^n` eventually smaller than any positive bound, and monotone
endpoints carry the estimate from the threshold stage to all later
ones. -/
theorem length_tendsto_zero {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right)
    (hdyadic : F.DyadicArchimedeanPrinciple) :
    F.IntervalLengthsToZero
      (lower F u left right) (upper F u left right) := by
  intro eps heps
  let L := F.sub right left
  have hL_nonneg : F.le F.zero L :=
    sub_nonneg_of_le F h0
  cases hdyadic.small_mul_inv hL_nonneg heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hlen_le :
          F.le (length F u left right n) (length F u left right N) := by
        unfold length
        exact sub_le_sub_of_le_of_le F
          (upper_antitone F h0 hn)
          (lower_mono F h0 hn)
      have hlenN :
          F.lt (length F u left right N) eps := by
        rwa [length_formula F N]
      have hlen_lt : F.lt (length F u left right n) eps :=
        lt_of_le_of_lt F hlen_le hlenN
      have hlen_nonneg :
          F.le F.zero (length F u left right n) := by
        unfold length
        exact sub_nonneg_of_le F (interval_order F h0 n)
      change
        F.lt (abs F (F.sub (length F u left right n) F.zero)) eps
      rwa [sub_zero F (length F u left right n),
        abs_of_nonneg F hlen_nonneg]

theorem seqBounded_order {u : Nat -> alpha} {left right : alpha}
    (hbounds :
      forall n : Nat,
        And (F.le left (u n)) (F.le (u n) right)) :
    F.le left right :=
  F.le_trans (hbounds 0).left (hbounds 0).right

/-- The subsequence extracted from the invariant: stage `k` picks, by
classical choice, a term at or beyond one past the previous stage's pick
that lies in stage `k`'s interval. The one-past threshold makes the index
function strictly increasing. -/
noncomputable def chosenIndex {u : Nat -> alpha} {left right : alpha}
    (hfreq :
      forall k : Nat,
        FrequentlyInInterval F u
          (lower F u left right k) (upper F u left right k)) :
    Nat -> Nat
  | 0 => Classical.choose (hfreq 0 0)
  | k + 1 =>
      Classical.choose
        (hfreq (k + 1) (chosenIndex hfreq k + 1))

theorem chosenIndex_interval {u : Nat -> alpha} {left right : alpha}
    (hfreq :
      forall k : Nat,
        FrequentlyInInterval F u
          (lower F u left right k) (upper F u left right k))
    (k : Nat) :
    F.ClosedInterval
      (lower F u left right k) (upper F u left right k)
      (u (chosenIndex (F := F) hfreq k)) := by
  cases k with
  | zero =>
      exact (Classical.choose_spec (hfreq 0 0)).right
  | succ k =>
      exact
          (Classical.choose_spec
          (hfreq (k + 1)
            (chosenIndex (F := F) hfreq k + 1))).right

theorem chosenIndex_step {u : Nat -> alpha} {left right : alpha}
    (hfreq :
      forall k : Nat,
        FrequentlyInInterval F u
          (lower F u left right k) (upper F u left right k))
    (k : Nat) :
    chosenIndex (F := F) hfreq k <
      chosenIndex (F := F) hfreq (k + 1) := by
  have hle :
      chosenIndex (F := F) hfreq k + 1 <=
        chosenIndex (F := F) hfreq (k + 1) :=
    (Classical.choose_spec
      (hfreq (k + 1)
        (chosenIndex (F := F) hfreq k + 1))).left
  omega

theorem chosenIndex_subsequence {u : Nat -> alpha} {left right : alpha}
    (hfreq :
      forall k : Nat,
        FrequentlyInInterval F u
          (lower F u left right k) (upper F u left right k)) :
    SubsequenceIndex (chosenIndex (F := F) hfreq) :=
  chosenIndex_step F hfreq

/-- Any chosen term at or beyond stage `k` still lies in stage `k`'s
interval, because later stages are nested inside it. This squeeze is what
drives the chosen subsequence towards the common point. -/
theorem chosenIndex_interval_of_le
    {u : Nat -> alpha} {left right : alpha}
    (h0 : F.le left right)
    (hfreq :
      forall k : Nat,
        FrequentlyInInterval F u
          (lower F u left right k) (upper F u left right k))
    {k n : Nat} (hkn : k <= n) :
    F.ClosedInterval
      (lower F u left right k) (upper F u left right k)
      (u (chosenIndex (F := F) hfreq n)) := by
  have hn := chosenIndex_interval F hfreq n
  constructor
  · exact F.le_trans (lower_mono F h0 hkn) hn.left
  · exact F.le_trans hn.right (upper_antitone F h0 hkn)

/-- The chosen subsequence converges to any common point `l` of the
bisection chain: past stage `K` every chosen term lies in stage `K`'s
interval, whose length is below `eps` by `length_tendsto_zero`, and both
endpoints of that stage bound `l`. -/
theorem selected_tendsto_nested_point
    {u : Nat -> alpha} {left right l : alpha}
    (h0 : F.le left right)
    (hfreq :
      forall k : Nat,
        FrequentlyInInterval F u
          (lower F u left right k) (upper F u left right k))
    (hdyadic : F.DyadicArchimedeanPrinciple)
    (hl :
      forall n : Nat,
        And
          (F.le (lower F u left right n) l)
          (F.le l (upper F u left right n))) :
    F.SeqTendsto
      (subsequence u (chosenIndex (F := F) hfreq)) l := by
  intro eps heps
  have hlen :=
    length_tendsto_zero (F := F) (u := u) h0 hdyadic eps heps
  cases hlen with
  | intro K hK =>
      refine Exists.intro K ?_
      intro n hn
      have hselected :
          F.ClosedInterval
            (lower F u left right K) (upper F u left right K)
            (u (chosenIndex (F := F) hfreq n)) :=
        chosenIndex_interval_of_le F h0 hfreq hn
      have hclose := hK K (Nat.le_refl K)
      have hlenK :
          F.lt (length F u left right K) eps := by
        have hlen_nonneg :
            F.le F.zero (length F u left right K) := by
          unfold length
          exact sub_nonneg_of_le F (interval_order F h0 K)
        change
          F.lt (abs F (F.sub (length F u left right K) F.zero)) eps
            at hclose
        rwa [sub_zero F (length F u left right K),
          abs_of_nonneg F hlen_nonneg] at hclose
      exact NestedBasic.interval_points_close F hselected (hl K) hlenK

end FromNestedSequential
end Compactness
end IsOrderedFieldBaseLike
end Tautology
