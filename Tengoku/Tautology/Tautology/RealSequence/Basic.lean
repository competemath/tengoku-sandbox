import Tengoku.Tautology.Tautology.Nat.Eventually
import Tengoku.Tautology.Tautology.RealBootstrap.Abs
import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra

/-!
# Convergence, Cauchy, monotone, bounded

The vocabulary the whole region runs on, all of it over an arbitrary ordered
field: `SeqTendsto` with thresholds supplied through
`Tautology.Nat.Eventually`, `SeqCauchy` with a single threshold serving both
indices rather than two separate eventual statements, monotonicity in pairwise
form, and boundedness on all indices.

The theorems are the ones available before any completeness is assumed: a
constant sequence converges, a convergent sequence is Cauchy, and step-wise
monotonicity implies the pairwise form. A small `FromCauchyMonotone` namespace
at the end holds the two negation reflections that let the decreasing halves of
later results be read off the increasing ones instead of being proved twice.

## Position and role

Implementation module, the base of `RealSequence` and, through
`Tautology.RealSequence.Principles.Statements`, the ground the completeness
route graph stands on. Neither completeness nor any Archimedean principle
appears here.
-/

namespace Tautology

namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Convergence of a sequence, stated over an arbitrary ordered field: for
every positive tolerance `eps`, `|u n - l| < eps` holds eventually, the
threshold being supplied by `Tautology.Nat.Eventually`. Only ordered-field
algebra enters the predicate; producing limits for it is the business of the
completeness nodes declared in `Tautology.RealSequence.Principles.Statements`.
-/
def SeqTendsto (u : Nat -> alpha) (l : alpha) : Prop :=
  forall eps : alpha,
    F.lt F.zero eps ->
      Eventually
        (fun n : Nat => F.lt (abs F (F.sub (u n) l)) eps)

theorem seqTendsto_const (c : alpha) :
    SeqTendsto F (fun _ : Nat => c) c := by
  intro eps heps
  apply Eventually.of_forall
  intro n
  rw [abs_sub_self F c]
  exact heps

theorem seqTendsto_eventually {u : Nat -> alpha} {l eps : alpha}
    (h : SeqTendsto F u l)
    (heps : F.lt F.zero eps) :
    Eventually
      (fun n : Nat => F.lt (abs F (F.sub (u n) l)) eps) :=
  h eps heps

/-- The Cauchy predicate: past a single threshold `N`, any two terms are
within `eps` of each other. One threshold serves both indices rather than
two eventual statements being intersected, and no candidate limit occurs in
the statement at all. -/
def SeqCauchy (u : Nat -> alpha) : Prop :=
  forall eps : alpha,
    F.lt F.zero eps ->
      Exists
        (fun N : Nat =>
          forall n m : Nat,
            N <= n ->
              N <= m ->
                F.lt (abs F (F.sub (u n) (u m))) eps)

/-- Every convergent sequence is Cauchy. The proof drives both tails to the
common limit at half the tolerance and joins them by the triangle inequality,
so only ordered-field algebra enters. The converse direction is not available
at this level; the library declares it as the `CauchyCriterionPrinciple` node
of `Tautology.RealSequence.Principles.Statements`, to be supplied by a
completeness route. -/
theorem seqCauchy_of_seqTendsto
    {u : Nat -> alpha} {l : alpha}
    (hu : SeqTendsto F u l) :
    SeqCauchy F u := by
  intro eps heps
  let e2 := half F eps
  have he2 : F.lt F.zero e2 :=
    half_pos F heps
  cases hu e2 he2 with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n m hn hm
      have hnclose := hN n hn
      have hmclose := hN m hm
      have hmclose' :
          F.lt (abs F (F.sub l (u m))) e2 := by
        simpa [abs_sub_comm F l (u m)] using hmclose
      have htri :
          F.le (abs F (F.sub (u n) (u m)))
            (F.add
              (abs F (F.sub (u n) l))
              (abs F (F.sub l (u m)))) := by
        have h :=
          abs_add_le_abs_add_abs F
            (F.sub (u n) l) (F.sub l (u m))
        rwa [sub_add_sub_cancel F (u n) l (u m)] at h
      have hsum :
          F.lt
            (F.add
              (abs F (F.sub (u n) l))
              (abs F (F.sub l (u m)))) eps := by
        have h := add_lt_add F hnclose hmclose'
        rwa [half_add_half F eps] at h
      exact lt_of_le_of_lt F htri hsum

/-- Monotonicity in pairwise form: `n <= m` implies `u n <= u m`. The
adjacent-step lemma below shows that checking neighbouring indices already
suffices. -/
def MonotoneIncreasing (u : Nat -> alpha) : Prop :=
  forall n m : Nat, n <= m -> F.le (u n) (u m)

/-- Monotonicity in the reverse direction: `n <= m` implies `u m <= u n`.
The mirror of `MonotoneIncreasing`; termwise negation exchanges the two,
which is how the `FromCauchyMonotone` reflections below exploit the
symmetry. -/
def MonotoneDecreasing (u : Nat -> alpha) : Prop :=
  forall n m : Nat, n <= m -> F.le (u m) (u n)

/-- Adjacent-step monotonicity `u n <= u (n + 1)` already gives the pairwise
form. The proof walks the gap `m - n` by induction on a summand, which is
why consumers may verify monotonicity one step at a time. -/
theorem monotoneIncreasing_of_step
    {u : Nat -> alpha}
    (hstep : forall n : Nat, F.le (u n) (u (n + 1))) :
    MonotoneIncreasing F u := by
  intro n m hnm
  have htail :
      forall k : Nat, F.le (u n) (u (n + k)) := by
    intro k
    induction k with
    | zero =>
        rw [Nat.add_zero]
        exact F.le_refl (u n)
    | succ k ih =>
        have hnext : F.le (u (n + k)) (u ((n + k) + 1)) :=
          hstep (n + k)
        have htarget :
            n + (k + 1) = (n + k) + 1 := by
          omega
        rw [htarget]
        exact F.le_trans ih hnext
  have hm : n + (m - n) = m := by
    omega
  simpa [hm] using htail (m - n)

/-- The decreasing mirror: adjacent steps `u (n + 1) <= u n` give pairwise
monotonicity by the same induction along the gap. -/
theorem monotoneDecreasing_of_step
    {u : Nat -> alpha}
    (hstep : forall n : Nat, F.le (u (n + 1)) (u n)) :
    MonotoneDecreasing F u := by
  intro n m hnm
  have htail :
      forall k : Nat, F.le (u (n + k)) (u n) := by
    intro k
    induction k with
    | zero =>
        rw [Nat.add_zero]
        exact F.le_refl (u n)
    | succ k ih =>
        have hnext : F.le (u ((n + k) + 1)) (u (n + k)) :=
          hstep (n + k)
        have htarget :
            n + (k + 1) = (n + k) + 1 := by
          omega
        rw [htarget]
        exact F.le_trans hnext ih
  have hm : n + (m - n) = m := by
    omega
  simpa [hm] using htail (m - n)

/-- Boundedness above by a single bound, demanded of every index without
exception. The all-index strength is what the monotone convergence nodes
take as hypothesis; the eventual, two-sided variant lives in
`Tautology.RealSequence.Bounded` as `EventuallyBounded`. -/
def SeqBoundedAbove (u : Nat -> alpha) : Prop :=
  Exists (fun B : alpha => forall n : Nat, F.le (u n) B)

/-- Boundedness below by a single bound, again at every index. Together with
`MonotoneDecreasing` this is the hypothesis side of the decreasing half of
the monotone convergence node. -/
def SeqBoundedBelow (u : Nat -> alpha) : Prop :=
  Exists (fun B : alpha => forall n : Nat, F.le B (u n))

namespace FromCauchyMonotone

/-- Termwise negation turns a decreasing sequence into an increasing one.
The namespace records the customer: the entries and edges of the principles
graph derive the decreasing halves of their nodes from the increasing halves
through this reflection. -/
theorem neg_monotone_increasing_of_decreasing {u : Nat -> alpha}
    (hmono : F.MonotoneDecreasing u) :
    F.MonotoneIncreasing (fun n : Nat => F.neg (u n)) := by
  intro n m hnm
  exact neg_le_neg F (hmono n m hnm)

/-- Boundedness below negates into boundedness above, bound and terms
together. The companion reflection, completing the reduction of the
decreasing monotone convergence node to the increasing one. -/
theorem neg_boundedAbove_of_boundedBelow {u : Nat -> alpha}
    (hbdd : F.SeqBoundedBelow u) :
    F.SeqBoundedAbove (fun n : Nat => F.neg (u n)) := by
  cases hbdd with
  | intro B hB =>
      refine Exists.intro (F.neg B) ?_
      intro n
      exact neg_le_neg F (hB n)

end FromCauchyMonotone

end IsOrderedFieldBaseLike
end Tautology
