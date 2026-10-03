import Tengoku.Tautology.Tautology.Foundation.Cardinal.Pairing
import Tengoku.Tautology.Tautology.RealBootstrap.FiniteSum
import Tengoku.Tautology.Tautology.RealSequence.Algebra
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Partial sums, dyadic budgets, and diagonal flattening

Series in the only form this library needs them: finite partial sums, plus the
two devices that let a countable amount of bookkeeping be controlled by one
positive quantity.

`dyadicBudget eps n` is `eps / 2 ^ (n + 1)`, the share of a budget allotted to
row `n`, whose shares sum to less than the budget. `diagonalFlatten` turns a
family indexed by two naturals into a single sequence along Cantor's pairing.
Together they give the estimate that everything countable in this library is
proved with: if each row of a doubly indexed nonnegative family has partial
sums within its dyadic share, then the flattened sequence has all partial sums
below the budget.

That combination is what `Tautology.RealNegligibility.NullSet` uses to prove a
countable union of null sets null, and it is why no theory of convergent series
is needed there -- the conclusion is a bound on every finite partial sum, not a
statement about a limit.

## Position and role

Implementation module over an arbitrary ordered field; completeness plays no
part. Sums of series in the limit sense are stated here too, but the budget
machinery is what the rest of the library consumes.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- A sequence whose terms are all nonnegative. The hypothesis every
monotonicity statement of this module runs on; positivity is never needed,
only nonnegativity. -/
def NonnegativeSeq (u : Nat -> alpha) : Prop :=
  forall n : Nat, F.le F.zero (u n)

/-- The partial sum of the first `n` terms, `u 0` through `u (n - 1)`, built on
`finiteSum` with the empty sum equal to zero. Everything in this module, and
the cover-length budgets of `Tautology.RealNegligibility.NullSet`, are partial
sums of this shape; no series limit is ever taken here. -/
def seriesPartialSum (u : Nat -> alpha) (n : Nat) : alpha :=
  finiteSum F u n

theorem seriesPartialSum_zero (u : Nat -> alpha) :
    seriesPartialSum F u 0 = F.zero :=
  finiteSum_zero F u

theorem seriesPartialSum_succ (u : Nat -> alpha) (n : Nat) :
    seriesPartialSum F u (n + 1) =
      F.add (seriesPartialSum F u n) (u n) :=
  finiteSum_succ F u n

/-- The nonnegative series sums to `s`: its partial-sum sequence converges
to `s`. Convergence of this one sequence is the only limiting notion of
series summation the library has. -/
def PositiveSeriesHasSum (u : Nat -> alpha) (s : alpha) : Prop :=
  SeqTendsto F (seriesPartialSum F u) s

/-- The series has some sum. Kept existential, so consumers that need only
existence never name the sum. -/
def PositiveSeriesSummable (u : Nat -> alpha) : Prop :=
  Exists (fun s : alpha => PositiveSeriesHasSum F u s)

theorem positiveSeriesHasSum_unique
    {u : Nat -> alpha} {s t : alpha}
    (hs : PositiveSeriesHasSum F u s)
    (ht : PositiveSeriesHasSum F u t) :
    s = t :=
  seqTendsto_unique F hs ht

theorem seriesPartialSum_nonneg
    {u : Nat -> alpha}
    (hu : NonnegativeSeq F u) :
    forall n : Nat, F.le F.zero (seriesPartialSum F u n)
  | 0 => by
      rw [seriesPartialSum_zero]
      exact F.le_refl F.zero
  | n + 1 => by
      rw [seriesPartialSum_succ]
      have ih : F.le F.zero (seriesPartialSum F u n) :=
        seriesPartialSum_nonneg hu n
      have hlast : F.le F.zero (u n) := hu n
      have hsum :
          F.le (F.add F.zero F.zero)
            (F.add (seriesPartialSum F u n) (u n)) :=
        add_le_add F ih hlast
      rwa [F.zero_add] at hsum

theorem seriesPartialSum_step_le
    {u : Nat -> alpha}
    (hu : NonnegativeSeq F u)
    (n : Nat) :
    F.le (seriesPartialSum F u n) (seriesPartialSum F u (n + 1)) := by
  rw [seriesPartialSum_succ]
  have h := add_le_add_left F (hu n) (seriesPartialSum F u n)
  rwa [F.add_zero] at h

/-- The partial sums of a nonnegative series form a monotone increasing
sequence. This is the bridge through which series statements reach the
monotone convergence node. -/
theorem seriesPartialSum_monotone
    {u : Nat -> alpha}
    (hu : NonnegativeSeq F u) :
    MonotoneIncreasing F (seriesPartialSum F u) :=
  monotoneIncreasing_of_step F (seriesPartialSum_step_le F hu)

/-- Termwise domination of summands gives domination of partial sums at
every length. Comparisons against budgets are therefore made term by term,
never through a supremum. -/
theorem seriesPartialSum_le_of_pointwise_le
    {u v : Nat -> alpha}
    (hle : forall k : Nat, F.le (u k) (v k)) :
    forall n : Nat,
      F.le (seriesPartialSum F u n) (seriesPartialSum F v n)
  | 0 => by
      rw [seriesPartialSum_zero, seriesPartialSum_zero]
      exact F.le_refl F.zero
  | n + 1 => by
      rw [seriesPartialSum_succ, seriesPartialSum_succ]
      exact add_le_add F
        (seriesPartialSum_le_of_pointwise_le hle n)
        (hle n)

/-- A nonnegative series with bounded-above partial sums is summable -- given
the monotone convergence principle as an explicit hypothesis. The node rides on
the theorem instead of being imported: over a bare ordered field the statement
need not hold, and the consumer, the integral test of
`Tautology.RealIntegral.Riemann.Improper.Tests.PositiveIntegralTest`, supplies
the node its own route has reached. -/
theorem positiveSeriesSummable_of_seriesPartialSum_boundedAbove
    {u : Nat -> alpha}
    (hmono : MonotoneConvergencePrinciple F)
    (hu : NonnegativeSeq F u)
    (hbdd : SeqBoundedAbove F (seriesPartialSum F u)) :
    PositiveSeriesSummable F u := by
  exact
    hmono.increasing
      (seriesPartialSum F u)
      (seriesPartialSum_monotone F hu)
      hbdd

/-- The converse direction at the level of a named sum: a convergent
partial-sum sequence is bounded above, by the explicit bound `s + 1`. The
tail is bounded by convergence at tolerance one, the head by monotonicity;
no completeness enters, which is why this half stands on its own. -/
theorem seriesPartialSum_boundedAbove_of_positiveSeriesHasSum
    {u : Nat -> alpha} {s : alpha}
    (hu : NonnegativeSeq F u)
    (hs : PositiveSeriesHasSum F u s) :
    SeqBoundedAbove F (seriesPartialSum F u) := by
  let B := F.add s F.one
  have hmono : MonotoneIncreasing F (seriesPartialSum F u) :=
    seriesPartialSum_monotone F hu
  have hclose :
      Eventually
        (fun n : Nat =>
          F.lt
            (F.abs (F.sub (seriesPartialSum F u n) s)) F.one) :=
    hs F.one (zero_lt_one F)
  have hevent :
      Eventually
        (fun n : Nat => F.le (seriesPartialSum F u n) B) := by
    apply Eventually.mono ?_ hclose
    intro n hn
    dsimp [B]
    exact le_of_lt F (abs_sub_lt_right F hn)
  cases hevent with
  | intro N hN =>
      refine Exists.intro B ?_
      intro n
      cases Nat.le_total n N with
      | inl hnN =>
          exact F.le_trans (hmono n N hnN) (hN N (Nat.le_refl N))
      | inr hNn =>
          exact hN n hNn

/-- Existential packaging of the preceding bound: summability alone gives
boundedness above of the partial sums. Together with
`positiveSeriesSummable_of_seriesPartialSum_boundedAbove`, and modulo the
monotone convergence node, this makes summability and boundedness
equivalent. -/
theorem seriesPartialSum_boundedAbove_of_positiveSeriesSummable
    {u : Nat -> alpha}
    (hu : NonnegativeSeq F u)
    (hsum : PositiveSeriesSummable F u) :
    SeqBoundedAbove F (seriesPartialSum F u) := by
  cases hsum with
  | intro s hs =>
      exact seriesPartialSum_boundedAbove_of_positiveSeriesHasSum F hu hs

/-- The running remainder of the dyadic split: `eps` halved `n` times. The
tail left over after the first `n` row budgets have been spent. -/
def dyadicTail (eps : alpha) : Nat -> alpha
  | 0 => eps
  | n + 1 => half F (dyadicTail eps n)

/-- The row budgets of the dyadic split of `eps`: row `n` receives
`eps / 2 ^ (n + 1)`, one halving beyond the tail. The partial sums of this
sequence stay strictly below `eps` at every length
(`seriesPartialSum_dyadicBudget_lt`), which is what countable-union covers
charge their lengths against in `Tautology.RealNegligibility.NullSet`. -/
def dyadicBudget (eps : alpha) (n : Nat) : alpha :=
  dyadicTail F eps (n + 1)

theorem dyadicTail_zero (eps : alpha) :
    dyadicTail F eps 0 = eps := rfl

theorem dyadicTail_succ (eps : alpha) (n : Nat) :
    dyadicTail F eps (n + 1) = half F (dyadicTail F eps n) := rfl

theorem dyadicBudget_eq_tail_succ (eps : alpha) (n : Nat) :
    dyadicBudget F eps n = dyadicTail F eps (n + 1) := rfl

theorem dyadicTail_nonnegative {eps : alpha}
    (heps : F.le F.zero eps) :
    forall n : Nat, F.le F.zero (dyadicTail F eps n)
  | 0 => by
      rwa [dyadicTail_zero]
  | n + 1 => by
      rw [dyadicTail_succ]
      exact half_nonneg F (dyadicTail_nonnegative heps n)

theorem dyadicBudget_nonnegative {eps : alpha}
    (heps : F.le F.zero eps) :
    NonnegativeSeq F (dyadicBudget F eps) := by
  intro n
  unfold dyadicBudget
  exact dyadicTail_nonnegative F heps (n + 1)

theorem dyadicTail_pos {eps : alpha}
    (heps : F.lt F.zero eps) :
    forall n : Nat, F.lt F.zero (dyadicTail F eps n)
  | 0 => by
      rwa [dyadicTail_zero]
  | n + 1 => by
      rw [dyadicTail_succ]
      exact half_pos F (dyadicTail_pos heps n)

/-- Every row budget is strictly positive whenever `eps` is. The sign
hypothesis a cover argument needs before it can spend any budget at all. -/
theorem dyadicBudget_pos {eps : alpha}
    (heps : F.lt F.zero eps) :
    forall n : Nat, F.lt F.zero (dyadicBudget F eps n) := by
  intro n
  unfold dyadicBudget
  exact dyadicTail_pos F heps (n + 1)

/-- Exact telescoping: the partial sums of the dyadic budget plus the
running tail rebuild `eps` identically, at every length. The identity is
exact rather than an estimate, which is what makes the strict inequality
below available uniformly. -/
theorem seriesPartialSum_dyadicBudget_add_tail (eps : alpha) :
    forall n : Nat,
      F.add
        (seriesPartialSum F (dyadicBudget F eps) n)
        (dyadicTail F eps n) =
      eps
  | 0 => by
      rw [seriesPartialSum_zero, dyadicTail_zero, F.zero_add]
  | n + 1 => by
      calc
        F.add
            (seriesPartialSum F (dyadicBudget F eps) (n + 1))
            (dyadicTail F eps (n + 1)) =
            F.add
              (F.add
                (seriesPartialSum F (dyadicBudget F eps) n)
                (dyadicBudget F eps n))
              (dyadicTail F eps (n + 1)) := by
              rw [seriesPartialSum_succ]
        _ =
            F.add
              (seriesPartialSum F (dyadicBudget F eps) n)
              (F.add
                (dyadicTail F eps (n + 1))
                (dyadicTail F eps (n + 1))) := by
              rw [F.add_assoc]
              rw [dyadicBudget_eq_tail_succ]
        _ =
            F.add
              (seriesPartialSum F (dyadicBudget F eps) n)
              (dyadicTail F eps n) := by
              rw [dyadicTail_succ, half_add_half]
        _ = eps :=
            seriesPartialSum_dyadicBudget_add_tail eps n

/-- The dyadic budget is never fully spent: every partial sum stays strictly
below `eps`, the positive tail always remaining. The bound is uniform in
`n`, so no convergence of the budget series is ever invoked. -/
theorem seriesPartialSum_dyadicBudget_lt {eps : alpha}
    (heps : F.lt F.zero eps) :
    forall n : Nat,
      F.lt (seriesPartialSum F (dyadicBudget F eps) n) eps := by
  intro n
  have htail : F.lt F.zero (dyadicTail F eps n) :=
    dyadicTail_pos F heps n
  have hlt :=
    add_lt_add_left F htail
      (seriesPartialSum F (dyadicBudget F eps) n)
  change
    F.lt
      (F.add (seriesPartialSum F (dyadicBudget F eps) n) F.zero)
      (F.add
        (seriesPartialSum F (dyadicBudget F eps) n)
        (dyadicTail F eps n)) at hlt
  rw [F.add_zero] at hlt
  rwa [seriesPartialSum_dyadicBudget_add_tail F eps n] at hlt

/-- A doubly-indexed family read as one sequence, by walking the diagonal
enumeration `diagonalEnum` of `Tautology.Foundation.Cardinal.Pairing`: the flat
term at `m` is `term i j`, where `(i, j)` is the pair `m` decodes to. This is
the device that turns a countable family of covers into a single `Nat`-indexed
one. -/
def diagonalFlatten (term : Nat -> Nat -> alpha) (m : Nat) : alpha :=
  let p := Foundation.Cardinal.diagonalEnum m
  term p.fst p.snd

/-- The flattening inverts at the diagonal corners: the flat index
`triangular (i + j) + j` carries exactly the pair `(i, j)`. This is how a
member of the doubly-indexed family is located inside the flattened
enumeration. -/
theorem diagonalFlatten_triangular_add
    (term : Nat -> Nat -> alpha) (i j : Nat) :
    diagonalFlatten term
      (Foundation.Cardinal.triangular (i + j) + j) =
      term i j := by
  unfold diagonalFlatten
  have hjle : j <= i + j := by omega
  have hdiag :=
    Foundation.Cardinal.diagonalEnum_tri_add (i + j) j hjle
  rw [hdiag]
  have hfirst : i + j - j = i := by omega
  rw [hfirst]

theorem diagonalFlatten_nonnegative
    {term : Nat -> Nat -> alpha}
    (hterm : forall i j : Nat, F.le F.zero (term i j)) :
    NonnegativeSeq F (diagonalFlatten term) := by
  intro m
  unfold diagonalFlatten
  cases Foundation.Cardinal.diagonalEnum m with
  | mk i j =>
      exact hterm i j

/-- The sum along the `s`-th anti-diagonal, the block of entries with
`i + j = s`, walked with the first index increasing. One flat block of the
flattening, as a standalone quantity. -/
def diagonalRowBlockSum (term : Nat -> Nat -> alpha) (s : Nat) : alpha :=
  finiteSum F (fun i : Nat => term i (s - i)) (s + 1)

/-- A block of the flattened sequence, from `triangular s` up to
`triangular (s + 1)`, sums to the `s`-th anti-diagonal sum. The walking
order inside a diagonal runs opposite to the row reading, which is why a
sum reversal appears in the proof. -/
theorem diagonalFlatten_block_sum_eq_rowBlockSum
    (term : Nat -> Nat -> alpha) (s : Nat) :
    finiteSum F
        (fun k : Nat =>
          diagonalFlatten term (Foundation.Cardinal.triangular s + k))
        (s + 1) =
      diagonalRowBlockSum F term s := by
  unfold diagonalRowBlockSum
  calc
    finiteSum F
        (fun k : Nat =>
          diagonalFlatten term (Foundation.Cardinal.triangular s + k))
        (s + 1) =
        finiteSum F (fun k : Nat => term (s - k) k) (s + 1) := by
        apply finiteSum_congr_lt F
        intro k hk
        unfold diagonalFlatten
        have hk_le : k <= s := by omega
        have hdiag := Foundation.Cardinal.diagonalEnum_tri_add s k hk_le
        rw [hdiag]
    _ =
        finiteSum F (fun i : Nat => term i (s - i)) (s + 1) := by
        rw [finiteSum_reverse F (fun k : Nat => term (s - k) k) s]
        apply finiteSum_congr_lt F
        intro i hi
        have hidx : s - (s - i) = i := by omega
        rw [hidx]

/-- Completed prefixes decompose blockwise: the partial sum of the flattened
sequence at the triangular number `triangular s` equals the sum of the
first `s` anti-diagonals. This is the rearrangement step of the whole
budget argument. -/
theorem diagonalFlatten_completed_sum_eq_rowBlocks
    (term : Nat -> Nat -> alpha) :
    forall s : Nat,
      seriesPartialSum F (diagonalFlatten term)
          (Foundation.Cardinal.triangular s) =
        seriesPartialSum F (diagonalRowBlockSum F term) s
  | 0 => by
      rw [Foundation.Cardinal.triangular]
      rw [seriesPartialSum_zero, seriesPartialSum_zero]
  | s + 1 => by
      have htri :
          Foundation.Cardinal.triangular (s + 1) =
            Foundation.Cardinal.triangular s + (s + 1) := by
        rw [Foundation.Cardinal.triangular_succ]
        omega
      unfold seriesPartialSum
      rw [htri]
      rw [finiteSum_add_length]
      have ih := diagonalFlatten_completed_sum_eq_rowBlocks term s
      unfold seriesPartialSum at ih
      rw [ih]
      rw [diagonalFlatten_block_sum_eq_rowBlockSum]
      rw [finiteSum_succ]

/-- Each anti-diagonal sum regroups into row prefixes: the `s`-th block
equals the sum over rows `i` of the first `s - i` entries of row `i`. Pure
finite-sum bookkeeping (`finiteSum_triangle_swap`), turning diagonal
blocks into the row shape the budget hypothesis is stated in. -/
theorem diagonalRowBlocks_eq_rowPrefixes
    (term : Nat -> Nat -> alpha) :
    forall s : Nat,
      seriesPartialSum F (diagonalRowBlockSum F term) s =
        finiteSum F
          (fun i : Nat => seriesPartialSum F (term i) (s - i))
          s
  | 0 => by
      rw [seriesPartialSum_zero, finiteSum_zero]
  | n + 1 => by
      unfold seriesPartialSum diagonalRowBlockSum
      change
        finiteSum F
            (fun i : Nat =>
              finiteSum F (fun j : Nat => term j (i - j)) (i + 1))
            (n + 1) =
          finiteSum F
            (fun i : Nat => finiteSum F (term i) (n + 1 - i))
            (n + 1)
      rw [finiteSum_triangle_swap F
        (fun i j : Nat => term j (i - j)) n]
      apply finiteSum_congr_lt F
      intro j hj
      apply finiteSum_congr_lt F
      intro h hh
      have hidx : j + h - j = h := by omega
      rw [hidx]

/-- If each row's partial sums are bounded by that row's budget, then each
completed block sum is bounded by the corresponding partial sum of the
budget sequence. -/
theorem diagonalRowBlocks_le_rowBudget
    {term : Nat -> Nat -> alpha} {budget : Nat -> alpha}
    (hrow :
      forall i n : Nat,
        F.le (seriesPartialSum F (term i) n) (budget i)) :
    forall s : Nat,
      F.le
        (seriesPartialSum F (diagonalRowBlockSum F term) s)
        (seriesPartialSum F budget s) := by
  intro s
  rw [diagonalRowBlocks_eq_rowPrefixes]
  exact seriesPartialSum_le_of_pointwise_le F
    (fun i => hrow i (s - i)) s

/-- Combining the block decomposition with the row-bound comparison:
completed prefixes of the flattened series are bounded by partial sums of
the budget sequence. -/
theorem diagonalFlatten_completed_sum_le_rowBudget
    {term : Nat -> Nat -> alpha} {budget : Nat -> alpha}
    (hrow :
      forall i n : Nat,
        F.le (seriesPartialSum F (term i) n) (budget i)) :
    forall s : Nat,
      F.le
        (seriesPartialSum F (diagonalFlatten term)
          (Foundation.Cardinal.triangular s))
        (seriesPartialSum F budget s) := by
  intro s
  rw [diagonalFlatten_completed_sum_eq_rowBlocks]
  exact diagonalRowBlocks_le_rowBudget F hrow s

/-- Every index sits at or below the next triangular boundary. This
two-line arithmetic fact is what pushes an arbitrary prefix up to a
completed one in the final estimate, so that monotonicity alone, with no
rearrangement of partial blocks, closes the argument. -/
theorem le_triangular_succ (n : Nat) :
    n <= Foundation.Cardinal.triangular (n + 1) := by
  induction n with
  | zero =>
      rw [Foundation.Cardinal.triangular_succ]
      omega
  | succ n ih =>
      rw [Foundation.Cardinal.triangular_succ]
      omega

/-- The countable-union budget device: if a nonnegative doubly-indexed
family has each row's partial sums bounded by its dyadic budget
`eps / 2 ^ (i + 1)`, then every partial sum of the diagonal-flattened
single series stays strictly below `eps`. No convergence, limit or
supremum appears -- the bound holds at every `N` -- which is exactly the
shape the null-set cover definition of `Tautology.RealNegligibility.NullSet`
consumes. -/
theorem diagonalFlatten_dyadicBudget_lt
    {term : Nat -> Nat -> alpha} {eps : alpha}
    (hterm : forall i j : Nat, F.le F.zero (term i j))
    (hrow :
      forall i n : Nat,
        F.le
          (seriesPartialSum F (term i) n)
          (dyadicBudget F eps i))
    (heps : F.lt F.zero eps) :
    forall N : Nat,
      F.lt
        (seriesPartialSum F (diagonalFlatten term) N)
        eps := by
  intro N
  have hflat_nonneg : NonnegativeSeq F (diagonalFlatten term) :=
    diagonalFlatten_nonnegative F hterm
  have hmono :
      MonotoneIncreasing F
        (seriesPartialSum F (diagonalFlatten term)) :=
    seriesPartialSum_monotone F hflat_nonneg
  have hprefix :
      F.le
        (seriesPartialSum F (diagonalFlatten term) N)
        (seriesPartialSum F (diagonalFlatten term)
          (Foundation.Cardinal.triangular (N + 1))) :=
    hmono N (Foundation.Cardinal.triangular (N + 1))
      (le_triangular_succ N)
  have hcompleted :
      F.le
        (seriesPartialSum F (diagonalFlatten term)
          (Foundation.Cardinal.triangular (N + 1)))
        (seriesPartialSum F (dyadicBudget F eps) (N + 1)) :=
    diagonalFlatten_completed_sum_le_rowBudget F hrow (N + 1)
  have hbudget :
      F.lt (seriesPartialSum F (dyadicBudget F eps) (N + 1)) eps :=
    seriesPartialSum_dyadicBudget_lt F heps (N + 1)
  exact lt_of_le_of_lt F (F.le_trans hprefix hcompleted) hbudget

end IsOrderedFieldBaseLike
end Tautology
