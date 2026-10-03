import Tengoku.Tautology.Tautology.RealSequence.Basic

/-!
# Every sequence has a monotone subsequence

The peak argument, in full. Call an index a peak when no later term exceeds its
value; either there are infinitely many peaks, and they give a decreasing
subsequence, or past the last one every term is exceeded later, and the rising
construction gives an increasing one. Both branches are built by recursion with
a classical choice at each step.

Everything else in the file is the vocabulary of subsequences: that an index
sequence dominates its own argument, and that convergence transfers along one.
Those are used all over the library; the peak machinery itself has exactly one
consumer.

## Position and role

Implementation module over an arbitrary ordered field. Its single exit is the
monotone-subsequence theorem, which is what makes
`Tautology.RealSequence.Principles.FromMonotoneCauchy` -- the free edge from
monotone convergence to the Cauchy criterion -- cost eight declarations and no
Archimedean hypothesis.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- A subsequence index: strictly increasing in the strong one-step sense
`phi n < phi (n + 1)`. Strictness is what keeps `u (phi n)` a genuine
subsequence, with no repeated terms and the original order preserved,
rather than an arbitrary reindexing. -/
def SubsequenceIndex (phi : Nat -> Nat) : Prop :=
  forall n : Nat, phi n < phi (n + 1)

/-- The subsequence of `u` selected by `phi`, as plain composition. Kept a
bare function so that every statement about it remains a statement about
`u (phi n)`. -/
def subsequence (u : Nat -> alpha) (phi : Nat -> Nat) : Nat -> alpha :=
  fun n : Nat => u (phi n)

/-- A subsequence index is pairwise monotone: `n <= m` gives `phi n <= phi m`,
by induction along the gap. This is the form the order-based consumers
need; the strict step form is the definition. -/
theorem subsequenceIndex_mono {phi : Nat -> Nat}
    (hphi : SubsequenceIndex phi)
    {n m : Nat} (hnm : n <= m) :
    phi n <= phi m := by
  induction hnm with
  | refl =>
      exact Nat.le_refl (phi n)
  | step h ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (hphi _))

/-- A subsequence index dominates the identity: `n <= phi n`. This is the
property that transfers convergence from a sequence to its subsequences. -/
theorem subsequenceIndex_ge_self {phi : Nat -> Nat}
    (hphi : SubsequenceIndex phi)
    (n : Nat) :
    n <= phi n := by
  induction n with
  | zero =>
      exact Nat.zero_le (phi 0)
  | succ n ih =>
      have hstep : phi n < phi (n + 1) :=
        hphi n
      omega

/-- Subsequences of a convergent sequence converge to the same limit. Only
`phi n >= n` enters the proof, so any index function dominating the identity
would do; `SubsequenceIndex` carries more structure than convergence
transfer needs. -/
theorem seqTendsto_of_subsequenceIndex {u : Nat -> alpha} {l : alpha}
    {phi : Nat -> Nat}
    (hu : SeqTendsto F u l)
    (hphi : SubsequenceIndex phi) :
    SeqTendsto F (subsequence u phi) l := by
  intro eps heps
  cases hu eps heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      unfold subsequence
      exact hN (phi n)
        (Nat.le_trans hn (subsequenceIndex_ge_self hphi n))

/-- Index `n` is a peak of `u` when no later term is larger. The monotone
subsequence theorem below runs on the dichotomy this sets up: infinitely
many peaks enumerate a decreasing subsequence, while a tail free of peaks
admits an increasing one. -/
def Peak (u : Nat -> alpha) (n : Nat) : Prop :=
  forall m : Nat, n <= m -> F.le (u m) (u n)

/-- At a non-peak index, some strictly later term is at least as large: the
one-step extraction the increasing branch of the dichotomy repeats. Proved
by classical contradiction, the negated existential being exactly the peak
condition. -/
theorem not_peak_exists_later_above {u : Nat -> alpha} {n : Nat}
    (hn : Not (Peak F u n)) :
    Exists (fun m : Nat => And (n < m) (F.le (u n) (u m))) := by
  classical
  by_cases hex :
      Exists (fun m : Nat => And (n < m) (F.le (u n) (u m)))
  · exact hex
  · have hpeak : Peak F u n := by
      intro m hnm
      by_cases hle : F.le (u m) (u n)
      · exact hle
      · have hforward : F.le (u n) (u m) := by
          cases F.le_total (u n) (u m) with
          | inl h => exact h
          | inr h => exact False.elim (hle h)
        have hlt : n < m := by
          have hne : Not (m = n) := by
            intro hmn
            have hsame : F.le (u m) (u n) := by
              rw [hmn]
              exact F.le_refl (u n)
            exact hle hsame
          omega
        exact False.elim (hex (Exists.intro m (And.intro hlt hforward)))
    exact False.elim (hn hpeak)

/-- If peaks do not occur arbitrarily far out, then none occur past some
`N`. A pure negation shuffle between two eventual shapes, isolated so that
the main theorem reads as a clean case split on the dichotomy. -/
theorem eventually_not_peak_of_not_infinite {u : Nat -> alpha}
    (h :
      Not
        (forall N : Nat,
          Exists (fun n : Nat => And (N <= n) (Peak F u n)))) :
    Exists
      (fun N : Nat =>
        forall n : Nat, N <= n -> Not (Peak F u n)) := by
  classical
  by_cases hex :
      Exists
        (fun N : Nat =>
          forall n : Nat, N <= n -> Not (Peak F u n))
  · exact hex
  · have hinf :
        forall N : Nat,
          Exists (fun n : Nat => And (N <= n) (Peak F u n)) := by
      intro N
      by_cases hN :
          Exists (fun n : Nat => And (N <= n) (Peak F u n))
      · exact hN
      · have hbad :
            Exists
              (fun N0 : Nat =>
                forall n : Nat, N0 <= n -> Not (Peak F u n)) := by
          refine Exists.intro N ?_
          intro n hn hpeak
          exact hN (Exists.intro n (And.intro hn hpeak))
        exact False.elim (hex hbad)
    exact False.elim (h hinf)

/-- The choice sequence enumerating peaks: index zero picks a peak at or
above zero, and each step picks a peak beyond the previous choice plus one.
Built with `Classical.choose` under the infinitely-many-peaks hypothesis,
which is exactly one branch of the dichotomy. -/
noncomputable def peakIndex {u : Nat -> alpha}
    (hinf :
      forall N : Nat,
        Exists (fun n : Nat => And (N <= n) (Peak F u n))) :
    Nat -> Nat
  | 0 => Classical.choose (hinf 0)
  | k + 1 => Classical.choose (hinf (peakIndex hinf k + 1))

/-- Every selected index is a peak, the half of the choice specification
the decreasing branch consumes. -/
theorem peakIndex_peak {u : Nat -> alpha}
    (hinf :
      forall N : Nat,
        Exists (fun n : Nat => And (N <= n) (Peak F u n)))
    (k : Nat) :
    Peak F u (peakIndex F hinf k) := by
  cases k with
  | zero =>
      exact (Classical.choose_spec (hinf 0)).right
  | succ k =>
      exact
        (Classical.choose_spec
          (hinf (peakIndex F hinf k + 1))).right

/-- The selected indices are strictly increasing: each choice was demanded
beyond the previous index plus one, the other half of the specification. -/
theorem peakIndex_step {u : Nat -> alpha}
    (hinf :
      forall N : Nat,
        Exists (fun n : Nat => And (N <= n) (Peak F u n)))
    (k : Nat) :
    peakIndex F hinf k < peakIndex F hinf (k + 1) := by
  have hle :
      peakIndex F hinf k + 1 <= peakIndex F hinf (k + 1) :=
    (Classical.choose_spec (hinf (peakIndex F hinf k + 1))).left
  omega

/-- The peak enumeration is a legitimate subsequence index, the preceding
step packaged into `SubsequenceIndex`. -/
theorem peakIndex_subsequence {u : Nat -> alpha}
    (hinf :
      forall N : Nat,
        Exists (fun n : Nat => And (N <= n) (Peak F u n))) :
    SubsequenceIndex (peakIndex F hinf) :=
  peakIndex_step F hinf

/-- The peak subsequence is monotone decreasing: a later selected index lies
beyond the earlier peak, and a peak caps every term after it. -/
theorem peakIndex_decreasing {u : Nat -> alpha}
    (hinf :
      forall N : Nat,
        Exists (fun n : Nat => And (N <= n) (Peak F u n))) :
    F.MonotoneDecreasing (subsequence u (peakIndex F hinf)) := by
  intro n m hnm
  have hidx :
      peakIndex F hinf n <= peakIndex F hinf m :=
    subsequenceIndex_mono (peakIndex_subsequence F hinf) hnm
  exact peakIndex_peak F hinf n (peakIndex F hinf m) hidx

/-- The recursion behind the increasing branch: starting from a tail bound
`N` beyond which no index is a peak, repeatedly choose a later index whose
term is at least as large as the current one. The invariant `N <= i` is
carried in the subtype, keeping every choice inside the peak-free tail. -/
noncomputable def risingIndexState {u : Nat -> alpha}
    (N : Nat)
    (hno : forall n : Nat, N <= n -> Not (Peak F u n)) :
    Nat -> {i : Nat // N <= i}
  | 0 => ⟨N, Nat.le_refl N⟩
  | k + 1 =>
      let s := risingIndexState N hno k
      let hnext := not_peak_exists_later_above F (hno s.val s.property)
      let m := Classical.choose hnext
      have hm : s.val < m := (Classical.choose_spec hnext).left
      ⟨m, by omega⟩

/-- The index sequence of the increasing branch, read off the state
recursion; the estimates below use it without ever mentioning the subtype
invariant behind it. -/
noncomputable def risingIndex {u : Nat -> alpha}
    (N : Nat)
    (hno : forall n : Nat, N <= n -> Not (Peak F u n)) :
    Nat -> Nat :=
  fun k : Nat => (risingIndexState F N hno k).val

/-- Strictly increasing steps: the next choice was made strictly beyond the
current index. -/
theorem risingIndex_step {u : Nat -> alpha}
    (N : Nat)
    (hno : forall n : Nat, N <= n -> Not (Peak F u n))
    (k : Nat) :
    risingIndex F N hno k < risingIndex F N hno (k + 1) := by
  unfold risingIndex
  let s := risingIndexState F N hno k
  let hnext := not_peak_exists_later_above F (hno s.val s.property)
  change s.val < (Classical.choose hnext)
  exact (Classical.choose_spec hnext).left

/-- Each step lands on a term at least as large as the current one, the
extraction content that makes the subsequence monotone. -/
theorem risingIndex_step_le {u : Nat -> alpha}
    (N : Nat)
    (hno : forall n : Nat, N <= n -> Not (Peak F u n))
    (k : Nat) :
    F.le
      (u (risingIndex F N hno k))
      (u (risingIndex F N hno (k + 1))) := by
  unfold risingIndex
  let s := risingIndexState F N hno k
  let hnext := not_peak_exists_later_above F (hno s.val s.property)
  change F.le (u s.val) (u (Classical.choose hnext))
  exact (Classical.choose_spec hnext).right

/-- The rising enumeration is a legitimate subsequence index,
`risingIndex_step` packaged into `SubsequenceIndex`. -/
theorem risingIndex_subsequence {u : Nat -> alpha}
    (N : Nat)
    (hno : forall n : Nat, N <= n -> Not (Peak F u n)) :
    SubsequenceIndex (risingIndex F N hno) :=
  risingIndex_step F N hno

/-- The rising subsequence is monotone increasing, by transitivity along
the step inequalities. -/
theorem risingIndex_increasing {u : Nat -> alpha}
    (N : Nat)
    (hno : forall n : Nat, N <= n -> Not (Peak F u n)) :
    F.MonotoneIncreasing (subsequence u (risingIndex F N hno)) := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact F.le_refl (subsequence u (risingIndex F N hno) n)
  | step h ih =>
      exact F.le_trans ih (risingIndex_step_le F N hno _)

/-- Every sequence in an ordered field has a monotone subsequence,
increasing or decreasing: the classical peak argument. Infinitely many
peaks enumerate a decreasing subsequence; otherwise a tail free of peaks
admits an increasing one. No boundedness and no completeness is assumed --
the theorem is pure order combinatorics on the indices. -/
theorem exists_monotone_subsequence (u : Nat -> alpha) :
    Exists
      (fun phi : Nat -> Nat =>
        And (SubsequenceIndex phi)
          (Or
            (F.MonotoneIncreasing (subsequence u phi))
            (F.MonotoneDecreasing (subsequence u phi)))) := by
  classical
  by_cases hinf :
      forall N : Nat,
        Exists (fun n : Nat => And (N <= n) (Peak F u n))
  · refine Exists.intro (peakIndex F hinf) ?_
    exact And.intro (peakIndex_subsequence F hinf)
      (Or.inr (peakIndex_decreasing F hinf))
  · cases eventually_not_peak_of_not_infinite F hinf with
    | intro N hno =>
        refine Exists.intro (risingIndex F N hno) ?_
        exact And.intro (risingIndex_subsequence F N hno)
          (Or.inl (risingIndex_increasing F N hno))

end IsOrderedFieldBaseLike
end Tautology
