import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Bounded
import Tengoku.Tautology.Tautology.RealSequence.Subsequence
import Tengoku.Tautology.Tautology.RealTopology.Sequential

/-!
# Sequentially compact subsets are exactly the closed bounded ones

The sequential counterpart of `Tautology.RealCompactness.HeineBorel`, and the
file makes its hypotheses unusually explicit: the Bolzano-Weierstrass principle
is spent only on the direction that builds compactness, while the two
directions that extract boundedness and closedness each spend a different
Archimedean principle and no completeness whatsoever.

Both extraction directions are refutations that construct an escaping
sequence. For boundedness, pick at step `n` a point outside the window of
radius `n + 1`; any convergent subsequence is eventually bounded, and the
linear Archimedean principle produces a natural number past that bound, which
the subsequence index dominates. For closedness, suppose a point outside the
set had no neighbourhood in the complement; pick at step `n` a point of the set
within `1 / (n + 1)`, which the inverse-natural Archimedean principle drives to
convergence, contradicting that subsequential limits stay in the set.

## Position and role

Implementation module. `Tautology.RealCompactness.LimitPointCompact` and
`Tautology.RealCompactness.CompactSequential` build on it, and the facade
`Tautology.RealTheory.Compactness` carries the results to the selected carrier.
The Bolzano-Weierstrass hypothesis is supplied there by
`Tautology.RealCompactness.ClosedInterval.Selected`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The shrinking radius `1 / (n + 1)`, the window size this module uses to
turn proximity into convergence: the radii never increase with `n`, and the
inverse Archimedean principle is exactly what makes them eventually smaller
than any given positive quantity. -/
def invSuccRadius (n : Nat) : alpha :=
  F.inv (nat F (n + 1))

theorem invSuccRadius_pos (n : Nat) :
    F.lt F.zero (invSuccRadius F n) := by
  unfold invSuccRadius
  exact inv_pos F (nat_succ_pos F n)

theorem invSuccRadius_antitone {m n : Nat}
    (hmn : m <= n) :
    F.le (invSuccRadius F n) (invSuccRadius F m) := by
  unfold invSuccRadius
  apply inv_le_inv_of_le_pos F
  · exact nat_succ_pos F m
  · exact nat_succ_pos F n
  · exact nat_le_nat_of_le F (by omega : m + 1 <= n + 1)

/-- The Archimedean principle in the form this module consumes it: every
field element lies below some natural. It is extracted from the
`large_nat_mul` field of the principle, applied to the absolute value of
`x` at an epsilon of one. -/
theorem exists_nat_gt_of_linearArchimedean
    (harch : LinearArchimedeanPrinciple F)
    (x : alpha) :
    Exists (fun n : Nat => F.lt x (nat F n)) := by
  cases harch.large_nat_mul (abs_nonneg F x) (zero_lt_one F) with
  | intro n hn =>
      refine Exists.intro n ?_
      have habs_lt : F.lt (abs F x) (nat F n) := by
        rwa [F.mul_one] at hn
      exact lt_of_le_of_lt F (le_abs_self F x) habs_lt

theorem seqTendsto_subsequence {u : Nat -> alpha}
    {phi : Nat -> Nat} {l : alpha}
    (hphi : SubsequenceIndex phi)
    (hu : SeqTendsto F u l) :
    SeqTendsto F (subsequence u phi) l :=
  seqTendsto_of_subsequenceIndex F hu hphi

theorem limit_mem_of_closed {S : alpha -> Prop}
    {u : Nat -> alpha} {l : alpha}
    (hclosed : IsClosed F S)
    (huS : forall n : Nat, S (u n))
    (hlim : SeqTendsto F u l) :
    S l :=
  mem_of_closed_of_seqTendsto F hclosed huS hlim

theorem seqBounded_of_setBounded {S : alpha -> Prop}
    {u : Nat -> alpha}
    (hbdd : SetBounded F S)
    (huS : forall n : Nat, S (u n)) :
    SeqBounded F u := by
  cases hbdd with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          exact Exists.intro left
            (Exists.intro right
              (fun n : Nat => hright (u n) (huS n)))

/-- A closed bounded set is sequentially compact, from the sequential half
of Bolzano-Weierstrass: the terms form a bounded sequence, the principle
returns a convergent subsequence, and closedness keeps its limit inside
the set. This is the only step of this direction where a
Bolzano-Weierstrass input is spent. -/
theorem sequentiallyCompact_of_closed_bounded
    (hseq : BolzanoWeierstrassSequentialPrinciple F)
    {S : alpha -> Prop}
    (hclosed : IsClosed F S)
    (hbdd : SetBounded F S) :
    IsSequentiallyCompact F S := by
  intro u huS
  have huBdd : SeqBounded F u :=
    seqBounded_of_setBounded F hbdd huS
  cases hseq.convergent_subsequence u huBdd with
  | intro l hl =>
      cases hl with
      | intro phi hphi =>
          have hsubS :
              forall n : Nat, S (subsequence u phi n) := by
            intro n
            exact huS (phi n)
          have hlS : S l :=
            limit_mem_of_closed F hclosed hsubS hphi.right
          exact
            Exists.intro l
              (And.intro hlS
                (Exists.intro phi hphi))

/-- Unboundedness in the form the escape construction needs: if `S` is not
bounded, then for every bound `B` some member of `S` lies outside the
window between `-B` and `B`. Proved by contraposition, a set with no such
member being bounded by that very window, so that the choice below has an
existence statement to feed on. -/
theorem exists_outside_of_not_setBounded {S : alpha -> Prop}
    (hnot : Not (SetBounded F S))
    (B : alpha) :
    Exists
      (fun x : alpha =>
        And (S x)
          (Or (F.lt x (F.neg B)) (F.lt B x))) := by
  classical
  by_cases hex :
      Exists
        (fun x : alpha =>
          And (S x)
            (Or (F.lt x (F.neg B)) (F.lt B x)))
  · exact hex
  · have hbdd : SetBounded F S := by
      refine Exists.intro (F.neg B) ?_
      refine Exists.intro B ?_
      intro x hxS
      have hnotOutside :
          Not (Or (F.lt x (F.neg B)) (F.lt B x)) := by
        intro hout
        exact hex (Exists.intro x (And.intro hxS hout))
      constructor
      · apply le_of_not_lt F
        intro hxlt
        exact hnotOutside (Or.inl hxlt)
      · apply le_of_not_lt F
        intro hBltx
        exact hnotOutside (Or.inr hBltx)
    exact False.elim (hnot hbdd)

/-- The escape sequence read off an unbounded set: at stage `n`, a chosen
member of `S` outside the window of width `nat (n + 1)`. Choice enters here
through `Classical.choose`; any sequence with these two properties would
drive the boundedness contradiction equally well. -/
noncomputable def unboundedEscapePoint {S : alpha -> Prop}
    (hnot : Not (SetBounded F S))
    (n : Nat) : alpha :=
  Classical.choose
    (exists_outside_of_not_setBounded F hnot (nat F (n + 1)))

theorem unboundedEscapePoint_mem {S : alpha -> Prop}
    (hnot : Not (SetBounded F S))
    (n : Nat) :
    S (unboundedEscapePoint F hnot n) :=
  (Classical.choose_spec
    (exists_outside_of_not_setBounded F hnot (nat F (n + 1)))).left

theorem unboundedEscapePoint_outside {S : alpha -> Prop}
    (hnot : Not (SetBounded F S))
    (n : Nat) :
    Or
      (F.lt (unboundedEscapePoint F hnot n)
        (F.neg (nat F (n + 1))))
      (F.lt (nat F (n + 1))
        (unboundedEscapePoint F hnot n)) :=
  (Classical.choose_spec
    (exists_outside_of_not_setBounded F hnot (nat F (n + 1)))).right

theorem lt_abs_of_outside {x B : alpha}
    (hout : Or (F.lt x (F.neg B)) (F.lt B x)) :
    F.lt B (abs F x) := by
  cases hout with
  | inl hleft =>
      have hneg : F.lt B (F.neg x) := by
        have h := neg_lt_neg F hleft
        rwa [neg_neg F B] at h
      exact lt_of_lt_of_le F hneg (neg_le_abs_self F x)
  | inr hright =>
      exact lt_of_lt_of_le F hright (le_abs_self F x)

/-- Sequentially compact sets are bounded. If not, the escape sequence of
`unboundedEscapePoint` lives in `S`, and sequential compactness gives a
convergent, hence eventually bounded, subsequence, while the Archimedean
principle supplies a natural threshold already beyond that bound -- a
subsequence index dominates its argument, so some escape stage is both past
the threshold and inside the bounded tail. -/
theorem bounded_of_sequentiallyCompact
    (harch : LinearArchimedeanPrinciple F)
    {S : alpha -> Prop}
    (hseq : IsSequentiallyCompact F S) :
    SetBounded F S := by
  classical
  by_cases hbdd : SetBounded F S
  · exact hbdd
  · let u : Nat -> alpha := unboundedEscapePoint F hbdd
    have huS : forall n : Nat, S (u n) := by
      intro n
      exact unboundedEscapePoint_mem F hbdd n
    cases hseq u huS with
    | intro l hl =>
        cases hl with
        | intro hlS hconv =>
            cases hconv with
            | intro phi hphi =>
                cases seqTendsto_eventuallyBounded F hphi.right with
                | intro B hB =>
                    cases hB.right with
                    | intro N hN =>
                        cases exists_nat_gt_of_linearArchimedean F harch B with
                        | intro m hm =>
                            let K := Nat.max N m
                            have hNK : N <= K := Nat.le_max_left N m
                            have hmK : m <= K := Nat.le_max_right N m
                            have hKphi : K <= phi K :=
                              subsequenceIndex_ge_self hphi.left K
                            have hm_phi_succ : m <= phi K + 1 := by
                              omega
                            have hB_lt_threshold :
                                F.lt B (nat F (phi K + 1)) :=
                              lt_of_lt_of_le F hm
                                (nat_le_nat_of_le F hm_phi_succ)
                            have hout :
                                Or
                                  (F.lt (u (phi K))
                                    (F.neg (nat F (phi K + 1))))
                                  (F.lt (nat F (phi K + 1))
                                    (u (phi K))) :=
                              unboundedEscapePoint_outside F hbdd (phi K)
                            have hthreshold_lt_abs :
                                F.lt (nat F (phi K + 1))
                                  (abs F (u (phi K))) :=
                              lt_abs_of_outside F hout
                            have hB_lt_abs :
                                F.lt B (abs F (subsequence u phi K)) := by
                              dsimp [subsequence]
                              exact lt_trans F hB_lt_threshold
                                hthreshold_lt_abs
                            have hclose :
                                F.lt (abs F (subsequence u phi K)) B :=
                              hN K hNK
                            exact False.elim ((lt_asymm F hB_lt_abs) hclose)

/-- If no open interval around `x` is contained in the complement of `S`,
then every open interval around `x` meets `S`. The contrapositive
restatement is what lets the choice below pick a point of `S` inside each
shrinking window. -/
theorem exists_mem_interval_of_no_compl_neighborhood
    {S : alpha -> Prop} {x left right : alpha}
    (hno :
      Not
        (Exists (fun a : alpha =>
          Exists (fun b : alpha =>
            And (F.lt a x)
              (And (F.lt x b)
                (forall y : alpha,
                  OpenInterval F a b y -> SetPred.Compl S y))))))
    (hleft : F.lt left x)
    (hright : F.lt x right) :
    Exists
      (fun y : alpha =>
        And (S y) (OpenInterval F left right y)) := by
  classical
  by_cases hex :
      Exists
        (fun y : alpha =>
          And (S y) (OpenInterval F left right y))
  · exact hex
  · have hneigh :
        Exists (fun a : alpha =>
          Exists (fun b : alpha =>
            And (F.lt a x)
              (And (F.lt x b)
                (forall y : alpha,
                  OpenInterval F a b y -> SetPred.Compl S y)))) := by
      refine Exists.intro left ?_
      refine Exists.intro right ?_
      refine And.intro hleft ?_
      refine And.intro hright ?_
      intro y hy hyS
      exact hex (Exists.intro y (And.intro hyS hy))
    exact False.elim (hno hneigh)

/-- The near-point sequence read off a point `x` whose every open interval
meets `S`: at stage `n`, a chosen point of `S` inside the window of radius
`invSuccRadius n` about `x`. -/
noncomputable def nearClosedPoint {S : alpha -> Prop} {x : alpha}
    (hno :
      Not
        (Exists (fun a : alpha =>
          Exists (fun b : alpha =>
            And (F.lt a x)
              (And (F.lt x b)
                (forall y : alpha,
                  OpenInterval F a b y -> SetPred.Compl S y))))))
    (n : Nat) : alpha :=
  Classical.choose
    (exists_mem_interval_of_no_compl_neighborhood F hno
      (sub_lt_self_of_pos F (invSuccRadius_pos F n))
      (by
        have h := add_lt_add_left F (invSuccRadius_pos F n) x
        rwa [F.add_zero] at h))

theorem nearClosedPoint_mem {S : alpha -> Prop} {x : alpha}
    (hno :
      Not
        (Exists (fun a : alpha =>
          Exists (fun b : alpha =>
            And (F.lt a x)
              (And (F.lt x b)
                (forall y : alpha,
                  OpenInterval F a b y -> SetPred.Compl S y))))))
    (n : Nat) :
    S (nearClosedPoint F hno n) :=
  (Classical.choose_spec
    (exists_mem_interval_of_no_compl_neighborhood F hno
      (sub_lt_self_of_pos F (invSuccRadius_pos F n))
      (by
        have h := add_lt_add_left F (invSuccRadius_pos F n) x
        rwa [F.add_zero] at h))).left

theorem nearClosedPoint_interval {S : alpha -> Prop} {x : alpha}
    (hno :
      Not
        (Exists (fun a : alpha =>
          Exists (fun b : alpha =>
            And (F.lt a x)
              (And (F.lt x b)
                (forall y : alpha,
                  OpenInterval F a b y -> SetPred.Compl S y))))))
    (n : Nat) :
    OpenInterval F
      (F.sub x (invSuccRadius F n))
      (F.add x (invSuccRadius F n))
      (nearClosedPoint F hno n) :=
  (Classical.choose_spec
    (exists_mem_interval_of_no_compl_neighborhood F hno
      (sub_lt_self_of_pos F (invSuccRadius_pos F n))
      (by
        have h := add_lt_add_left F (invSuccRadius_pos F n) x
        rwa [F.add_zero] at h))).right

/-- The chosen near-points converge to `x`, because their windows shrink:
making `1 / (n + 1)` eventually smaller than the tolerance is exactly what
the inverse Archimedean principle provides. This is the step where that
principle enters the closedness argument. -/
theorem nearClosedPoint_tendsto
    (hinvNat : InvNatArchimedeanPrinciple F)
    {S : alpha -> Prop} {x : alpha}
    (hno :
      Not
        (Exists (fun a : alpha =>
          Exists (fun b : alpha =>
            And (F.lt a x)
              (And (F.lt x b)
                (forall y : alpha,
                  OpenInterval F a b y -> SetPred.Compl S y)))))) :
    SeqTendsto F (nearClosedPoint F hno) x := by
  intro eps heps
  cases hinvNat.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hr_le : F.le (invSuccRadius F n) (invSuccRadius F N) :=
        invSuccRadius_antitone F hn
      have hr_lt_eps : F.lt (invSuccRadius F n) eps :=
        lt_of_le_of_lt F hr_le hN
      have hinterval := nearClosedPoint_interval F hno n
      have hclose :
          F.lt
            (abs F (F.sub (nearClosedPoint F hno n) x))
            (invSuccRadius F n) :=
        abs_sub_lt_of_bounds F hinterval.left hinterval.right
      exact lt_trans F hclose hr_lt_eps

/-- Sequentially compact sets are closed. For `x` outside `S`, either
some open interval around `x` already misses `S`, which is the openness
witness for the complement, or every interval meets `S`, and then the
near-point sequence converges to `x` while one of its subsequences converges
to a limit inside `S`; the two limits agree by uniqueness, which is the
contradiction. -/
theorem closed_of_sequentiallyCompact
    (hinvNat : InvNatArchimedeanPrinciple F)
    {S : alpha -> Prop}
    (hseq : IsSequentiallyCompact F S) :
    IsClosed F S := by
  intro x hxS
  classical
  by_cases hneigh :
      Exists (fun a : alpha =>
        Exists (fun b : alpha =>
          And (F.lt a x)
            (And (F.lt x b)
              (forall y : alpha,
                OpenInterval F a b y -> SetPred.Compl S y))))
  · exact hneigh
  · let u : Nat -> alpha := nearClosedPoint F hneigh
    have huS : forall n : Nat, S (u n) := by
      intro n
      exact nearClosedPoint_mem F hneigh n
    have huTendsto : SeqTendsto F u x :=
      nearClosedPoint_tendsto F hinvNat hneigh
    cases hseq u huS with
    | intro l hl =>
        cases hl with
        | intro hlS hconv =>
            cases hconv with
            | intro phi hphi =>
                have hsubx :
                    SeqTendsto F (subsequence u phi) x :=
                  seqTendsto_subsequence F hphi.left huTendsto
                have hlx : l = x :=
                  seqTendsto_unique F hphi.right hsubx
                rw [hlx] at hlS
                exact False.elim (hxS hlS)

/-- The characterization of sequential compactness on the line. From
closed-and-bounded it is Bolzano-Weierstrass alone; back the other way,
boundedness costs the linear Archimedean principle and closedness the
inverse one, through the escape sequence and the near-point sequence
respectively. -/
theorem sequentialCompact_iff_closed_bounded
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (S : alpha -> Prop) :
    IsSequentiallyCompact F S <-> And (IsClosed F S) (SetBounded F S) := by
  constructor
  · intro hseq
    exact And.intro
      (closed_of_sequentiallyCompact F hinvNat hseq)
      (bounded_of_sequentiallyCompact F harch hseq)
  · intro h
    exact sequentiallyCompact_of_closed_bounded F hBW h.left h.right

end IsOrderedFieldBaseLike
end Tautology
