import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealSequence.Subsequence

/-!
# Edge: monotone convergence gives the Cauchy criterion

The second crossing on the selected route, and it is free -- no Archimedean
hypothesis, eight declarations. The classical peak argument does the work: a
Cauchy sequence has a monotone subsequence, monotone convergence supplies its
limit, and a Cauchy sequence with a convergent subsequence converges.

Compare `Tautology.RealSequence.Principles.FromNestedCauchy`, which reaches the
same node from the other side at five times the declaration count --
thirty-nine against eight -- and with an Archimedean hypothesis. Where a route
enters the graph decides what the later steps cost.

## Position and role

Edge module exporting `cauchyCriterion`, travelled by
`Tautology.RealSequence.Principles.Selected` as its last step.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace FromMonotoneCauchy

/-- An eventual property pulls back along a subsequence index: since
`phi n >= n` for a `SubsequenceIndex`, the threshold from which `P` holds
also serves `P (phi n)`. -/
theorem eventually_subsequence_of_eventually {phi : Nat -> Nat}
    {P : Nat -> Prop}
    (hphi : SubsequenceIndex phi)
    (hP : Eventually P) :
    Eventually (fun n : Nat => P (phi n)) := by
  cases hP with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hn_phi : n <= phi n :=
        subsequenceIndex_ge_self hphi n
      exact hN (phi n) (Nat.le_trans hn hn_phi)

/-- A Cauchy sequence is eventually bounded above, by the term at a
tolerance-one threshold shifted up by one. Only eventual boundedness is
available, since finitely many early terms can be arbitrary. -/
theorem seqCauchy_eventually_upper {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    Exists (fun B : alpha => Eventually (fun n : Nat => F.le (u n) B)) := by
  cases hu F.one (zero_lt_one F) with
  | intro N hN =>
      refine Exists.intro (F.add (u N) F.one) ?_
      refine Exists.intro N ?_
      intro n hn
      have hclose := hN n N hn (Nat.le_refl N)
      exact le_of_lt F (abs_sub_lt_right F hclose)

/-- The lower mirror: a Cauchy sequence is eventually bounded below by the
term at a tolerance-one threshold shifted down by one. -/
theorem seqCauchy_eventually_lower {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    Exists (fun B : alpha => Eventually (fun n : Nat => F.le B (u n))) := by
  cases hu F.one (zero_lt_one F) with
  | intro N hN =>
      refine Exists.intro (F.sub (u N) F.one) ?_
      refine Exists.intro N ?_
      intro n hn
      have hclose := hN n N hn (Nat.le_refl N)
      exact le_of_lt F (abs_sub_lt_left F hclose)

/-- For an increasing sequence an eventual upper bound is a global one,
since every earlier term is dominated by the term at the threshold. This
converts the eventual bounds a Cauchy sequence supplies into the bounds the
monotone node demands. -/
theorem monotoneIncreasing_boundedAbove_of_eventually_le
    {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hB : Eventually (fun n : Nat => F.le (u n) B)) :
    F.SeqBoundedAbove u := by
  cases hB with
  | intro N hN =>
      refine Exists.intro B ?_
      intro n
      cases Nat.le_total n N with
      | inl hnN =>
          exact F.le_trans (hmono n N hnN) (hN N (Nat.le_refl N))
      | inr hNn =>
          exact hN n hNn

/-- The decreasing mirror of the same conversion, from an eventual lower
bound to a global one. -/
theorem monotoneDecreasing_boundedBelow_of_eventually_ge
    {u : Nat -> alpha} {B : alpha}
    (hmono : F.MonotoneDecreasing u)
    (hB : Eventually (fun n : Nat => F.le B (u n))) :
    F.SeqBoundedBelow u := by
  cases hB with
  | intro N hN =>
      refine Exists.intro B ?_
      intro n
      cases Nat.le_total n N with
      | inl hnN =>
          exact F.le_trans (hN N (Nat.le_refl N)) (hmono n N hnN)
      | inr hNn =>
          exact hN n hNn

/-- A Cauchy sequence with a convergent subsequence converges to that
subsequence's limit: at half the tolerance the sequence is eventually
close to the reindexed term `u (phi K)`, which is itself close to the
limit. This is what lets the monotone node, applied to a subsequence only,
fix the convergence of the whole sequence. -/
theorem seqTendsto_of_cauchy_subsequence {u : Nat -> alpha}
    {phi : Nat -> Nat} {l : alpha}
    (hu : F.SeqCauchy u)
    (hphi : SubsequenceIndex phi)
    (hsub : F.SeqTendsto (subsequence u phi) l) :
    F.SeqTendsto u l := by
  intro eps heps
  let delta := half F eps
  have hdelta : F.lt F.zero delta :=
    half_pos F heps
  cases hu delta hdelta with
  | intro Nc hNc =>
      cases hsub delta hdelta with
      | intro Ns hNs =>
          let K := Nat.max Nc Ns
          refine Exists.intro K ?_
          intro n hn
          have hNc_n : Nc <= n :=
            Nat.le_trans (Nat.le_max_left Nc Ns) hn
          have hNs_K : Ns <= K :=
            Nat.le_max_right Nc Ns
          have hK_phi : K <= phi K :=
            subsequenceIndex_ge_self hphi K
          have hNc_phi : Nc <= phi K :=
            Nat.le_trans (Nat.le_max_left Nc Ns) hK_phi
          have hclose_cauchy :
              F.lt (abs F (F.sub (u n) (u (phi K)))) delta :=
            hNc n (phi K) hNc_n hNc_phi
          have hclose_sub :
              F.lt (abs F (F.sub (u (phi K)) l)) delta :=
            hNs K hNs_K
          have hsum :
              F.lt
                (F.add
                  (abs F (F.sub (u n) (u (phi K))))
                  (abs F (F.sub (u (phi K)) l)))
                eps := by
            have hsum_delta :
                F.lt
                  (F.add
                    (abs F (F.sub (u n) (u (phi K))))
                    (abs F (F.sub (u (phi K)) l)))
                  (F.add delta delta) :=
              add_lt_add F hclose_cauchy hclose_sub
            rwa [half_add_half F eps] at hsum_delta
          have htri :
              F.le (abs F (F.sub (u n) l))
                (F.add
                  (abs F (F.sub (u n) (u (phi K))))
                  (abs F (F.sub (u (phi K)) l))) := by
            have h :=
              abs_add_le_abs_add_abs F
                (F.sub (u n) (u (phi K)))
                (F.sub (u (phi K)) l)
            rwa [sub_add_sub_cancel F (u n) (u (phi K)) l] at h
          exact lt_of_le_of_lt F htri hsum

/-- Assembly of the edge: every sequence has a monotone subsequence by the
peak argument of `Tautology.RealSequence.Subsequence`; a Cauchy sequence is
eventually bounded, so that subsequence is bounded; the monotone node
converges it; and `seqTendsto_of_cauchy_subsequence` returns the limit to
the whole sequence. -/
theorem cauchy_converges
    (hmono : F.MonotoneConvergencePrinciple)
    {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    Exists (fun l : alpha => F.SeqTendsto u l) := by
  cases exists_monotone_subsequence F u with
  | intro phi hphi =>
      cases hphi.right with
      | inl hinc =>
          cases seqCauchy_eventually_upper F hu with
          | intro B hB =>
              have hBsub :
                  Eventually
                    (fun n : Nat =>
                      F.le (subsequence u phi n) B) :=
                eventually_subsequence_of_eventually hphi.left hB
              have hbdd :
                  F.SeqBoundedAbove (subsequence u phi) :=
                monotoneIncreasing_boundedAbove_of_eventually_le
                  F hinc hBsub
              cases hmono.increasing (subsequence u phi) hinc hbdd with
              | intro l hl =>
                  exact Exists.intro l
                    (seqTendsto_of_cauchy_subsequence F hu hphi.left hl)
      | inr hdec =>
          cases seqCauchy_eventually_lower F hu with
          | intro B hB =>
              have hBsub :
                  Eventually
                    (fun n : Nat =>
                      F.le B (subsequence u phi n)) :=
                eventually_subsequence_of_eventually hphi.left hB
              have hbdd :
                  F.SeqBoundedBelow (subsequence u phi) :=
                monotoneDecreasing_boundedBelow_of_eventually_ge
                  F hdec hBsub
              cases hmono.decreasing (subsequence u phi) hdec hbdd with
              | intro l hl =>
                  exact Exists.intro l
                    (seqTendsto_of_cauchy_subsequence F hu hphi.left hl)

/-- The edge from the monotone-convergence node to the Cauchy node, and it
carries no extra hypothesis: the peak argument is combinatorics, and a
Cauchy sequence supplies its own eventual bounds, so ordered-field structure
is enough in this direction. -/
theorem cauchyCriterion
    (hmono : F.MonotoneConvergencePrinciple) :
    F.CauchyCriterionPrinciple where
  converges := by
    intro u hu
    exact cauchy_converges F hmono hu

end FromMonotoneCauchy
end IsOrderedFieldBaseLike
end Tautology
