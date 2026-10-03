import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Edge: the Cauchy criterion gives monotone convergence

Eleven declarations and a `LinearArchimedeanPrinciple`. The argument is a
refutation: if a bounded increasing sequence were not Cauchy, some fixed
tolerance would be exceeded infinitely often, and chaining those jumps builds
an arithmetic progression inside the sequence. The Archimedean hypothesis is
what lets that progression pass any bound, contradicting boundedness.

The decreasing case is obtained by negating the sequence rather than repeating
the argument.

## Position and role

Edge module exporting `monotoneConvergence`, used by
`RealSequence.Principles.Routes.fromCauchy`. Not on the selected path.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace FromCauchyMonotone

theorem add_le_of_sub_le {x y eps : alpha}
    (h : F.le eps (F.sub y x)) :
    F.le (F.add x eps) y := by
  have h' := F.add_le_add_right h x
  have hleft : F.add eps x = F.add x eps :=
    F.add_comm eps x
  rwa [hleft, sub_add_cancel F y x] at h'

theorem add_nat_mul_succ (x eps : alpha) (k : Nat) :
    F.add (F.add x (F.mul (nat F k) eps)) eps =
      F.add x (F.mul (nat F (k + 1)) eps) := by
  calc
    F.add (F.add x (F.mul (nat F k) eps)) eps =
        F.add x (F.add (F.mul (nat F k) eps) eps) := by
          rw [F.add_assoc]
    _ = F.add x
        (F.add (F.mul (nat F k) eps) (F.mul F.one eps)) := by
          rw [F.one_mul]
    _ = F.add x (F.mul (F.add (nat F k) F.one) eps) := by
          rw [F.add_mul]
    _ = F.add x (F.mul (nat F (k + 1)) eps) := by
          rw [nat_succ]

/-- If the Cauchy condition fails at tolerance `eps`, then past any index
some pair of terms violates it. Obtained classically, this is the input the
jump construction below runs on. -/
theorem exists_bad_pair_of_not_cauchy_at {u : Nat -> alpha}
    {eps : alpha}
    (hbad :
      Not
        (Exists
          (fun N : Nat =>
            forall n m : Nat,
              N <= n ->
                N <= m ->
                  F.lt (abs F (F.sub (u n) (u m))) eps)))
    (N : Nat) :
    Exists
      (fun n : Nat =>
        Exists
          (fun m : Nat =>
            And (N <= n)
              (And (N <= m)
                (Not (F.lt (abs F (F.sub (u n) (u m))) eps))))) := by
  classical
  by_cases hex :
      Exists
        (fun n : Nat =>
          Exists
            (fun m : Nat =>
              And (N <= n)
                (And (N <= m)
                  (Not (F.lt (abs F (F.sub (u n) (u m))) eps)))))
  · exact hex
  · have hgood :
        forall n m : Nat,
          N <= n ->
            N <= m ->
              F.lt (abs F (F.sub (u n) (u m))) eps := by
      intro n m hn hm
      by_cases hlt : F.lt (abs F (F.sub (u n) (u m))) eps
      · exact hlt
      · exact False.elim
          (hex
            (Exists.intro n
              (Exists.intro m
                (And.intro hn (And.intro hm hlt)))))
    exact False.elim (hbad (Exists.intro N hgood))

/-- For an increasing sequence the violating pair straightens out: some
index past `N` carries a term at least `u N` shifted up by `eps`.
Monotonicity is what turns the failure of an absolute difference into a
forward jump. -/
theorem exists_later_add_eps_le_of_not_cauchy {u : Nat -> alpha}
    {eps : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbad :
      Not
        (Exists
          (fun N : Nat =>
            forall n m : Nat,
              N <= n ->
                N <= m ->
                  F.lt (abs F (F.sub (u n) (u m))) eps)))
    (N : Nat) :
    Exists (fun M : Nat =>
      And (N <= M) (F.le (F.add (u N) eps) (u M))) := by
  cases exists_bad_pair_of_not_cauchy_at F hbad N with
  | intro n hn =>
      cases hn with
      | intro m hm =>
          have hNn : N <= n := hm.left
          have hNm : N <= m := hm.right.left
          have hnot : Not (F.lt (abs F (F.sub (u n) (u m))) eps) :=
            hm.right.right
          have hle_abs : F.le eps (abs F (F.sub (u n) (u m))) :=
            le_of_not_lt F hnot
          cases Nat.le_total n m with
          | inl hnm =>
              have hunm : F.le (u n) (u m) :=
                hmono n m hnm
              have hgap_nonneg : F.le F.zero (F.sub (u m) (u n)) :=
                sub_nonneg_of_le F hunm
              have hle_gap : F.le eps (F.sub (u m) (u n)) := by
                rwa [abs_sub_comm F (u n) (u m),
                  abs_of_nonneg F hgap_nonneg] at hle_abs
              have hadd : F.le (F.add (u n) eps) (u m) :=
                add_le_of_sub_le F hle_gap
              have hN_add :
                  F.le (F.add (u N) eps) (F.add (u n) eps) :=
                F.add_le_add_right (hmono N n hNn) eps
              exact Exists.intro m
                (And.intro hNm (F.le_trans hN_add hadd))
          | inr hmn =>
              have humn : F.le (u m) (u n) :=
                hmono m n hmn
              have hgap_nonneg : F.le F.zero (F.sub (u n) (u m)) :=
                sub_nonneg_of_le F humn
              have hle_gap : F.le eps (F.sub (u n) (u m)) := by
                rwa [abs_of_nonneg F hgap_nonneg] at hle_abs
              have hadd : F.le (F.add (u m) eps) (u n) :=
                add_le_of_sub_le F hle_gap
              have hN_add :
                  F.le (F.add (u N) eps) (F.add (u m) eps) :=
                F.add_le_add_right (hmono N m hNm) eps
              exact Exists.intro n
                (And.intro hNn (F.le_trans hN_add hadd))

/-- The chain of jumping indices: starting from zero, each next index is
chosen so that the term there exceeds the previous term by at least `eps`.
It exists only under the not-Cauchy hypothesis, and is chosen
classically. -/
noncomputable def jumpIndex {u : Nat -> alpha} {eps : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbad :
      Not
        (Exists
          (fun N : Nat =>
            forall n m : Nat,
              N <= n ->
                N <= m ->
                  F.lt (abs F (F.sub (u n) (u m))) eps))) :
    Nat -> Nat
  | 0 => 0
  | k + 1 =>
      Classical.choose
        (exists_later_add_eps_le_of_not_cauchy F hmono hbad
          (jumpIndex hmono hbad k))

theorem jumpIndex_step_le {u : Nat -> alpha} {eps : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbad :
      Not
        (Exists
          (fun N : Nat =>
            forall n m : Nat,
              N <= n ->
                N <= m ->
                  F.lt (abs F (F.sub (u n) (u m))) eps)))
    (k : Nat) :
    F.le
      (F.add (u (jumpIndex F hmono hbad k)) eps)
      (u (jumpIndex F hmono hbad (k + 1))) :=
  (Classical.choose_spec
    (exists_later_add_eps_le_of_not_cauchy F hmono hbad
      (jumpIndex F hmono hbad k))).right

/-- Along the chain the terms dominate an arithmetic progression:
`u (jumpIndex k)` is at least `u 0` plus `k` copies of `eps`. A bounded
sequence cannot host such a progression, which is the contradiction the
edge runs on. -/
theorem jumpIndex_lower_bound {u : Nat -> alpha} {eps : alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbad :
      Not
        (Exists
          (fun N : Nat =>
            forall n m : Nat,
              N <= n ->
                N <= m ->
                  F.lt (abs F (F.sub (u n) (u m))) eps)))
    (k : Nat) :
    F.le
      (F.add (u 0) (F.mul (nat F k) eps))
      (u (jumpIndex F hmono hbad k)) := by
  induction k with
  | zero =>
      change F.le (F.add (u 0) (F.mul (nat F 0) eps)) (u 0)
      rw [nat_zero, zero_mul F, F.add_zero]
      exact F.le_refl (u 0)
  | succ k ih =>
      have hprev_add :
          F.le
            (F.add (F.add (u 0) (F.mul (nat F k) eps)) eps)
            (F.add (u (jumpIndex F hmono hbad k)) eps) :=
        F.add_le_add_right ih eps
      have hstep := jumpIndex_step_le F hmono hbad k
      have hmain :
          F.le
            (F.add (F.add (u 0) (F.mul (nat F k) eps)) eps)
            (u (jumpIndex F hmono hbad (k + 1))) :=
        F.le_trans hprev_add hstep
      rwa [add_nat_mul_succ F (u 0) eps k] at hmain

/-- A bounded increasing sequence is Cauchy, given the linear Archimedean
principle. The argument is by contradiction: were the Cauchy condition to
fail at some `eps`, the jump chain would pin `u 0` plus `k` copies of
`eps` below the bound for every `k`, and the principle supplies a `k` for
which that is impossible. This is the single place where the edge's
Archimedean hypothesis enters. -/
theorem increasing_seqCauchy_of_bounded
    (harch : F.LinearArchimedeanPrinciple)
    {u : Nat -> alpha}
    (hmono : F.MonotoneIncreasing u)
    (hbdd : F.SeqBoundedAbove u) :
    F.SeqCauchy u := by
  intro eps heps
  classical
  by_cases hgood :
      Exists
        (fun N : Nat =>
          forall n m : Nat,
            N <= n ->
              N <= m ->
                F.lt (abs F (F.sub (u n) (u m))) eps)
  · exact hgood
  · cases hbdd with
    | intro B hB =>
        let L := F.sub B (u 0)
        have hL_nonneg : F.le F.zero L :=
          sub_nonneg_of_le F (hB 0)
        cases harch.large_nat_mul hL_nonneg heps with
        | intro K hK =>
            have hlow :=
              jumpIndex_lower_bound F hmono hgood K
            have hupper : F.le (u (jumpIndex F hmono hgood K)) B :=
              hB (jumpIndex F hmono hgood K)
            have hsum_le_B :
                F.le
                  (F.add (u 0) (F.mul (nat F K) eps))
                  B :=
              F.le_trans hlow hupper
            have hB_lt_sum :
                F.lt B (F.add (u 0) (F.mul (nat F K) eps)) := by
              have h := add_lt_add_right F hK (u 0)
              have hright :
                  F.add (F.mul (nat F K) eps) (u 0) =
                    F.add (u 0) (F.mul (nat F K) eps) :=
                F.add_comm (F.mul (nat F K) eps) (u 0)
              rwa [sub_add_cancel F B (u 0), hright] at h
            exact False.elim ((not_le_of_lt F hB_lt_sum) hsum_le_B)

/-- Negating every term preserves the Cauchy property, the mirror step that
reduces the decreasing case to the increasing one. -/
theorem seqCauchy_of_neg_seqCauchy {u : Nat -> alpha}
    (hv : F.SeqCauchy (fun n : Nat => F.neg (u n))) :
    F.SeqCauchy u := by
  intro eps heps
  cases hv eps heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n m hn hm
      have h := hN n m hn hm
      simpa [sub_neg_neg_eq_neg_sub F (u n) (u m),
        abs_neg F (F.sub (u n) (u m))] using h

/-- A bounded decreasing sequence is Cauchy, by negating it into a bounded
increasing one and using the mirror step. -/
theorem decreasing_seqCauchy_of_bounded
    (harch : F.LinearArchimedeanPrinciple)
    {u : Nat -> alpha}
    (hmono : F.MonotoneDecreasing u)
    (hbdd : F.SeqBoundedBelow u) :
    F.SeqCauchy u := by
  let v : Nat -> alpha := fun n => F.neg (u n)
  have hvmono : F.MonotoneIncreasing v :=
    neg_monotone_increasing_of_decreasing F hmono
  have hvbdd : F.SeqBoundedAbove v :=
    neg_boundedAbove_of_boundedBelow F hbdd
  have hvcauchy : F.SeqCauchy v :=
    increasing_seqCauchy_of_bounded F harch hvmono hvbdd
  exact seqCauchy_of_neg_seqCauchy F hvcauchy

/-- The edge from the Cauchy node to the monotone-convergence node, with
the linear Archimedean principle as its price. The whole content is that a
bounded monotone sequence is Cauchy, the conversion above; once that
holds, the node merely has to be applied to the sequences it
produces. -/
theorem monotoneConvergence
    (hcauchy : F.CauchyCriterionPrinciple)
    (harch : F.LinearArchimedeanPrinciple) :
    F.MonotoneConvergencePrinciple where
  increasing := by
    intro u hmono hbdd
    exact hcauchy.converges u
      (increasing_seqCauchy_of_bounded F harch hmono hbdd)
  decreasing := by
    intro u hmono hbdd
    exact hcauchy.converges u
      (decreasing_seqCauchy_of_bounded F harch hmono hbdd)

end FromCauchyMonotone
end IsOrderedFieldBaseLike
end Tautology
