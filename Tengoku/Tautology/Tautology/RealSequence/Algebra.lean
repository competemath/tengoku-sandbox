import Tengoku.Tautology.Tautology.RealSequence.Basic

/-!
# Limits are unique, additive, and respect negation

Four results, one method. Intersect the two eventual statements into a single
threshold, push each part into half the tolerance, close with the triangle
inequality. Uniqueness is the same idea run at the distance between two
candidate limits.

The difference rule is assembled from the sum and negation rules rather than
proved on its own -- worth noticing, because it is why nothing here needs a
separate estimate.

## Position and role

Implementation module, over an arbitrary ordered field; completeness plays no
part. The multiplicative rules live apart, in `Tautology.RealSequence.Mul` and
`Tautology.RealSequence.InvDiv`, because they need the eventual boundedness
developed in `Tautology.RealSequence.Bounded`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- A sequence has at most one limit. Two candidate limits are placed at
their mutual distance and the tails are driven to half of it on either
side, so only the order separation of the field enters. This is what
licenses speaking of the limit of a sequence, and downstream of the sum of
a series. -/
theorem seqTendsto_unique {u : Nat -> alpha} {a b : alpha}
    (ha : SeqTendsto F u a)
    (hb : SeqTendsto F u b) :
    a = b := by
  by_cases hab : a = b
  · exact hab
  · let eps := abs F (F.sub a b)
    have hsub_ne : Not (F.sub a b = F.zero) := by
      intro hsub
      exact hab (eq_of_sub_eq_zero F hsub)
    have heps : F.lt F.zero eps :=
      abs_pos_of_ne_zero F hsub_ne
    let delta := half F eps
    have hdelta : F.lt F.zero delta :=
      half_pos F heps
    have hA := ha delta hdelta
    have hB := hb delta hdelta
    cases Eventually.and hA hB with
    | intro N hN =>
        have hN' := hN N (Nat.le_refl N)
        have hleft : F.lt (abs F (F.sub a (u N))) delta := by
          simpa [abs_sub_comm F a (u N)] using hN'.left
        have hright : F.lt (abs F (F.sub (u N) b)) delta :=
          hN'.right
        have hsum :
            F.lt
              (F.add (abs F (F.sub a (u N)))
                (abs F (F.sub (u N) b)))
              eps := by
          have hsum_delta :
              F.lt
                (F.add (abs F (F.sub a (u N)))
                  (abs F (F.sub (u N) b)))
                (F.add delta delta) :=
            add_lt_add F hleft hright
          rwa [half_add_half F eps] at hsum_delta
        have htri :
            F.le (abs F (F.sub a b))
              (F.add (abs F (F.sub a (u N)))
                (abs F (F.sub (u N) b))) := by
          have h :=
            abs_add_le_abs_add_abs F (F.sub a (u N)) (F.sub (u N) b)
          rwa [sub_add_sub_cancel F a (u N) b] at h
        have hbad : F.lt eps eps :=
          lt_of_le_of_lt F htri hsum
        exact False.elim ((lt_irrefl F eps) hbad)

/-- Sums of convergent sequences converge to the sum of the limits. The two
eventual statements are intersected into one threshold and each summand is
driven within half the tolerance, the pattern every algebra lemma in this
chain of modules repeats. -/
theorem seqTendsto_add {u v : Nat -> alpha} {a b : alpha}
    (hu : SeqTendsto F u a)
    (hv : SeqTendsto F v b) :
    SeqTendsto F (fun n => F.add (u n) (v n)) (F.add a b) := by
  intro eps heps
  let delta := half F eps
  have hdelta : F.lt F.zero delta :=
    half_pos F heps
  have hu_delta := hu delta hdelta
  have hv_delta := hv delta hdelta
  apply Eventually.mono ?_ (Eventually.and hu_delta hv_delta)
  intro n hn
  have hsum :
      F.lt
        (F.add (abs F (F.sub (u n) a)) (abs F (F.sub (v n) b)))
        eps := by
    have hsum_delta :
        F.lt
          (F.add (abs F (F.sub (u n) a)) (abs F (F.sub (v n) b)))
          (F.add delta delta) :=
      add_lt_add F hn.left hn.right
    rwa [half_add_half F eps] at hsum_delta
  have htri :
      F.le
        (abs F (F.sub (F.add (u n) (v n)) (F.add a b)))
        (F.add (abs F (F.sub (u n) a)) (abs F (F.sub (v n) b))) := by
    have h :=
      abs_add_le_abs_add_abs F (F.sub (u n) a) (F.sub (v n) b)
    rw [add_sub_add_eq_sub_add_sub F (u n) (v n) a b]
    exact h
  exact lt_of_le_of_lt F htri hsum

/-- Termwise negation converges to the negated limit. The absolute value
swallows the sign, so no case analysis is needed; this is the half of the
subtraction rule that is not the addition rule. -/
theorem seqTendsto_neg {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a) :
    SeqTendsto F (fun n => F.neg (u n)) (F.neg a) := by
  intro eps heps
  apply Eventually.mono ?_ (hu eps heps)
  intro n hn
  rwa [sub_neg_neg_eq_neg_sub F (u n) a, abs_neg F (F.sub (u n) a)]

/-- Differences of convergent sequences converge to the difference of the
limits, assembled from the addition and negation rules rather than by a
separate estimate. -/
theorem seqTendsto_sub {u v : Nat -> alpha} {a b : alpha}
    (hu : SeqTendsto F u a)
    (hv : SeqTendsto F v b) :
    SeqTendsto F (fun n => F.sub (u n) (v n)) (F.sub a b) := by
  intro eps heps
  have h :=
    seqTendsto_add F hu (seqTendsto_neg F hv) eps heps
  apply Eventually.mono ?_ h
  intro n hn
  change
    F.lt (abs F (F.sub (F.sub (u n) (v n)) (F.sub a b))) eps
  simpa [F.sub_eq_add_neg] using hn

end IsOrderedFieldBaseLike
end Tautology
