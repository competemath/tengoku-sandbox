import Tengoku.Tautology.Tautology.RealSequence.Order

/-!
# Eventual boundedness, and staying away from zero

Two tail predicates and the chain between them. A convergent sequence is
eventually bounded, with the explicit bound `|a| + 1` rather than an existence
statement; and a sequence converging to a nonzero limit eventually stays above
`|a| / 2` in absolute value, hence is eventually nonzero, which is what makes
its reciprocal defined on a tail.

Both exist to supply hypotheses to `Tautology.RealSequence.Mul` and
`Tautology.RealSequence.InvDiv`; they are stated eventually rather than
globally because that is exactly what those proofs need.

## Position and role

Implementation module over an arbitrary ordered field; completeness plays no
part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Boundedness demanded only of a tail: some positive `B` with `|u n| < B`
from some index on. Weaker than the all-index boundedness of
`Tautology.RealSequence.Basic`, and all that the product and reciprocal rules
need, since their estimates control tails. -/
def EventuallyBounded (u : Nat -> alpha) : Prop :=
  Exists
    (fun B : alpha =>
      And (F.lt F.zero B)
        (Eventually (fun n : Nat => F.lt (abs F (u n)) B)))

/-- The tail stays clear of zero: some positive `c` with `c < |u n|`
eventually. This is the hypothesis shape the reciprocal rule needs; when the
sequence converges to a nonzero limit, half the absolute value of the limit
serves as `c`. -/
def EventuallyAwayFromZero (u : Nat -> alpha) : Prop :=
  Exists
    (fun c : alpha =>
      And (F.lt F.zero c)
        (Eventually (fun n : Nat => F.lt c (abs F (u n)))))

/-- A convergent sequence is eventually bounded. The bound is produced
explicitly, `|a| + 1`, from the convergence window at tolerance one, so no
existential search over bounds happens anywhere. -/
theorem seqTendsto_eventuallyBounded {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a) :
    EventuallyBounded F u := by
  let B := F.add (abs F a) F.one
  refine Exists.intro B ?_
  constructor
  · exact abs_add_one_pos F a
  · have hclose := hu F.one (zero_lt_one F)
    apply Eventually.mono ?_ hclose
    intro n hn
    have htri :
        F.le (abs F (u n))
          (F.add (abs F (F.sub (u n) a)) (abs F a)) := by
      have h :=
        abs_add_le_abs_add_abs F (F.sub (u n) a) a
      rwa [sub_add_cancel F (u n) a] at h
    have hsum :
        F.lt
          (F.add (abs F (F.sub (u n) a)) (abs F a))
          B := by
      have h := add_lt_add_right F hn (abs F a)
      rwa [F.add_comm F.one (abs F a)] at h
    exact lt_of_le_of_lt F htri hsum

/-- A sequence converging to a nonzero `a` eventually satisfies
`|a| / 2 < |u n|`. The constant is half of `|a|` precisely so that its
reciprocal bounds the reciprocal terms in `Tautology.RealSequence.InvDiv`; the
window is split out as its own lemma because that module quotes it verbatim. -/
theorem seqTendsto_eventually_half_abs_lt_abs {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a)
    (ha : Not (a = F.zero)) :
    Eventually
      (fun n : Nat => F.lt (half F (abs F a)) (abs F (u n))) := by
  let c := half F (abs F a)
  have habs_pos : F.lt F.zero (abs F a) :=
    abs_pos_of_ne_zero F ha
  have hcpos : F.lt F.zero c :=
    half_pos F habs_pos
  have hclose := hu c hcpos
  apply Eventually.mono ?_ hclose
  intro n hn
  have hclose' : F.lt (abs F (F.sub a (u n))) c := by
    simpa [abs_sub_comm F a (u n)] using hn
  have htri :
      F.le (abs F a)
        (F.add (abs F (F.sub a (u n))) (abs F (u n))) := by
    have h :=
      abs_add_le_abs_add_abs F (F.sub a (u n)) (u n)
    rwa [sub_add_cancel F a (u n)] at h
  have hsum :
      F.lt (abs F a) (F.add c (abs F (u n))) := by
    exact lt_of_le_of_lt F htri
      (add_lt_add_right F hclose' (abs F (u n)))
  have hsum_comm : F.lt (abs F a) (F.add (abs F (u n)) c) := by
    rwa [F.add_comm c (abs F (u n))] at hsum
  have hdiff : F.lt (F.sub (abs F a) (abs F (u n))) c :=
    sub_lt_of_lt_add F hsum_comm
  have haway : F.lt (F.sub (abs F a) c) (abs F (u n)) :=
    sub_lt_of_lt_right F hdiff
  rwa [sub_half_self F (abs F a)] at haway

/-- Existential packaging of the preceding window: convergence to a nonzero
limit gives `EventuallyAwayFromZero`, with witness half the absolute value
of the limit. -/
theorem seqTendsto_eventuallyAwayFromZero {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a)
    (ha : Not (a = F.zero)) :
    EventuallyAwayFromZero F u := by
  refine Exists.intro (half F (abs F a)) ?_
  constructor
  · exact half_pos F (abs_pos_of_ne_zero F ha)
  · exact seqTendsto_eventually_half_abs_lt_abs F hu ha

/-- Eventually the terms are literally nonzero, so termwise reciprocals are
defined on a tail. Strictly weaker information than the window above, and
exactly what forming those reciprocals needs. -/
theorem seqTendsto_eventually_ne_zero {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a)
    (ha : Not (a = F.zero)) :
    Eventually (fun n : Nat => Not (u n = F.zero)) := by
  cases seqTendsto_eventuallyAwayFromZero F hu ha with
  | intro c hc =>
      apply Eventually.mono ?_ hc.right
      intro n hn hzero
      have hzero_abs : abs F (u n) = F.zero := by
        rw [hzero]
        exact abs_zero F
      rw [hzero_abs] at hn
      exact (lt_irrefl F F.zero) (lt_trans F hc.left hn)

end IsOrderedFieldBaseLike
end Tautology
