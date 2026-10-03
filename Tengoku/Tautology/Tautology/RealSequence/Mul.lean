import Tengoku.Tautology.Tautology.RealBootstrap.StrictOrder
import Tengoku.Tautology.Tautology.RealSequence.Bounded

/-!
# The product rule

A single theorem, and the classical asymmetry of its estimate is kept rather
than smoothed away: the difference is split as
`(u n - a) * v n + a * (v n - b)`, so the first factor's tolerance is divided
in advance by the eventual bound on `v`, while the second is capped by the
constant `|a| + 1`. Each half is then pushed below half the tolerance.

## Position and role

Implementation module, standing on the eventual boundedness of
`Tautology.RealSequence.Bounded`. Over an arbitrary ordered field; completeness
plays no part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Products of convergent sequences converge to the product of the limits.
The classical asymmetry of the estimate is preserved: the second factor only
needs eventual boundedness, the first is driven within a tolerance
pre-divided by that bound, and the constant factor is capped by the a
priori bound `|a| + 1`. The difference splits as
`(u n - a) * v n + a * (v n - b)`, and each part is brought under half the
tolerance. -/
theorem seqTendsto_mul {u v : Nat -> alpha} {a b : alpha}
    (hu : SeqTendsto F u a)
    (hv : SeqTendsto F v b) :
    SeqTendsto F (fun n => F.mul (u n) (v n)) (F.mul a b) := by
  intro eps heps
  let e2 := half F eps
  have he2 : F.lt F.zero e2 :=
    half_pos F heps
  cases seqTendsto_eventuallyBounded F hv with
  | intro B hB =>
      have hBpos : F.lt F.zero B := hB.left
      have hBne : Not (B = F.zero) :=
        pos_ne_zero F hBpos
      let A := F.add (abs F a) F.one
      have hApos : F.lt F.zero A :=
        abs_add_one_pos F a
      have hAne : Not (A = F.zero) :=
        pos_ne_zero F hApos
      let deltaU := F.mul e2 (F.inv B)
      let deltaV := F.mul (F.inv A) e2
      have hdeltaU : F.lt F.zero deltaU := by
        unfold deltaU
        exact mul_pos F he2 (inv_pos F hBpos)
      have hdeltaV : F.lt F.zero deltaV := by
        unfold deltaV
        exact mul_pos F (inv_pos F hApos) he2
      have hscaleU : F.mul deltaU B = e2 := by
        unfold deltaU
        exact mul_inv_mul_cancel_right F e2 hBne
      have hscaleV : F.mul A deltaV = e2 := by
        unfold deltaV
        calc
          F.mul A (F.mul (F.inv A) e2) =
              F.mul (F.mul A (F.inv A)) e2 := by
                rw [<- F.mul_assoc]
          _ = F.mul F.one e2 := by rw [F.mul_inv_cancel hAne]
          _ = e2 := by rw [F.one_mul]
      have hu_delta := hu deltaU hdeltaU
      have hv_delta := hv deltaV hdeltaV
      have hE :=
        Eventually.and (Eventually.and hu_delta hv_delta) hB.right
      apply Eventually.mono ?_ hE
      intro n hn
      have hu_close := hn.left.left
      have hv_close := hn.left.right
      have hv_bound := hn.right
      let t1 := F.mul (F.sub (u n) a) (v n)
      let t2 := F.mul a (F.sub (v n) b)
      have htri :
          F.le
            (abs F (F.sub (F.mul (u n) (v n)) (F.mul a b)))
            (F.add (abs F t1) (abs F t2)) := by
        have h :=
          abs_add_le_abs_add_abs F t1 t2
        unfold t1 at h
        unfold t2 at h
        rwa [<- mul_sub_mul_eq_sub_mul_add_mul_sub F (u n) (v n) a b] at h
      have hterm1 : F.lt (abs F t1) e2 := by
        unfold t1
        rw [abs_mul F (F.sub (u n) a) (v n)]
        have hle :
            F.le
              (F.mul (abs F (F.sub (u n) a)) (abs F (v n)))
              (F.mul (abs F (F.sub (u n) a)) B) :=
          F.mul_le_mul_nonneg_left
            (le_of_lt F hv_bound)
            (abs_nonneg F (F.sub (u n) a))
        have hlt :
            F.lt
              (F.mul (abs F (F.sub (u n) a)) B)
              (F.mul deltaU B) :=
          F.mul_lt_mul_pos_right hu_close hBpos
        have h' : F.lt
            (F.mul (abs F (F.sub (u n) a)) (abs F (v n))) e2 := by
          have h'' := lt_of_le_of_lt F hle hlt
          rwa [hscaleU] at h''
        exact h'
      have hterm2 : F.lt (abs F t2) e2 := by
        unfold t2
        rw [abs_mul F a (F.sub (v n) b)]
        have hAbsA_lt_A : F.lt (abs F a) A := by
          unfold A
          have h := add_lt_add_left F (zero_lt_one F) (abs F a)
          rwa [F.add_zero] at h
        have hle :
            F.le
              (F.mul (abs F a) (abs F (F.sub (v n) b)))
              (F.mul A (abs F (F.sub (v n) b))) :=
          F.mul_le_mul_nonneg_right
            (le_of_lt F hAbsA_lt_A)
            (abs_nonneg F (F.sub (v n) b))
        have hlt :
            F.lt
              (F.mul A (abs F (F.sub (v n) b)))
              (F.mul A deltaV) :=
          F.mul_lt_mul_pos_left hv_close hApos
        have h' : F.lt
            (F.mul (abs F a) (abs F (F.sub (v n) b))) e2 := by
          have h'' := lt_of_le_of_lt F hle hlt
          rwa [hscaleV] at h''
        exact h'
      have hsum :
          F.lt (F.add (abs F t1) (abs F t2)) eps := by
        have h := add_lt_add F hterm1 hterm2
        rwa [half_add_half F eps] at h
      exact lt_of_le_of_lt F htri hsum

end IsOrderedFieldBaseLike
end Tautology
