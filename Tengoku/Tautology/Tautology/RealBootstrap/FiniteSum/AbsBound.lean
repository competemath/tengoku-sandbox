import Tengoku.Tautology.Tautology.RealBootstrap.Abs
import Tengoku.Tautology.Tautology.RealBootstrap.FiniteSum.Basic

/-!
# The triangle inequality for finite sums

Two theorems: the absolute value of a sum is at most the sum of absolute
values, and a sum is bounded by a sum of pointwise bounds. Separated from
`Tautology.RealBootstrap.FiniteSum.Basic` because they are the only facts about
finite sums that need the absolute value, and that dependency would otherwise
pull `Tautology.RealBootstrap.Abs` into the base of the sum calculus.

## Position and role

Implementation module over an arbitrary ordered field.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem abs_finiteSum_le_finiteSum_abs
    (term : Nat -> alpha) : forall n : Nat,
      F.le (abs F (finiteSum F term n))
        (finiteSum F (fun k : Nat => abs F (term k)) n)
  | 0 => by
      rw [finiteSum_zero, finiteSum_zero]
      rw [abs_zero F]
      exact F.le_refl F.zero
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_succ]
      exact F.le_trans
        (abs_add_le_abs_add_abs F (finiteSum F term n) (term n))
        (add_le_add F
          (abs_finiteSum_le_finiteSum_abs term n)
          (F.le_refl (abs F (term n))))

/-- A uniform pointwise bound `M` on the summands in absolute value bounds
the whole sum by the count of summands times `M`, with the count as the
embedded natural `nat F n`. The nonnegativity hypothesis on `M` is carried by
the statement but not used by the proof. -/
theorem finiteSum_le_of_abs_le
    (term : Nat -> alpha) {M : alpha}
    (hM : F.le F.zero M) :
    forall n : Nat,
      (forall k : Nat, k < n -> F.le (abs F (term k)) M) ->
      F.le
        (abs F (finiteSum F term n))
        (F.mul (nat F n) M)
  | 0, _ => by
      rw [finiteSum_zero]
      change
        F.le (abs F F.zero)
          (F.mul (nat F 0) M)
      rw [abs_zero F]
      rw [nat_zero]
      rw [F.zero_mul]
      exact F.le_refl F.zero
  | n + 1, hbound => by
      have ih :
          F.le
            (abs F (finiteSum F term n))
            (F.mul (nat F n) M) :=
        finiteSum_le_of_abs_le term hM n
          (fun k hk => hbound k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have hlast :
          F.le (abs F (term n)) M :=
        hbound n (Nat.lt_succ_self n)
      have htri :
          F.le
            (abs F (finiteSum F term (n + 1)))
            (F.add
              (abs F (finiteSum F term n))
              (abs F (term n))) := by
        rw [finiteSum_succ]
        exact abs_add_le_abs_add_abs
          F (finiteSum F term n) (term n)
      have hsum :
          F.le
            (F.add
              (abs F (finiteSum F term n))
              (abs F (term n)))
            (F.add (F.mul (nat F n) M) M) :=
        add_le_add F ih hlast
      have htarget :
          F.add (F.mul (nat F n) M) M =
            F.mul (nat F (n + 1)) M := by
        rw [nat_succ]
        change
          F.add (F.mul (nat F n) M) M =
            F.mul (F.add (nat F n) F.one) M
        rw [F.add_mul]
        rw [F.one_mul]
      exact F.le_trans htri (by rwa [htarget] at hsum)

end IsOrderedFieldBaseLike
end Tautology
