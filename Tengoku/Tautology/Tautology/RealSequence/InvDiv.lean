import Tengoku.Tautology.Tautology.RealSequence.Mul

/-!
# Reciprocals and quotients

The remaining limit rules. Both rest on a sequence with nonzero limit staying
away from zero on a tail (`Tautology.RealSequence.Bounded`), which is what
makes the reciprocal defined there at all, and on the identity
`1 / x - 1 / a = -((x - a) * (1 / x)) * (1 / a)`, which converts a difference
of reciprocals into a difference of the originals scaled by two bounded
factors.

The quotient rule is the product rule applied to the reciprocal, not a separate
argument.

## Position and role

Implementation module over an arbitrary ordered field; completeness plays no
part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Inversion inverts magnitudes: for positive `c`, the bound `c < |x|`
gives `|1 / x| < 1 / c`. The pointwise fact that turns an away-from-zero
window into a bound on reciprocals. -/
theorem abs_inv_lt_inv_of_pos_lt_abs {c x : alpha}
    (hc : F.lt F.zero c)
    (hcx : F.lt c (abs F x)) :
    F.lt (abs F (F.inv x)) (F.inv c) := by
  have hxne : Not (x = F.zero) := by
    intro hx
    rw [hx, abs_zero F] at hcx
    exact (lt_irrefl F F.zero) (lt_trans F hc hcx)
  have hinvne : Not (F.inv x = F.zero) :=
    inv_ne_zero_of_ne_zero F hxne
  have habsinv_pos : F.lt F.zero (abs F (F.inv x)) :=
    abs_pos_of_ne_zero F hinvne
  have hprod_lt :
      F.lt
        (F.mul c (abs F (F.inv x)))
        (F.mul (abs F x) (abs F (F.inv x))) :=
    F.mul_lt_mul_pos_right hcx habsinv_pos
  have hright :
      F.mul (abs F x) (abs F (F.inv x)) = F.one := by
    calc
      F.mul (abs F x) (abs F (F.inv x)) =
          F.mul (abs F (F.inv x)) (abs F x) := by
            rw [F.mul_comm]
      _ = abs F (F.mul (F.inv x) x) := by
            rw [abs_mul F (F.inv x) x]
      _ = abs F F.one := by rw [F.inv_mul_cancel hxne]
      _ = F.one := abs_one F
  have hprod_one :
      F.lt (F.mul c (abs F (F.inv x))) F.one := by
    rwa [hright] at hprod_lt
  have hscaled :=
    F.mul_lt_mul_pos_left hprod_one (inv_pos F hc)
  have hleft :
      F.mul (F.inv c) (F.mul c (abs F (F.inv x))) =
        abs F (F.inv x) := by
    calc
      F.mul (F.inv c) (F.mul c (abs F (F.inv x))) =
          F.mul (F.mul (F.inv c) c) (abs F (F.inv x)) := by
            rw [<- F.mul_assoc]
      _ = F.mul F.one (abs F (F.inv x)) := by
            rw [F.inv_mul_cancel (pos_ne_zero F hc)]
      _ = abs F (F.inv x) := by rw [F.one_mul]
  have hright_scaled :
      F.mul (F.inv c) F.one = F.inv c := by
    rw [F.mul_one]
  rwa [hleft, hright_scaled] at hscaled

/-- The difference of reciprocals, reshaped as a product: `1 / x - 1 / a`
equals the negation of `(x - a)` times the two reciprocals. Rewriting the
left side into one difference multiplied by two bounded factors is the
entire mechanism of the reciprocal limit rule below. -/
theorem inv_sub_inv_eq_neg_sub_mul_inv_mul_inv {x a : alpha}
    (hx : Not (x = F.zero))
    (ha : Not (a = F.zero)) :
    F.sub (F.inv x) (F.inv a) =
      F.neg
        (F.mul (F.mul (F.sub x a) (F.inv x)) (F.inv a)) := by
  have hcore :
      F.mul (F.mul (F.inv x) (F.sub x a)) (F.inv a) =
        F.sub (F.inv a) (F.inv x) := by
    rw [F.sub_eq_add_neg x a]
    rw [F.mul_add]
    rw [F.inv_mul_cancel hx]
    rw [F.mul_neg]
    rw [F.add_mul]
    rw [F.one_mul]
    rw [neg_mul F (F.mul (F.inv x) a) (F.inv a)]
    have hright :
        F.mul (F.mul (F.inv x) a) (F.inv a) = F.inv x := by
      calc
        F.mul (F.mul (F.inv x) a) (F.inv a) =
            F.mul (F.inv x) (F.mul a (F.inv a)) := by
              rw [F.mul_assoc]
        _ = F.mul (F.inv x) F.one := by rw [F.mul_inv_cancel ha]
        _ = F.inv x := by rw [F.mul_one]
    rw [hright]
    rw [F.sub_eq_add_neg]
  calc
    F.sub (F.inv x) (F.inv a) =
        F.neg (F.sub (F.inv a) (F.inv x)) := by
          rw [sub_rev_eq_neg_sub F (F.inv a) (F.inv x)]
    _ = F.neg
        (F.mul (F.mul (F.inv x) (F.sub x a)) (F.inv a)) := by
          rw [hcore]
    _ = F.neg
        (F.mul (F.mul (F.sub x a) (F.inv x)) (F.inv a)) := by
          rw [F.mul_comm (F.inv x) (F.sub x a)]

/-- The reciprocal rule: a sequence converging to a nonzero limit has
reciprocals converging to the reciprocal of the limit. On the tail where
`|u n|` exceeds half of `|a|`, both reciprocal factors are bounded by the
same constant, and the tolerance is pre-divided by its square, so the
product estimate closes without computing any new limit. -/
theorem seqTendsto_inv {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a)
    (ha : Not (a = F.zero)) :
    SeqTendsto F (fun n => F.inv (u n)) (F.inv a) := by
  intro eps heps
  let c := half F (abs F a)
  have habs_pos : F.lt F.zero (abs F a) :=
    abs_pos_of_ne_zero F ha
  have hcpos : F.lt F.zero c :=
    half_pos F habs_pos
  have hc_abs_a : F.lt c (abs F a) :=
    half_lt_self F habs_pos
  let K := F.inv c
  have hKpos : F.lt F.zero K :=
    inv_pos F hcpos
  let scale := F.mul K K
  have hscale_pos : F.lt F.zero scale := by
    unfold scale
    exact mul_pos F hKpos hKpos
  have hscale_ne : Not (scale = F.zero) :=
    pos_ne_zero F hscale_pos
  let delta := F.mul eps (F.inv scale)
  have hdelta : F.lt F.zero delta := by
    unfold delta
    exact mul_pos F heps (inv_pos F hscale_pos)
  have hdelta_scale : F.mul delta scale = eps := by
    unfold delta
    exact mul_inv_mul_cancel_right F eps hscale_ne
  have hclose := hu delta hdelta
  have haway := seqTendsto_eventually_half_abs_lt_abs F hu ha
  have hnonzero := seqTendsto_eventually_ne_zero F hu ha
  have hE := Eventually.and (Eventually.and hclose haway) hnonzero
  apply Eventually.mono ?_ hE
  intro n hn
  have hcloseN := hn.left.left
  have hawayN := hn.left.right
  have hneN := hn.right
  have hInvU : F.lt (abs F (F.inv (u n))) K := by
    unfold K
    exact abs_inv_lt_inv_of_pos_lt_abs F hcpos hawayN
  have hInvA : F.lt (abs F (F.inv a)) K := by
    unfold K
    exact abs_inv_lt_inv_of_pos_lt_abs F hcpos hc_abs_a
  have hidentity :=
    inv_sub_inv_eq_neg_sub_mul_inv_mul_inv F hneN ha
  have habs_identity :
      abs F (F.sub (F.inv (u n)) (F.inv a)) =
        F.mul
          (F.mul (abs F (F.sub (u n) a)) (abs F (F.inv (u n))))
          (abs F (F.inv a)) := by
    rw [hidentity]
    rw [abs_neg F
      (F.mul (F.mul (F.sub (u n) a) (F.inv (u n))) (F.inv a))]
    rw [abs_mul F (F.mul (F.sub (u n) a) (F.inv (u n))) (F.inv a)]
    rw [abs_mul F (F.sub (u n) a) (F.inv (u n))]
  rw [habs_identity]
  let D := abs F (F.sub (u n) a)
  let IU := abs F (F.inv (u n))
  let IA := abs F (F.inv a)
  have hIUle : F.le IU K := by
    exact le_of_lt F hInvU
  have hIAle : F.le IA K := by
    exact le_of_lt F hInvA
  have hDnonneg : F.le F.zero D := by
    unfold D
    exact abs_nonneg F (F.sub (u n) a)
  have hKnonneg : F.le F.zero K :=
    le_of_lt F hKpos
  have hDKnonneg : F.le F.zero (F.mul D K) :=
    F.mul_nonneg hDnonneg hKnonneg
  have hle1 : F.le (F.mul D IU) (F.mul D K) :=
    F.mul_le_mul_nonneg_left hIUle hDnonneg
  have hle2 :
      F.le (F.mul (F.mul D IU) IA) (F.mul (F.mul D K) IA) :=
    F.mul_le_mul_nonneg_right hle1 (abs_nonneg F (F.inv a))
  have hle3 :
      F.le (F.mul (F.mul D K) IA) (F.mul (F.mul D K) K) :=
    F.mul_le_mul_nonneg_left hIAle hDKnonneg
  have hle :
      F.le (F.mul (F.mul D IU) IA) (F.mul (F.mul D K) K) :=
    F.le_trans hle2 hle3
  have hlt :
      F.lt (F.mul (F.mul D K) K) eps := by
    have hDK_lt : F.lt (F.mul D K) (F.mul delta K) :=
      F.mul_lt_mul_pos_right hcloseN hKpos
    have hDKK_lt :
        F.lt (F.mul (F.mul D K) K) (F.mul (F.mul delta K) K) :=
      F.mul_lt_mul_pos_right hDK_lt hKpos
    have hright :
        F.mul (F.mul delta K) K = eps := by
      calc
        F.mul (F.mul delta K) K =
            F.mul delta (F.mul K K) := by rw [F.mul_assoc]
        _ = F.mul delta scale := rfl
        _ = eps := hdelta_scale
    rwa [hright] at hDKK_lt
  exact lt_of_le_of_lt F hle hlt

/-- The quotient rule, composed from the product rule and the reciprocal
rule rather than proved by a separate estimate. The only hypothesis beyond
the two convergences is that the limit of the denominator is nonzero. -/
theorem seqTendsto_div {u v : Nat -> alpha} {a b : alpha}
    (hu : SeqTendsto F u a)
    (hv : SeqTendsto F v b)
    (hb : Not (b = F.zero)) :
    SeqTendsto F
      (fun n => F.mul (u n) (F.inv (v n)))
      (F.mul a (F.inv b)) :=
  seqTendsto_mul F hu (seqTendsto_inv F hv hb)

end IsOrderedFieldBaseLike
end Tautology
