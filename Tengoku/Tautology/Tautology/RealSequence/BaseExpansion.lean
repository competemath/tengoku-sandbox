import Tengoku.Tautology.Tautology.RealSequence.Algebra
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean

/-!
# Powers and tails of a base

The arithmetic floor of the base-expansion cluster: `basePow q n` is `q ^ n`,
`baseTail q n` is `1 / q ^ n`, and the all-maximal truncation has the closed
form `1 - 1 / q ^ n`. Two limit statements follow, that the tails vanish and
that the all-maximal truncations climb to one -- the second being the general
form of `0.999... = 1`.

Note that `baseTail q 0` is `1`, not `0`: the empty truncation still has the
whole unit interval ahead of it. The name reads the other way and has caught
readers out.

Neither limit uses completeness. Both take an `InvNatArchimedeanPrinciple` as
an explicit hypothesis and reach it through the elementary bound `n + 1` at
most `q ^ n`, which pushes `1 / q ^ n` below `1 / (n + 1)`.

## Position and role

Implementation module, the base of the three-file expansion cluster; the other
two are `Tautology.RealSequence.BaseExpansionDigits` and
`Tautology.RealSequence.BaseExpansionExistence`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The power `q ^ n` outgrows `n + 1` whenever the base exceeds one,
with equality at `n = 0`. This Nat-side inequality is the arithmetic
input behind the tail limits of this module and of
`Tautology.RealSequence.BaseExpansionExistence`: it is what lets the
inverse-natural Archimedean principle reach `1 / q ^ n` through
`1 / (N + 1)`. -/
theorem nat_succ_le_pow_of_one_lt {q : Nat}
    (hq : 1 < q) :
    forall n : Nat, n + 1 <= q ^ n := by
  have hq2 : 2 <= q := by omega
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= q * (q ^ n) := Nat.mul_le_mul hq2 ih
        _ = q ^ (n + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]

/-- The `n`-th power of the base as a field element: the natural `q ^ n`
pushed through `nat F`. Its reciprocal is the tail `baseTail`, and
between them the two carry all the scaling in the base-expansion modules. -/
noncomputable def basePow (q n : Nat) : alpha :=
  nat F (q ^ n)

/-- The tail of a base-`q` expansion at stage `n`: the reciprocal `1 / q ^ n`,
the weight still to be distributed over the digits from place `n` onwards.
Downstream, `Tautology.RealNegligibility.CantorSet` reads the base-3 tail as
its stage width and hands the base-2 tail its decay rate. -/
noncomputable def baseTail (q n : Nat) : alpha :=
  F.inv (basePow F q n)

/-- The `n`-th truncation of the all-max digit stream `0.(q-1)(q-1)...`:
one minus the tail, `1 - 1 / q ^ n`. These closed-form partials are what
climb towards one in the limit theorems below. -/
noncomputable def repeatingMaxDigitPartial (q digits : Nat) : alpha :=
  F.sub F.one (baseTail F q digits)

/-- The tails tend to zero, stated with an index shift (`n + 1`); the
unshifted version the rest of the library quotes is
`baseTail_tendsto_zero_all` in `Tautology.RealSequence.BaseExpansionExistence`.
The inverse-natural Archimedean principle arrives as an explicit
hypothesis, and it is genuinely needed: if some positive `eps` bounds
every `1 / (n + 1)` from below, it bounds every `1 / q ^ n` too, since
`q ^ n` is one of the naturals. -/
theorem baseTail_tendsto_zero
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : 1 < q) :
    SeqTendsto F (fun n : Nat => baseTail F q (n + 1)) F.zero := by
  intro eps heps
  cases A.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      let qpow := q ^ (n + 1)
      have hN_le_qpow : N + 1 <= qpow := by
        have hNn : N + 1 <= n + 1 := Nat.succ_le_succ hn
        have hn_succ_le : n + 1 <= n + 1 + 1 := Nat.le_succ (n + 1)
        have hpow : n + 1 + 1 <= q ^ (n + 1) :=
          nat_succ_le_pow_of_one_lt hq (n + 1)
        exact Nat.le_trans (Nat.le_trans hNn hn_succ_le) hpow
      have hqpow_ne : Not (qpow = 0) := by
        intro hzero
        have hbad : N + 1 <= 0 := by
          rwa [hzero] at hN_le_qpow
        omega
      have hNpos : F.lt F.zero (nat F (N + 1)) :=
        nat_succ_pos F N
      have hqpow_pos : F.lt F.zero (nat F qpow) :=
        nat_pos_of_ne_zero F hqpow_ne
      have hle_nat :
          F.le (nat F (N + 1)) (nat F qpow) :=
        nat_le_nat_of_le F hN_le_qpow
      have hle_inv :
          F.le (F.inv (nat F qpow)) (F.inv (nat F (N + 1))) :=
        inv_le_inv_of_le_pos F hNpos hqpow_pos hle_nat
      have hinv_pos : F.lt F.zero (F.inv (nat F qpow)) :=
        inv_pos F hqpow_pos
      have habs :
          abs F (F.sub (baseTail F q (n + 1)) F.zero) =
            F.inv (nat F qpow) := by
        unfold baseTail basePow
        dsimp [qpow]
        rw [sub_zero F]
        exact abs_of_nonneg F (le_of_lt F hinv_pos)
      rw [habs]
      exact lt_of_le_of_lt F hle_inv hN

/-- The all-max truncations climb to one: `1 - 1 / q ^ (n + 1)` tends to
`1`. This is the general-base form of the repeating-nines limit; the
decimal case is packaged separately below. -/
theorem repeatingMaxDigitPartial_tendsto_one
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : 1 < q) :
    SeqTendsto F
      (fun n : Nat => repeatingMaxDigitPartial F q (n + 1))
      F.one := by
  change
    SeqTendsto F
      (fun n : Nat => F.sub F.one (baseTail F q (n + 1)))
      F.one
  have hconst : SeqTendsto F (fun _ : Nat => F.one) F.one :=
    seqTendsto_const F F.one
  have htail : SeqTendsto F (fun n : Nat => baseTail F q (n + 1)) F.zero :=
    baseTail_tendsto_zero F A hq
  have hsub := seqTendsto_sub F hconst htail
  change
    SeqTendsto F
      (fun n : Nat => F.sub F.one (baseTail F q (n + 1)))
      (F.sub F.one F.zero) at hsub
  rwa [sub_zero F] at hsub

/-- The repeating-nines identity, in the only shape this library can
state it: there is no infinite-sum vocabulary here, so `0.999... = 1` is
the convergence of the finite decimals `0.9...9` towards `1`. The base
is fixed at ten. -/
theorem zero_point_repeating_nines_eq_one
    (A : F.InvNatArchimedeanPrinciple) :
    SeqTendsto F
      (fun n : Nat => repeatingMaxDigitPartial F 10 (n + 1))
      F.one :=
  repeatingMaxDigitPartial_tendsto_one F A (by omega)

end IsOrderedFieldBaseLike
end Tautology
