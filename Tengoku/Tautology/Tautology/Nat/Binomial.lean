import Init.Data.Nat.Lemmas

/-!
# Binomial coefficients, by Pascal's recursion

`binom` is defined by the recursion `binom (n+1) (k+1) = binom n k +
binom n (k+1)` rather than as a quotient of factorials. That is the design
choice this file turns on: the recursive definition stays inside `Nat`, needs
no division and no proof that the division comes out even, so every result
below is ordinary arithmetic. The factorial formula is never needed and never
proved.

The price is that facts which are one line for the quotient have to be earned
by induction. `binom_eq_zero_of_lt` (vanishing above the diagonal),
`binom_self` and `binom_symm_of_le` (symmetry about the middle) are each
proved that way.

## The absorption identity is the hard one, and the reason for the file

`succ_mul_binom_succ` states `(k+1) * binom (n+1) (k+1) = (n+1) * binom n k`.
It is the recursion that lets an index be moved between the coefficient and a
factor outside it, which is what a Leibniz-style product rule needs on
every inductive step -- `Tautology.RealDerivative.Leibniz` is the consumer.
Note it is stated as an equation between products rather than as a quotient,
again to stay inside `Nat`; its proof is the long case analysis at the end of
the file.

## Position in the development

Bottom of the dependency order, on `Nat` alone. Consumers are
`Tautology.RealDerivative.Leibniz` (the higher-order product rule),
`Tautology.RealBootstrap.Bernoulli`,
`Tautology.RealBootstrap.Formal.Bell.ReciprocalPower` and
`Tautology.RealDerivative.Integral.Applications.PiSquaredIrrational`.

## Role

Implementation. There is no `Tautology/Nat.lean` region umbrella; this module
is imported directly by each consumer.
The words this header uses in a sense particular to this library -- region,
route, waist, valve, facade, and the three kinds of aggregation module -- are
each defined once, in the header of the root module `Tautology`. This region
has no umbrella to carry that pointer, so the modules that use the vocabulary
carry it themselves.

-/

namespace Tautology
namespace Nat

/-- Binomial coefficients by Pascal's recursion: `1` in the first column and
at the origin, `0` along the rest of the top row, and inside the recursion
`binom (n + 1) (k + 1) = binom n k + binom n (k + 1)`. No quotient of
factorials is involved anywhere in this file. -/
def binom : _root_.Nat -> _root_.Nat -> _root_.Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_zero_zero :
    binom 0 0 = 1 :=
  rfl

theorem binom_zero_succ (k : _root_.Nat) :
    binom 0 (k + 1) = 0 :=
  rfl

theorem binom_succ_zero (n : _root_.Nat) :
    binom (n + 1) 0 = 1 :=
  rfl

theorem binom_zero (n : _root_.Nat) :
    binom n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ n => exact binom_succ_zero n

theorem binom_succ_succ (n k : _root_.Nat) :
    binom (n + 1) (k + 1) =
      binom n k + binom n (k + 1) :=
  rfl

theorem binom_eq_zero_of_lt :
    forall {n k : _root_.Nat}, n < k -> binom n k = 0
  | 0, 0, h => False.elim ((_root_.Nat.not_lt_zero 0) h)
  | 0, k + 1, _ => rfl
  | n + 1, 0, h =>
      False.elim ((_root_.Nat.not_lt_zero (n + 1)) h)
  | n + 1, k + 1, h => by
      have hnk : n < k := _root_.Nat.lt_of_succ_lt_succ h
      have hnk1 : n < k + 1 :=
        _root_.Nat.lt_trans hnk (_root_.Nat.lt_succ_self k)
      rw [binom_succ_succ]
      rw [binom_eq_zero_of_lt hnk]
      rw [binom_eq_zero_of_lt hnk1]

theorem binom_self :
    forall n : _root_.Nat, binom n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [binom_succ_succ]
      rw [binom_self n]
      have hout : binom n (n + 1) = 0 :=
        binom_eq_zero_of_lt (_root_.Nat.lt_succ_self n)
      rw [hout]

theorem binom_symm_of_le :
    forall {n k : _root_.Nat}, k <= n ->
      binom n k = binom n (n - k)
  | 0, 0, _ => rfl
  | 0, k + 1, h => False.elim (by omega)
  | n + 1, 0, _ => by
      rw [binom_zero]
      rw [_root_.Nat.sub_zero]
      rw [binom_self]
  | n + 1, k + 1, h => by
      by_cases hk : k = n
      · subst k
        rw [binom_self]
        rw [_root_.Nat.sub_self]
        rw [binom_zero]
      · have hkn : k < n := by omega
        have hsub : n + 1 - (k + 1) = n - k := by omega
        have hrepr : n - k = (n - (k + 1)) + 1 := by omega
        rw [binom_succ_succ]
        rw [hsub]
        rw [hrepr]
        rw [binom_succ_succ]
        rw [binom_symm_of_le (n := n) (k := k) (by omega)]
        rw [binom_symm_of_le (n := n) (k := k + 1) (by omega)]
        rw [hrepr]
        rw [_root_.Nat.add_comm]

/-- The absorption identity: for `k <= n`,
`(k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k`. It moves a factor
between the outside of a product and the coefficient within, the manipulation
an inductive Leibniz-style product rule performs at every step. Stated as an
equation of products rather than a quotient, to stay inside `Nat`. -/
theorem succ_mul_binom_succ :
    forall {n k : _root_.Nat}, k <= n ->
      (k + 1) * binom (n + 1) (k + 1) =
        (n + 1) * binom n k
  | 0, 0, _ => rfl
  | 0, k + 1, h => False.elim (by omega)
  | n + 1, 0, _ => by
      have hprev : binom (n + 1) 1 = n + 1 := by
        have hrec :=
          succ_mul_binom_succ
            (n := n) (k := 0) (_root_.Nat.zero_le n)
        simpa [binom_zero] using hrec
      rw [binom_succ_succ]
      rw [binom_zero]
      rw [hprev]
      omega
  | n + 1, k + 1, h => by
      by_cases hk : k = n
      · subst k
        rw [binom_self]
        rw [binom_self]
      · have hkn : k < n := by omega
        let A := binom n k
        let B := binom n (k + 1)
        let U := binom (n + 1) (k + 1)
        let V := binom (n + 1) (k + 2)
        have hU : U = A + B := by
          exact binom_succ_succ n k
        have hleft : (k + 1) * U = (n + 1) * A := by
          exact succ_mul_binom_succ (n := n) (k := k) (by omega)
        have hright : (k + 2) * V = (n + 1) * B := by
          exact succ_mul_binom_succ (n := n) (k := k + 1) (by omega)
        rw [binom_succ_succ]
        change (k + 2) * (U + V) = (n + 2) * U
        calc
          (k + 2) * (U + V) =
              (k + 2) * U + (k + 2) * V := by
                rw [_root_.Nat.mul_add]
          _ = ((k + 1) * U + U) + (k + 2) * V := by
                rw [_root_.Nat.succ_mul]
          _ = ((n + 1) * A + U) + (n + 1) * B := by
                rw [hleft, hright]
          _ = ((n + 1) * A + (n + 1) * B) + U := by
                omega
          _ = (n + 1) * (A + B) + U := by
                rw [_root_.Nat.mul_add]
          _ = (n + 1) * U + U := by
                rw [<- hU]
          _ = (n + 2) * U := by
                exact Eq.symm (_root_.Nat.succ_mul (n + 1) U)

end Nat
end Tautology
