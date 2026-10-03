import Tengoku.Tautology.Tautology.Nat.Binomial
import Tengoku.Tautology.Tautology.RealBootstrap.FiniteSum

/-!
# Bernoulli numbers and polynomials

The recursive definition of the Bernoulli numbers, the polynomial values built
from them, and the two facts the library later needs: the reflection symmetry
about the midpoint, which forces the odd-index numbers past the first to
vanish, and an explicit envelope bounding the polynomial values on the unit
interval.

The proportions of the file are worth noting -- more than two thousand lines
support sixteen public declarations, the rest being private. The public surface
is deliberately narrow: consumers upstream want the recurrence, the low-index
values, the vanishing, and the envelope, and nothing about how the binomial
bookkeeping is organised.

Everything is finite arithmetic over an arbitrary ordered field. No limit, no
completeness, no generating function appears; the envelope is the analytic
input that the Euler-Maclaurin development far above will use, and it is proved
here by elementary estimates.

## Position and role

Implementation module built on `Tautology.RealBootstrap.FiniteSum` and the
binomial coefficients of `Tautology.Nat.Binomial`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

private def bernoulliStep (n : Nat)
    (previous : (k : Nat) -> k < n -> alpha) : alpha :=
  match n with
  | 0 => F.one
  | m + 1 =>
      F.neg (F.mul (F.inv (nat F (m + 2)))
        (finiteSum F
          (fun k : Nat =>
            if hk : k < m + 1 then
              F.mul (nat F (Tautology.Nat.binom (m + 2) k))
                (previous k hk)
            else
              F.zero)
          (m + 1)))

/-- The `n`-th Bernoulli number, defined by strong recursion on the index:
`B 0` is one, and each later `B (m + 1)` is the value that makes the
binomially weighted sum of the earlier numbers vanish, solved for its last
summand. The recursion runs through `Nat.strongRecOn`, so the two defining
equations do not hold by `rfl`; they are exported separately as
`bernoulliNumber_zero` and `bernoulliNumber_succ`. -/
noncomputable def bernoulliNumber (n : Nat) : alpha :=
  Nat.strongRecOn n (bernoulliStep F)

theorem bernoulliNumber_zero :
    bernoulliNumber F 0 = F.one := by
  unfold bernoulliNumber Nat.strongRecOn
  rw [WellFounded.fix_eq]
  rfl

/-- The defining recursion at a successor, as an equation to rewrite with.
Every computation of a Bernoulli number enters here, because the
`Nat.strongRecOn` definition does not unfold on its own. -/
theorem bernoulliNumber_succ (n : Nat) :
    bernoulliNumber F (n + 1) =
      F.neg (F.mul (F.inv (nat F (n + 2)))
        (finiteSum F
          (fun k : Nat =>
            F.mul (nat F (Tautology.Nat.binom (n + 2) k))
              (bernoulliNumber F k))
          (n + 1))) := by
  unfold bernoulliNumber Nat.strongRecOn
  rw [WellFounded.fix_eq]
  change
    F.neg (F.mul (F.inv (nat F (n + 2)))
        (finiteSum F
          (fun k : Nat =>
            if hk : k < n + 1 then
              F.mul (nat F (Tautology.Nat.binom (n + 2) k))
                ((Nat.lt_wfRel.wf.fix (bernoulliStep F)) k)
            else
              F.zero)
          (n + 1))) = _
  congr 2
  apply finiteSum_congr_lt F
  intro k hk
  simp only [dite_eq_left hk]

private theorem binom_succ_pred :
    forall n : Nat,
      Tautology.Nat.binom (n + 1) n = n + 1
  | 0 => rfl
  | n + 1 => by
      rw [Tautology.Nat.binom_succ_succ]
      rw [binom_succ_pred n]
      rw [Tautology.Nat.binom_self]

/-- The defining identity in its symmetric form: the binomially weighted sum
of the numbers up to `n` vanishes, for every positive `n`. The definition is
this equation solved for the last summand, so the identity is a consequence
of it rather than the definition itself; `n = 0` is excluded because the sum
there is `B 0 = 1`. -/
theorem bernoulli_recurrence {n : Nat} (hn : 0 < n) :
    finiteSum F
      (fun k : Nat =>
        F.mul (nat F (Tautology.Nat.binom (n + 1) k))
          (bernoulliNumber F k))
      (n + 1) = F.zero := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 hn)
  | succ m =>
      rw [finiteSum_succ]
      rw [binom_succ_pred (m + 1)]
      rw [bernoulliNumber_succ F m]
      let S : alpha :=
        finiteSum F
          (fun k : Nat =>
            F.mul (nat F (Tautology.Nat.binom (m + 2) k))
              (bernoulliNumber F k))
          (m + 1)
      change
        F.add S
          (F.mul (nat F (m + 2))
            (F.neg (F.mul (F.inv (nat F (m + 2))) S))) = F.zero
      rw [mul_neg F]
      rw [<- F.mul_assoc]
      rw [F.mul_inv_cancel (nat_ne_zero_of_ne_zero F (by omega))]
      rw [F.one_mul]
      rw [F.add_neg]

/-- The first Bernoulli number is `-1 / 2`. It is the only odd-indexed number
with a nonzero value; every later odd index vanishes, by
`bernoulliNumber_odd_eq_zero` below. -/
theorem bernoulliNumber_one :
    bernoulliNumber F 1 = F.neg (F.inv (nat F 2)) := by
  rw [bernoulliNumber_succ F 0]
  rw [finiteSum_one]
  rw [Tautology.Nat.binom_zero]
  rw [nat_one]
  rw [bernoulliNumber_zero]
  rw [F.one_mul]
  rw [F.mul_one]

private theorem one_add_three_mul_neg_inv_two :
    F.add F.one
        (F.mul (nat F 3) (F.neg (F.inv (nat F 2)))) =
      F.neg (F.inv (nat F 2)) := by
  rw [mul_neg F]
  rw [nat_succ F 2]
  rw [F.add_mul]
  rw [F.mul_inv_cancel (nat_ne_zero_of_ne_zero F (by omega))]
  rw [F.one_mul]
  rw [neg_add_distrib F]
  rw [<- F.add_assoc]
  rw [F.add_neg]
  rw [F.zero_add]

theorem bernoulliNumber_two :
    bernoulliNumber F 2 = F.inv (nat F 6) := by
  rw [bernoulliNumber_succ F 1]
  rw [finiteSum_succ]
  rw [finiteSum_one]
  change
    F.neg (F.mul (F.inv (nat F 3))
      (F.add
        (F.mul (nat F (Tautology.Nat.binom 3 0))
          (bernoulliNumber F 0))
        (F.mul (nat F (Tautology.Nat.binom 3 1))
          (bernoulliNumber F 1)))) = F.inv (nat F 6)
  rw [Tautology.Nat.binom_zero]
  change
    F.neg (F.mul (F.inv (nat F 3))
      (F.add
        (F.mul (nat F 1) (bernoulliNumber F 0))
        (F.mul (nat F 3) (bernoulliNumber F 1)))) = F.inv (nat F 6)
  rw [nat_one]
  rw [bernoulliNumber_zero]
  rw [bernoulliNumber_one]
  rw [F.one_mul]
  rw [one_add_three_mul_neg_inv_two]
  rw [mul_neg F]
  rw [neg_neg F]
  have h2 : Not (nat F 2 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  have h3 : Not (nat F 3 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  calc
    F.mul (F.inv (nat F 3)) (F.inv (nat F 2)) =
        F.inv (F.mul (nat F 2) (nat F 3)) := by
          exact Eq.symm (inv_mul F h2 h3)
    _ = F.inv (nat F 6) := by
          rw [<- nat_mul F 2 3]

private theorem four_mul_inv_two_eq_two :
    F.mul (nat F 4) (F.inv (nat F 2)) = nat F 2 := by
  have h2 : Not (nat F 2 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  calc
    F.mul (nat F 4) (F.inv (nat F 2)) =
        F.mul (F.mul (nat F 2) (nat F 2))
          (F.inv (nat F 2)) := by
            rw [<- nat_mul F 2 2]
    _ = F.mul (nat F 2)
          (F.mul (nat F 2) (F.inv (nat F 2))) := by
            rw [F.mul_assoc]
    _ = F.mul (nat F 2) F.one := by
            rw [F.mul_inv_cancel h2]
    _ = nat F 2 := by rw [F.mul_one]

private theorem bernoulli_three_inner_zero :
    F.add
        (F.add F.one
          (F.mul (nat F 4) (F.neg (F.inv (nat F 2)))))
        (F.mul (nat F 6) (F.inv (nat F 6))) =
      F.zero := by
  rw [mul_neg F]
  rw [four_mul_inv_two_eq_two]
  rw [F.mul_inv_cancel (nat_ne_zero_of_ne_zero F (by omega))]
  rw [nat_succ F 1]
  rw [nat_one]
  rw [neg_add_distrib F]
  calc
    F.add
        (F.add F.one (F.add (F.neg F.one) (F.neg F.one)))
        F.one =
        F.add
          (F.add (F.add F.one (F.neg F.one)) (F.neg F.one))
          F.one := by
            congr 1
            exact Eq.symm
              (F.add_assoc F.one (F.neg F.one) (F.neg F.one))
    _ = F.add (F.add F.one (F.neg F.one))
          (F.add (F.neg F.one) F.one) := by
            exact F.add_assoc
              (F.add F.one (F.neg F.one)) (F.neg F.one) F.one
    _ = F.add F.zero F.zero := by
            rw [F.add_neg, F.neg_add]
    _ = F.zero := by rw [F.zero_add]

/-- The third Bernoulli number is zero, by direct computation from the
recursion. The general vanishing theorem `bernoulliNumber_odd_eq_zero` below
recovers it as its `r = 1` case. -/
theorem bernoulliNumber_three :
    bernoulliNumber F 3 = F.zero := by
  rw [bernoulliNumber_succ F 2]
  rw [finiteSum_succ]
  rw [finiteSum_succ]
  rw [finiteSum_one]
  change
    F.neg (F.mul (F.inv (nat F 4))
      (F.add
        (F.add
          (F.mul (nat F 1) (bernoulliNumber F 0))
          (F.mul (nat F 4) (bernoulliNumber F 1)))
        (F.mul (nat F 6) (bernoulliNumber F 2)))) = F.zero
  rw [nat_one]
  rw [bernoulliNumber_zero]
  rw [bernoulliNumber_one]
  rw [bernoulliNumber_two]
  rw [F.one_mul]
  rw [bernoulli_three_inner_zero]
  rw [F.mul_zero]
  rw [neg_zero F]

private theorem six_mul_five_mul_inv_two_eq_fifteen :
    F.mul (nat F 6)
        (F.mul (nat F 5) (F.inv (nat F 2))) =
      nat F 15 := by
  have h2 : Not (nat F 2 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  calc
    F.mul (nat F 6)
        (F.mul (nat F 5) (F.inv (nat F 2))) =
        F.mul (F.mul (nat F 6) (nat F 5))
          (F.inv (nat F 2)) := by
            rw [F.mul_assoc]
    _ = F.mul (nat F (6 * 5)) (F.inv (nat F 2)) := by
            rw [nat_mul]
    _ = F.mul (nat F (15 * 2)) (F.inv (nat F 2)) := by
            rfl
    _ = F.mul (F.mul (nat F 15) (nat F 2))
          (F.inv (nat F 2)) := by
            rw [nat_mul]
    _ = F.mul (nat F 15)
          (F.mul (nat F 2) (F.inv (nat F 2))) := by
            rw [F.mul_assoc]
    _ = F.mul (nat F 15) F.one := by
            rw [F.mul_inv_cancel h2]
    _ = nat F 15 := by rw [F.mul_one]

private theorem six_mul_ten_mul_inv_six_eq_ten :
    F.mul (nat F 6)
        (F.mul (nat F 10) (F.inv (nat F 6))) =
      nat F 10 := by
  have h6 : Not (nat F 6 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  calc
    F.mul (nat F 6)
        (F.mul (nat F 10) (F.inv (nat F 6))) =
        F.mul (nat F 10)
          (F.mul (nat F 6) (F.inv (nat F 6))) := by
            rw [<- F.mul_assoc]
            rw [F.mul_comm (nat F 6) (nat F 10)]
            rw [F.mul_assoc]
    _ = F.mul (nat F 10) F.one := by
            rw [F.mul_inv_cancel h6]
    _ = nat F 10 := by rw [F.mul_one]

private theorem bernoulli_four_inner_eq_inv_six :
    F.add
        (F.add F.one
          (F.mul (nat F 5) (F.neg (F.inv (nat F 2)))))
        (F.mul (nat F 10) (F.inv (nat F 6))) =
      F.inv (nat F 6) := by
  have h6 : Not (nat F 6 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  apply eq_inv_of_mul_eq_one_left F h6
  rw [F.mul_add]
  rw [F.mul_add]
  rw [F.mul_one]
  rw [mul_neg F]
  rw [mul_neg F]
  rw [six_mul_five_mul_inv_two_eq_fifteen]
  rw [six_mul_ten_mul_inv_six_eq_ten]
  calc
    F.add (F.add (nat F 6) (F.neg (nat F 15))) (nat F 10) =
        F.add (F.add (nat F 6) (nat F 10))
          (F.neg (nat F 15)) := by
            rw [F.add_assoc]
            rw [F.add_comm (F.neg (nat F 15)) (nat F 10)]
            rw [<- F.add_assoc]
    _ = F.add (nat F 16) (F.neg (nat F 15)) := by
            rw [<- nat_add]
    _ = F.add (F.add (nat F 15) F.one)
          (F.neg (nat F 15)) := by
            rw [nat_succ]
    _ = F.add (nat F 15)
          (F.add F.one (F.neg (nat F 15))) := by
            rw [F.add_assoc]
    _ = F.add (nat F 15)
          (F.add (F.neg (nat F 15)) F.one) := by
            rw [F.add_comm F.one (F.neg (nat F 15))]
    _ = F.add (F.add (nat F 15) (F.neg (nat F 15)))
          F.one := by
            rw [F.add_assoc]
    _ = F.one := by rw [F.add_neg, F.zero_add]

theorem bernoulliNumber_four :
    bernoulliNumber F 4 = F.neg (F.inv (nat F 30)) := by
  rw [bernoulliNumber_succ F 3]
  rw [finiteSum_succ]
  rw [finiteSum_succ]
  rw [finiteSum_succ]
  rw [finiteSum_one]
  change
    F.neg (F.mul (F.inv (nat F 5))
      (F.add
        (F.add
          (F.add
            (F.mul (nat F 1) (bernoulliNumber F 0))
            (F.mul (nat F 5) (bernoulliNumber F 1)))
          (F.mul (nat F 10) (bernoulliNumber F 2)))
        (F.mul (nat F 10) (bernoulliNumber F 3)))) =
      F.neg (F.inv (nat F 30))
  rw [nat_one]
  rw [bernoulliNumber_zero]
  rw [bernoulliNumber_one]
  rw [bernoulliNumber_two]
  rw [bernoulliNumber_three]
  rw [F.one_mul]
  rw [F.mul_zero]
  rw [F.add_zero]
  rw [bernoulli_four_inner_eq_inv_six]
  congr 1
  have h5 : Not (nat F 5 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  have h6 : Not (nat F 6 = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  calc
    F.mul (F.inv (nat F 5)) (F.inv (nat F 6)) =
        F.inv (F.mul (nat F 6) (nat F 5)) := by
          exact Eq.symm (inv_mul F h6 h5)
    _ = F.inv (nat F 30) := by
          rw [<- nat_mul F 6 5]

private abbrev bernoulliPower
    (x : alpha) (n : Nat) : alpha :=
  Nat.rec F.one (fun _ previous => F.mul x previous) n

private theorem bernoulliPower_zero (x : alpha) :
    bernoulliPower F x 0 = F.one :=
  rfl

private theorem bernoulliPower_succ (x : alpha) (n : Nat) :
    bernoulliPower F x (n + 1) =
      F.mul x (bernoulliPower F x n) :=
  rfl

private theorem bernoulliPower_zero_succ (n : Nat) :
    bernoulliPower F F.zero (n + 1) = F.zero := by
  rw [bernoulliPower_succ]
  rw [zero_mul F]

private theorem bernoulliPower_one :
    forall n : Nat, bernoulliPower F F.one n = F.one
  | 0 => rfl
  | n + 1 => by
      rw [bernoulliPower_succ]
      rw [bernoulliPower_one n]
      rw [F.one_mul]

/-- The value of the `m`-th Bernoulli polynomial at `t`: the binomial expansion
with Bernoulli-number coefficients, `B k` times `t ^ (m - k)`, summed over
`k <= m`. Only values are formalised -- the polynomial is never an object at
this depth of the library, and the powers are a private `Nat.rec` iteration --
so a polynomial value is literally a finite sum and the whole calculus of
`Tautology.RealBootstrap.FiniteSum.Basic` applies to it. -/
noncomputable def bernoulliPolynomialValue (m : Nat) (t : alpha) : alpha :=
  finiteSum F
    (fun k : Nat =>
      F.mul
        (F.mul (nat F (Tautology.Nat.binom m k))
          (bernoulliNumber F k))
        (bernoulliPower F t (m - k)))
    (m + 1)

theorem bernoulliPolynomialValue_zero (m : Nat) :
    bernoulliPolynomialValue F m F.zero = bernoulliNumber F m := by
  unfold bernoulliPolynomialValue
  rw [finiteSum_succ]
  have hprefix :
      finiteSum F
          (fun k : Nat =>
            F.mul
              (F.mul (nat F (Tautology.Nat.binom m k))
                (bernoulliNumber F k))
              (bernoulliPower F F.zero (m - k)))
          m = F.zero := by
    apply finiteSum_eq_zero F
    intro k hk
    have hpos : 0 < m - k := by omega
    cases hpow : m - k with
    | zero => omega
    | succ q =>
        rw [bernoulliPower_zero_succ]
        rw [F.mul_zero]
  rw [hprefix]
  rw [F.zero_add]
  rw [Tautology.Nat.binom_self]
  rw [nat_one]
  rw [Nat.sub_self]
  rw [bernoulliPower_zero]
  rw [F.one_mul]
  rw [F.mul_one]

/-- The endpoint values agree: the polynomial at one equals the polynomial at
zero, hence the number `B m`, for every `m` at least `2`. The restriction is
genuine -- the first polynomial is the exception, taking value `1 / 2` at
one end and `-1 / 2` at the other. -/
theorem bernoulliPolynomialValue_one_eq {m : Nat} (hm : 2 <= m) :
    bernoulliPolynomialValue F m F.one =
      bernoulliPolynomialValue F m F.zero := by
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => omega
      | succ r =>
          rw [bernoulliPolynomialValue_zero]
          unfold bernoulliPolynomialValue
          rw [finiteSum_succ]
          have hprefix :
              finiteSum F
                  (fun k : Nat =>
                    F.mul
                      (F.mul
                        (nat F
                          (Tautology.Nat.binom (r + 2) k))
                        (bernoulliNumber F k))
                      (bernoulliPower F F.one (r + 2 - k)))
                  (r + 2) = F.zero := by
            calc
              finiteSum F
                  (fun k : Nat =>
                    F.mul
                      (F.mul
                        (nat F
                          (Tautology.Nat.binom (r + 2) k))
                        (bernoulliNumber F k))
                      (bernoulliPower F F.one (r + 2 - k)))
                  (r + 2) =
                  finiteSum F
                    (fun k : Nat =>
                      F.mul
                        (nat F
                          (Tautology.Nat.binom (r + 2) k))
                        (bernoulliNumber F k))
                    (r + 2) := by
                      apply finiteSum_congr_lt F
                      intro k hk
                      rw [bernoulliPower_one]
                      rw [F.mul_one]
              _ = F.zero :=
                    bernoulli_recurrence F (n := r + 1) (by omega)
          rw [hprefix]
          rw [F.zero_add]
          rw [Tautology.Nat.binom_self]
          rw [nat_one]
          rw [Nat.sub_self]
          rw [bernoulliPower_one]
          rw [F.one_mul]
          rw [F.mul_one]

private def bernoulliSign : Nat -> alpha
  | 0 => F.one
  | n + 1 => F.neg (bernoulliSign n)

private theorem bernoulliSign_zero :
    bernoulliSign F 0 = F.one :=
  rfl

private theorem bernoulliSign_succ (n : Nat) :
    bernoulliSign F (n + 1) = F.neg (bernoulliSign F n) :=
  rfl

private noncomputable def bernoulliCoefficient (m j : Nat) : alpha :=
  F.mul (nat F (Tautology.Nat.binom m j))
    (bernoulliNumber F (m - j))

private def finiteCoefficientValue
    (coefficient : Nat -> alpha) (n : Nat) (t : alpha) : alpha :=
  finiteSum F
    (fun j : Nat =>
      F.mul (coefficient j) (bernoulliPower F t j))
    (n + 1)

private def finiteCoefficientAverage
    (coefficient : Nat -> alpha) (n : Nat) : alpha :=
  finiteSum F
    (fun j : Nat =>
      F.mul (coefficient j) (F.inv (nat F (j + 1))))
    (n + 1)

private theorem bernoulliPolynomialValue_eq_coefficientValue
    (m : Nat) (t : alpha) :
    bernoulliPolynomialValue F m t =
      finiteCoefficientValue F (bernoulliCoefficient F m) m t := by
  unfold bernoulliPolynomialValue finiteCoefficientValue
  rw [finiteSum_reverse F
    (fun k : Nat =>
      F.mul
        (F.mul (nat F (Tautology.Nat.binom m k))
          (bernoulliNumber F k))
        (bernoulliPower F t (m - k)))
    m]
  apply finiteSum_congr_lt F
  intro j hj
  unfold bernoulliCoefficient
  have hjm : j <= m := by omega
  have hsub : m - (m - j) = j := by omega
  rw [hsub]
  rw [<- Tautology.Nat.binom_symm_of_le (n := m) (k := j) hjm]

private theorem bernoulliCoefficient_derivative
    {m j : Nat} (hj : j <= m) :
    F.mul (nat F (j + 1))
        (bernoulliCoefficient F (m + 1) (j + 1)) =
      F.mul (nat F (m + 1))
        (bernoulliCoefficient F m j) := by
  unfold bernoulliCoefficient
  have hsub : m + 1 - (j + 1) = m - j := by omega
  rw [hsub]
  have hweighted :
      F.mul (nat F (j + 1))
          (nat F (Tautology.Nat.binom (m + 1) (j + 1))) =
        F.mul (nat F (m + 1))
          (nat F (Tautology.Nat.binom m j)) := by
    calc
      F.mul (nat F (j + 1))
          (nat F (Tautology.Nat.binom (m + 1) (j + 1))) =
          nat F
            ((j + 1) * Tautology.Nat.binom (m + 1) (j + 1)) := by
              rw [nat_mul]
      _ = nat F
            ((m + 1) * Tautology.Nat.binom m j) := by
              rw [Tautology.Nat.succ_mul_binom_succ hj]
      _ = F.mul (nat F (m + 1))
            (nat F (Tautology.Nat.binom m j)) := by
              rw [nat_mul]
  rw [<- F.mul_assoc]
  rw [<- F.mul_assoc]
  rw [hweighted]

private theorem mul_inv_eq_inv_mul_of_cross
    {a b c d : alpha}
    (ha : Not (a = F.zero)) (hb : Not (b = F.zero))
    (hcross : F.mul a c = F.mul b d) :
    F.mul d (F.inv a) = F.mul (F.inv b) c := by
  calc
    F.mul d (F.inv a) =
        F.mul F.one (F.mul d (F.inv a)) := by
          rw [F.one_mul]
    _ = F.mul (F.mul (F.inv b) b)
          (F.mul d (F.inv a)) := by
          rw [F.inv_mul_cancel hb]
    _ = F.mul (F.inv b)
          (F.mul (F.mul b d) (F.inv a)) := by
          rw [F.mul_assoc]
          rw [F.mul_assoc]
    _ = F.mul (F.inv b)
          (F.mul (F.mul a c) (F.inv a)) := by
          rw [hcross]
    _ = F.mul (F.inv b)
          (F.mul c (F.mul a (F.inv a))) := by
          congr 1
          calc
            F.mul (F.mul a c) (F.inv a) =
                F.mul (F.mul c a) (F.inv a) := by
                  rw [F.mul_comm a c]
            _ = F.mul c (F.mul a (F.inv a)) := by
                  rw [F.mul_assoc]
    _ = F.mul (F.inv b) (F.mul c F.one) := by
          rw [F.mul_inv_cancel ha]
    _ = F.mul (F.inv b) c := by
          rw [F.mul_one]

private theorem bernoulliCoefficient_average_term
    {m j : Nat} (hj : j <= m) :
    F.mul (bernoulliCoefficient F m j)
        (F.inv (nat F (j + 1))) =
      F.mul (F.inv (nat F (m + 1)))
        (F.mul
          (nat F (Tautology.Nat.binom (m + 1) (j + 1)))
          (bernoulliNumber F (m - j))) := by
  unfold bernoulliCoefficient
  have hj1 : Not (nat F (j + 1) = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  have hm1 : Not (nat F (m + 1) = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  have hcross :
      F.mul (nat F (j + 1))
          (nat F (Tautology.Nat.binom (m + 1) (j + 1))) =
        F.mul (nat F (m + 1))
          (nat F (Tautology.Nat.binom m j)) := by
    calc
      F.mul (nat F (j + 1))
          (nat F (Tautology.Nat.binom (m + 1) (j + 1))) =
          nat F
            ((j + 1) * Tautology.Nat.binom (m + 1) (j + 1)) := by
              rw [nat_mul]
      _ = nat F
            ((m + 1) * Tautology.Nat.binom m j) := by
              rw [Tautology.Nat.succ_mul_binom_succ hj]
      _ = F.mul (nat F (m + 1))
            (nat F (Tautology.Nat.binom m j)) := by
              rw [nat_mul]
  have hratio :
      F.mul (nat F (Tautology.Nat.binom m j))
          (F.inv (nat F (j + 1))) =
        F.mul (F.inv (nat F (m + 1)))
          (nat F (Tautology.Nat.binom (m + 1) (j + 1))) :=
    mul_inv_eq_inv_mul_of_cross F hj1 hm1 hcross
  calc
    F.mul
        (F.mul (nat F (Tautology.Nat.binom m j))
          (bernoulliNumber F (m - j)))
        (F.inv (nat F (j + 1))) =
        F.mul
          (F.mul (nat F (Tautology.Nat.binom m j))
            (F.inv (nat F (j + 1))))
          (bernoulliNumber F (m - j)) := by
            rw [F.mul_assoc]
            rw [F.mul_comm
              (bernoulliNumber F (m - j))
              (F.inv (nat F (j + 1)))]
            rw [<- F.mul_assoc]
    _ = F.mul
          (F.mul (F.inv (nat F (m + 1)))
            (nat F (Tautology.Nat.binom (m + 1) (j + 1))))
          (bernoulliNumber F (m - j)) := by
            rw [hratio]
    _ = F.mul (F.inv (nat F (m + 1)))
          (F.mul
            (nat F (Tautology.Nat.binom (m + 1) (j + 1)))
            (bernoulliNumber F (m - j))) := by
            rw [F.mul_assoc]

private theorem bernoulliCoefficient_average_zero
    {m : Nat} (hm : 0 < m) :
    finiteCoefficientAverage F (bernoulliCoefficient F m) m =
      F.zero := by
  unfold finiteCoefficientAverage
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul (bernoulliCoefficient F m j)
            (F.inv (nat F (j + 1))))
        (m + 1) =
        finiteSum F
          (fun j : Nat =>
            F.mul (F.inv (nat F (m + 1)))
              (F.mul
                (nat F (Tautology.Nat.binom (m + 1) (j + 1)))
                (bernoulliNumber F (m - j))))
          (m + 1) := by
            apply finiteSum_congr_lt F
            intro j hj
            exact bernoulliCoefficient_average_term F (by omega)
    _ = F.mul (F.inv (nat F (m + 1)))
          (finiteSum F
            (fun j : Nat =>
              F.mul
                (nat F (Tautology.Nat.binom (m + 1) (j + 1)))
                (bernoulliNumber F (m - j)))
            (m + 1)) := by
            exact finiteSum_mul_left F
              (F.inv (nat F (m + 1)))
              (fun j : Nat =>
                F.mul
                  (nat F (Tautology.Nat.binom (m + 1) (j + 1)))
                  (bernoulliNumber F (m - j)))
              (m + 1)
    _ = F.mul (F.inv (nat F (m + 1)))
          (finiteSum F
            (fun k : Nat =>
              F.mul (nat F (Tautology.Nat.binom (m + 1) k))
                (bernoulliNumber F k))
            (m + 1)) := by
            congr 1
            rw [finiteSum_reverse F
              (fun j : Nat =>
                F.mul
                  (nat F (Tautology.Nat.binom (m + 1) (j + 1)))
                  (bernoulliNumber F (m - j)))
              m]
            apply finiteSum_congr_lt F
            intro k hk
            have hkm : k <= m := by omega
            have hindex : m - (m - k) = k := by omega
            have hchooseIndex :
                m - k + 1 = (m + 1) - k := by omega
            rw [hindex]
            rw [hchooseIndex]
            rw [<- Tautology.Nat.binom_symm_of_le
              (n := m + 1) (k := k) (by omega)]
    _ = F.mul (F.inv (nat F (m + 1))) F.zero := by
            rw [bernoulli_recurrence F hm]
    _ = F.zero := by rw [F.mul_zero]

private theorem bernoulliPower_step_of_lt
    (x : alpha) {n j : Nat} (hj : j < n) :
    F.mul x (bernoulliPower F x (n - (j + 1))) =
      bernoulliPower F x (n - j) := by
  have h : n - j = (n - (j + 1)) + 1 := by omega
  rw [h]

private def binomialPowerTerm
    (x y : alpha) (n k : Nat) : alpha :=
  F.mul
    (F.mul (nat F (Tautology.Nat.binom n k))
      (bernoulliPower F x (n - k)))
    (bernoulliPower F y k)

private def binomialPowerExpansion
    (x y : alpha) (n : Nat) : alpha :=
  finiteSum F (fun k : Nat => binomialPowerTerm F x y n k) (n + 1)

private def binomialPowerShiftTerm
    (x y : alpha) (n k : Nat) : alpha :=
  F.mul
    (F.mul (nat F (Tautology.Nat.binom n k))
      (bernoulliPower F x (n - k)))
    (bernoulliPower F y (k + 1))

private def binomialPowerPascalRightTerm
    (x y : alpha) (n : Nat) : Nat -> alpha
  | 0 => F.zero
  | j + 1 => binomialPowerShiftTerm F x y n j

private theorem binomialPowerTerm_out_of_range
    (x y : alpha) (n : Nat) :
    binomialPowerTerm F x y n (n + 1) = F.zero := by
  unfold binomialPowerTerm
  rw [Tautology.Nat.binom_eq_zero_of_lt (Nat.lt_succ_self n)]
  rw [nat_zero]
  rw [F.zero_mul]
  rw [F.zero_mul]

private theorem binomialPowerPascalRight_prepend_zero
    (x y : alpha) (n : Nat) :
    finiteSum F
        (binomialPowerPascalRightTerm F x y n)
        ((n + 1) + 1) =
      finiteSum F
        (fun k : Nat => binomialPowerShiftTerm F x y n k)
        (n + 1) := by
  unfold binomialPowerPascalRightTerm
  change
    finiteSum F
        (fun k : Nat =>
          match k with
          | 0 => F.zero
          | j + 1 => binomialPowerShiftTerm F x y n j)
        ((n + 1) + 1) =
      finiteSum F
        (fun k : Nat => binomialPowerShiftTerm F x y n k)
        (n + 1)
  exact finiteSum_prepend_zero F
    (fun k : Nat => binomialPowerShiftTerm F x y n k) (n + 1)

private theorem binomialPowerTerm_pascal
    (x y : alpha) (n k : Nat) (hk : k < (n + 1) + 1) :
    F.add
        (F.mul x (binomialPowerTerm F x y n k))
        (binomialPowerPascalRightTerm F x y n k) =
      binomialPowerTerm F x y (n + 1) k := by
  cases k with
  | zero =>
      unfold binomialPowerPascalRightTerm binomialPowerTerm
      rw [Tautology.Nat.binom_zero]
      rw [Tautology.Nat.binom_succ_zero]
      rw [nat_one]
      rw [Nat.sub_zero]
      rw [Nat.sub_zero]
      rw [bernoulliPower_zero]
      rw [F.one_mul]
      rw [F.mul_one]
      rw [F.mul_one]
      rw [F.add_zero]
      rw [bernoulliPower_succ]
      rw [F.one_mul]
  | succ j =>
      unfold binomialPowerPascalRightTerm
      unfold binomialPowerShiftTerm binomialPowerTerm
      rw [Tautology.Nat.binom_succ_succ]
      rw [nat_add]
      have hexp : n + 1 - (j + 1) = n - j := by omega
      rw [hexp]
      by_cases hj : j < n
      · have hstep := bernoulliPower_step_of_lt F x hj
        let A : alpha := nat F (Tautology.Nat.binom n j)
        let B : alpha := nat F (Tautology.Nat.binom n (j + 1))
        let X : alpha := bernoulliPower F x (n - j)
        let Y : alpha := bernoulliPower F y (j + 1)
        have hfirst :
            F.mul x
                (F.mul
                  (F.mul B
                    (bernoulliPower F x (n - (j + 1)))) Y) =
              F.mul (F.mul B X) Y := by
          let P : alpha := bernoulliPower F x (n - (j + 1))
          calc
            F.mul x
                (F.mul
                  (F.mul B
                    (bernoulliPower F x (n - (j + 1)))) Y) =
                F.mul (F.mul x (F.mul B P)) Y := by
                  exact Eq.symm
                    (F.mul_assoc x (F.mul B P) Y)
            _ = F.mul (F.mul (F.mul x B) P) Y := by
                  congr 1
                  exact Eq.symm (F.mul_assoc x B P)
            _ = F.mul (F.mul (F.mul B x) P) Y := by
                  congr 1
                  congr 1
                  exact F.mul_comm x B
            _ = F.mul (F.mul B (F.mul x P)) Y := by
                  congr 1
                  exact F.mul_assoc B x P
            _ = F.mul (F.mul B X) Y := by rw [hstep]
        rw [hfirst]
        change
          F.add (F.mul (F.mul B X) Y) (F.mul (F.mul A X) Y) =
            F.mul (F.mul (F.add A B) X) Y
        calc
          F.add (F.mul (F.mul B X) Y) (F.mul (F.mul A X) Y) =
              F.add (F.mul (F.mul A X) Y)
                (F.mul (F.mul B X) Y) := by
                  rw [F.add_comm]
          _ = F.mul
                (F.add (F.mul A X) (F.mul B X)) Y := by
                  exact Eq.symm
                    (F.add_mul (F.mul A X) (F.mul B X) Y)
          _ = F.mul (F.mul (F.add A B) X) Y := by
                  rw [<- F.add_mul]
      · have hjn : j = n := by omega
        subst j
        simp only
        rw [Tautology.Nat.binom_eq_zero_of_lt
          (Nat.lt_succ_self n)]
        rw [nat_zero]
        rw [F.zero_mul]
        rw [F.zero_mul]
        rw [F.mul_zero]
        rw [F.zero_add]
        rw [Tautology.Nat.binom_self]
        rw [nat_one]
        rw [Nat.sub_self]
        rw [bernoulliPower_zero]
        rw [F.one_mul]
        rw [F.one_mul]
        rw [F.add_zero]
        rw [F.one_mul]
        rw [F.one_mul]

private theorem binomialPowerExpansion_pascal
    (x y : alpha) (n : Nat) :
    binomialPowerExpansion F x y (n + 1) =
      F.add
        (F.mul x (binomialPowerExpansion F x y n))
        (finiteSum F
          (fun k : Nat => binomialPowerShiftTerm F x y n k)
          (n + 1)) := by
  unfold binomialPowerExpansion
  calc
    finiteSum F
        (fun k : Nat => binomialPowerTerm F x y (n + 1) k)
        ((n + 1) + 1) =
        finiteSum F
          (fun k : Nat =>
            F.add
              (F.mul x (binomialPowerTerm F x y n k))
              (binomialPowerPascalRightTerm F x y n k))
          ((n + 1) + 1) := by
            apply finiteSum_congr_lt F
            intro k hk
            exact Eq.symm (binomialPowerTerm_pascal F x y n k hk)
    _ = F.add
          (finiteSum F
            (fun k : Nat =>
              F.mul x (binomialPowerTerm F x y n k))
            ((n + 1) + 1))
          (finiteSum F
            (binomialPowerPascalRightTerm F x y n)
            ((n + 1) + 1)) := by
            exact finiteSum_add F
              (fun k : Nat =>
                F.mul x (binomialPowerTerm F x y n k))
              (binomialPowerPascalRightTerm F x y n)
              ((n + 1) + 1)
    _ = F.add
          (finiteSum F
            (fun k : Nat =>
              F.mul x (binomialPowerTerm F x y n k))
            (n + 1))
          (finiteSum F
            (binomialPowerPascalRightTerm F x y n)
            ((n + 1) + 1)) := by
            have hlast :
                F.mul x (binomialPowerTerm F x y n (n + 1)) =
                  F.zero := by
              rw [binomialPowerTerm_out_of_range]
              rw [F.mul_zero]
            rw [finiteSum_append_zero
              (F := F)
              (term := fun k : Nat =>
                F.mul x (binomialPowerTerm F x y n k))
              (n := n + 1) hlast]
    _ = F.add
          (F.mul x
            (finiteSum F
              (fun k : Nat => binomialPowerTerm F x y n k)
              (n + 1)))
          (finiteSum F
            (binomialPowerPascalRightTerm F x y n)
            ((n + 1) + 1)) := by
            rw [finiteSum_mul_left]
    _ = F.add
          (F.mul x
            (finiteSum F
              (fun k : Nat => binomialPowerTerm F x y n k)
              (n + 1)))
          (finiteSum F
            (fun k : Nat => binomialPowerShiftTerm F x y n k)
            (n + 1)) := by
            rw [binomialPowerPascalRight_prepend_zero]

private theorem binomialPowerShift_eq_mul_term
    (x y : alpha) (n k : Nat) :
    binomialPowerShiftTerm F x y n k =
      F.mul y (binomialPowerTerm F x y n k) := by
  unfold binomialPowerShiftTerm binomialPowerTerm
  rw [bernoulliPower_succ]
  let A : alpha :=
    F.mul (nat F (Tautology.Nat.binom n k))
      (bernoulliPower F x (n - k))
  calc
    F.mul A (F.mul y (bernoulliPower F y k)) =
        F.mul (F.mul A y) (bernoulliPower F y k) := by
          exact Eq.symm (F.mul_assoc A y (bernoulliPower F y k))
    _ = F.mul (F.mul y A) (bernoulliPower F y k) := by
          rw [F.mul_comm A y]
    _ = F.mul y (F.mul A (bernoulliPower F y k)) := by
          rw [F.mul_assoc]

private theorem binomialPowerExpansion_eq_power :
    forall n : Nat,
      binomialPowerExpansion F x y n =
        bernoulliPower F (F.add x y) n
  | 0 => by
      unfold binomialPowerExpansion binomialPowerTerm
      rw [finiteSum_one]
      rw [Tautology.Nat.binom_zero_zero]
      rw [nat_one]
      rw [Nat.sub_zero]
      change F.mul (F.mul F.one F.one) F.one = F.one
      rw [F.one_mul]
      rw [F.one_mul]
  | n + 1 => by
      rw [binomialPowerExpansion_pascal]
      have hshift :
          finiteSum F
              (fun k : Nat => binomialPowerShiftTerm F x y n k)
              (n + 1) =
            F.mul y (binomialPowerExpansion F x y n) := by
        unfold binomialPowerExpansion
        calc
          finiteSum F
              (fun k : Nat => binomialPowerShiftTerm F x y n k)
              (n + 1) =
              finiteSum F
                (fun k : Nat =>
                  F.mul y (binomialPowerTerm F x y n k))
                (n + 1) := by
                  apply finiteSum_congr F
                  intro k
                  rw [binomialPowerShift_eq_mul_term]
          _ = F.mul y
                (finiteSum F
                  (fun k : Nat => binomialPowerTerm F x y n k)
                  (n + 1)) := by
                  rw [finiteSum_mul_left]
      rw [hshift]
      rw [binomialPowerExpansion_eq_power n]
      rw [bernoulliPower_succ]
      rw [F.add_mul]

private theorem bernoulliPower_neg
    (t : alpha) : forall n : Nat,
      bernoulliPower F (F.neg t) n =
        F.mul (bernoulliSign F n) (bernoulliPower F t n)
  | 0 => by
      rw [bernoulliPower_zero]
      rw [bernoulliSign_zero]
      rw [F.one_mul]
      rw [bernoulliPower_zero]
  | n + 1 => by
      rw [bernoulliPower_succ]
      rw [bernoulliPower_neg t n]
      rw [bernoulliSign_succ]
      rw [bernoulliPower_succ]
      calc
        F.mul (F.neg t)
            (F.mul (bernoulliSign F n) (bernoulliPower F t n)) =
            F.neg
              (F.mul t
                (F.mul (bernoulliSign F n)
                  (bernoulliPower F t n))) := by
                rw [neg_mul F]
        _ = F.neg
              (F.mul (bernoulliSign F n)
                (F.mul t (bernoulliPower F t n))) := by
                congr 1
                calc
                  F.mul t
                      (F.mul (bernoulliSign F n)
                        (bernoulliPower F t n)) =
                      F.mul (F.mul t (bernoulliSign F n))
                        (bernoulliPower F t n) := by
                          rw [F.mul_assoc]
                  _ = F.mul
                        (F.mul (bernoulliSign F n) t)
                        (bernoulliPower F t n) := by
                          rw [F.mul_comm t (bernoulliSign F n)]
                  _ = F.mul (bernoulliSign F n)
                        (F.mul t (bernoulliPower F t n)) := by
                          rw [F.mul_assoc]
        _ = F.mul (F.neg (bernoulliSign F n))
              (F.mul t (bernoulliPower F t n)) := by
                exact Eq.symm
                  (neg_mul F (bernoulliSign F n)
                    (F.mul t (bernoulliPower F t n)))

private theorem bernoulliPower_one_sub_expansion
    (q : Nat) (t : alpha) :
    bernoulliPower F (F.sub F.one t) q =
      finiteSum F
        (fun j : Nat =>
          F.mul
            (F.mul (nat F (Tautology.Nat.binom q j))
              (bernoulliSign F j))
            (bernoulliPower F t j))
        (q + 1) := by
  rw [F.sub_eq_add_neg]
  rw [<- binomialPowerExpansion_eq_power
    (F := F) (x := F.one) (y := F.neg t) q]
  unfold binomialPowerExpansion binomialPowerTerm
  apply finiteSum_congr_lt F
  intro j hj
  rw [bernoulliPower_one]
  rw [bernoulliPower_neg]
  rw [F.mul_one]
  rw [F.mul_assoc]

private theorem bernoulliPower_one_sub_expansion_padded
    {q n : Nat} (hq : q <= n) (t : alpha) :
    bernoulliPower F (F.sub F.one t) q =
      finiteSum F
        (fun j : Nat =>
          F.mul
            (F.mul (nat F (Tautology.Nat.binom q j))
              (bernoulliSign F j))
            (bernoulliPower F t j))
        (n + 1) := by
  have hlen : n + 1 = (q + 1) + (n - q) := by omega
  let term : Nat -> alpha :=
    fun j : Nat =>
      F.mul
        (F.mul (nat F (Tautology.Nat.binom q j))
          (bernoulliSign F j))
        (bernoulliPower F t j)
  have htail :
      finiteSum F (fun r : Nat => term (q + 1 + r)) (n - q) =
        F.zero := by
    apply finiteSum_eq_zero F
    intro r hr
    unfold term
    rw [Tautology.Nat.binom_eq_zero_of_lt (by omega)]
    rw [nat_zero]
    rw [F.zero_mul]
    rw [F.zero_mul]
  calc
    bernoulliPower F (F.sub F.one t) q =
        finiteSum F term (q + 1) := by
          exact bernoulliPower_one_sub_expansion F q t
    _ = finiteSum F term ((q + 1) + (n - q)) := by
          calc
            finiteSum F term (q + 1) =
                F.add (finiteSum F term (q + 1)) F.zero := by
                  rw [F.add_zero]
            _ = F.add (finiteSum F term (q + 1))
                  (finiteSum F (fun r : Nat => term (q + 1 + r))
                    (n - q)) := by
                  rw [htail]
            _ = finiteSum F term ((q + 1) + (n - q)) := by
                  exact Eq.symm
                    (finiteSum_add_length F term (q + 1) (n - q))
    _ = finiteSum F term (n + 1) := by rw [<- hlen]

private def reflectedCoefficient
    (coefficient : Nat -> alpha) (n j : Nat) : alpha :=
  finiteSum F
    (fun q : Nat =>
      F.mul
        (F.mul (coefficient q)
          (nat F (Tautology.Nat.binom q j)))
        (bernoulliSign F j))
    (n + 1)

private theorem reflectedCoefficient_value
    (coefficient : Nat -> alpha) (n : Nat) (t : alpha) :
    finiteCoefficientValue F
        (reflectedCoefficient F coefficient n) n t =
      finiteCoefficientValue F coefficient n (F.sub F.one t) := by
  unfold finiteCoefficientValue reflectedCoefficient
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul
            (finiteSum F
              (fun q : Nat =>
                F.mul
                  (F.mul (coefficient q)
                    (nat F (Tautology.Nat.binom q j)))
                  (bernoulliSign F j))
              (n + 1))
            (bernoulliPower F t j))
        (n + 1) =
        finiteSum F
          (fun j : Nat =>
            finiteSum F
              (fun q : Nat =>
                F.mul
                  (F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                  (bernoulliPower F t j))
              (n + 1))
          (n + 1) := by
            apply finiteSum_congr F
            intro j
            exact Eq.symm
              (finiteSum_mul_right F
                (fun q : Nat =>
                  F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                (bernoulliPower F t j) (n + 1))
    _ = finiteSum F
          (fun q : Nat =>
            finiteSum F
              (fun j : Nat =>
                F.mul
                  (F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                  (bernoulliPower F t j))
              (n + 1))
          (n + 1) := by
            exact finiteSum_fubini F
              (fun j q : Nat =>
                F.mul
                  (F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                  (bernoulliPower F t j))
              (n + 1) (n + 1)
    _ = finiteSum F
          (fun q : Nat =>
            F.mul (coefficient q)
              (finiteSum F
                (fun j : Nat =>
                  F.mul
                    (F.mul
                      (nat F (Tautology.Nat.binom q j))
                      (bernoulliSign F j))
                    (bernoulliPower F t j))
                (n + 1)))
          (n + 1) := by
            apply finiteSum_congr F
            intro q
            calc
              finiteSum F
                  (fun j : Nat =>
                    F.mul
                      (F.mul
                        (F.mul (coefficient q)
                          (nat F (Tautology.Nat.binom q j)))
                        (bernoulliSign F j))
                      (bernoulliPower F t j))
                  (n + 1) =
                  finiteSum F
                    (fun j : Nat =>
                      F.mul (coefficient q)
                        (F.mul
                          (F.mul
                            (nat F (Tautology.Nat.binom q j))
                            (bernoulliSign F j))
                          (bernoulliPower F t j)))
                    (n + 1) := by
                      apply finiteSum_congr F
                      intro j
                      calc
                        F.mul
                            (F.mul
                              (F.mul (coefficient q)
                                (nat F (Tautology.Nat.binom q j)))
                              (bernoulliSign F j))
                            (bernoulliPower F t j) =
                            F.mul
                              (F.mul (coefficient q)
                                (F.mul
                                  (nat F (Tautology.Nat.binom q j))
                                  (bernoulliSign F j)))
                              (bernoulliPower F t j) := by
                                congr 1
                                exact F.mul_assoc
                                  (coefficient q)
                                  (nat F (Tautology.Nat.binom q j))
                                  (bernoulliSign F j)
                        _ = F.mul (coefficient q)
                              (F.mul
                                (F.mul
                                  (nat F (Tautology.Nat.binom q j))
                                  (bernoulliSign F j))
                                (bernoulliPower F t j)) := by
                                exact F.mul_assoc
                                  (coefficient q)
                                  (F.mul
                                    (nat F (Tautology.Nat.binom q j))
                                    (bernoulliSign F j))
                                  (bernoulliPower F t j)
              _ = F.mul (coefficient q)
                    (finiteSum F
                      (fun j : Nat =>
                        F.mul
                          (F.mul
                            (nat F (Tautology.Nat.binom q j))
                            (bernoulliSign F j))
                          (bernoulliPower F t j))
                      (n + 1)) := by
                      exact finiteSum_mul_left F (coefficient q)
                        (fun j : Nat =>
                          F.mul
                            (F.mul
                              (nat F (Tautology.Nat.binom q j))
                              (bernoulliSign F j))
                            (bernoulliPower F t j))
                        (n + 1)
    _ = finiteSum F
          (fun q : Nat =>
            F.mul (coefficient q)
              (bernoulliPower F (F.sub F.one t) q))
          (n + 1) := by
            apply finiteSum_congr_lt F
            intro q hq
            rw [bernoulliPower_one_sub_expansion_padded
              (F := F) (q := q) (n := n) (by omega) t]

private theorem bernoulliPower_zero_of_pos
    {n : Nat} (hn : 0 < n) :
    bernoulliPower F F.zero n = F.zero := by
  cases n with
  | zero => omega
  | succ n => exact bernoulliPower_zero_succ F n

private theorem alternating_binomial_sum_zero
    {n : Nat} (hn : 0 < n) :
    finiteSum F
        (fun j : Nat =>
          F.mul (nat F (Tautology.Nat.binom n j))
            (bernoulliSign F j))
        (n + 1) = F.zero := by
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul (nat F (Tautology.Nat.binom n j))
            (bernoulliSign F j))
        (n + 1) =
        binomialPowerExpansion F F.one (F.neg F.one) n := by
          unfold binomialPowerExpansion binomialPowerTerm
          apply finiteSum_congr_lt F
          intro j hj
          rw [bernoulliPower_one]
          rw [bernoulliPower_neg]
          rw [bernoulliPower_one]
          rw [F.mul_one]
          rw [F.mul_one]
    _ = bernoulliPower F (F.add F.one (F.neg F.one)) n := by
          exact binomialPowerExpansion_eq_power
            (F := F) (x := F.one) (y := F.neg F.one) n
    _ = bernoulliPower F F.zero n := by rw [F.add_neg]
    _ = F.zero := bernoulliPower_zero_of_pos F hn

private theorem shifted_alternating_binomial_sum_one (n : Nat) :
    finiteSum F
        (fun j : Nat =>
          F.mul
            (nat F (Tautology.Nat.binom (n + 1) (j + 1)))
            (bernoulliSign F j))
        (n + 1) = F.one := by
  let shifted : Nat -> alpha :=
    fun j : Nat =>
      F.mul
        (nat F (Tautology.Nat.binom (n + 1) (j + 1)))
        (bernoulliSign F j)
  have hfull := alternating_binomial_sum_zero F (n := n + 1) (by omega)
  rw [finiteSum_split_first F
    (fun k : Nat =>
      F.mul (nat F (Tautology.Nat.binom (n + 1) k))
        (bernoulliSign F k))
    (n + 1)] at hfull
  have htail :
      finiteSum F
          (fun j : Nat =>
            F.mul
              (nat F (Tautology.Nat.binom (n + 1) (j + 1)))
              (bernoulliSign F (j + 1)))
          (n + 1) =
        F.neg (finiteSum F shifted (n + 1)) := by
    calc
      finiteSum F
          (fun j : Nat =>
            F.mul
              (nat F (Tautology.Nat.binom (n + 1) (j + 1)))
              (bernoulliSign F (j + 1)))
          (n + 1) =
          finiteSum F (fun j : Nat => F.neg (shifted j)) (n + 1) := by
            apply finiteSum_congr F
            intro j
            unfold shifted
            rw [bernoulliSign_succ]
            rw [mul_neg F]
      _ = F.neg (finiteSum F shifted (n + 1)) := by
            exact finiteSum_neg F shifted (n + 1)
  rw [Tautology.Nat.binom_zero] at hfull
  rw [nat_one] at hfull
  rw [bernoulliSign_zero] at hfull
  rw [F.one_mul] at hfull
  rw [htail] at hfull
  have hneg :
      F.neg (finiteSum F shifted (n + 1)) = F.neg F.one :=
    eq_neg_of_add_eq_zero_left F hfull
  have h := congrArg F.neg hneg
  rw [neg_neg F] at h
  rw [neg_neg F] at h
  exact h

private theorem binomial_average_term
    {q j : Nat} (hj : j <= q) :
    F.mul
        (F.mul (nat F (Tautology.Nat.binom q j))
          (bernoulliSign F j))
        (F.inv (nat F (j + 1))) =
      F.mul (F.inv (nat F (q + 1)))
        (F.mul
          (nat F (Tautology.Nat.binom (q + 1) (j + 1)))
          (bernoulliSign F j)) := by
  have hj1 : Not (nat F (j + 1) = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  have hq1 : Not (nat F (q + 1) = F.zero) :=
    nat_ne_zero_of_ne_zero F (by omega)
  have hcross :
      F.mul (nat F (j + 1))
          (nat F (Tautology.Nat.binom (q + 1) (j + 1))) =
        F.mul (nat F (q + 1))
          (nat F (Tautology.Nat.binom q j)) := by
    calc
      F.mul (nat F (j + 1))
          (nat F (Tautology.Nat.binom (q + 1) (j + 1))) =
          nat F
            ((j + 1) * Tautology.Nat.binom (q + 1) (j + 1)) := by
              rw [nat_mul]
      _ = nat F ((q + 1) * Tautology.Nat.binom q j) := by
              rw [Tautology.Nat.succ_mul_binom_succ hj]
      _ = F.mul (nat F (q + 1))
            (nat F (Tautology.Nat.binom q j)) := by
              rw [nat_mul]
  have hratio :
      F.mul (nat F (Tautology.Nat.binom q j))
          (F.inv (nat F (j + 1))) =
        F.mul (F.inv (nat F (q + 1)))
          (nat F (Tautology.Nat.binom (q + 1) (j + 1))) :=
    mul_inv_eq_inv_mul_of_cross F hj1 hq1 hcross
  calc
    F.mul
        (F.mul (nat F (Tautology.Nat.binom q j))
          (bernoulliSign F j))
        (F.inv (nat F (j + 1))) =
        F.mul
          (F.mul (nat F (Tautology.Nat.binom q j))
            (F.inv (nat F (j + 1))))
          (bernoulliSign F j) := by
            rw [F.mul_assoc]
            rw [F.mul_comm
              (bernoulliSign F j) (F.inv (nat F (j + 1)))]
            rw [<- F.mul_assoc]
    _ = F.mul
          (F.mul (F.inv (nat F (q + 1)))
            (nat F (Tautology.Nat.binom (q + 1) (j + 1)))
          ) (bernoulliSign F j) := by rw [hratio]
    _ = F.mul (F.inv (nat F (q + 1)))
          (F.mul
            (nat F (Tautology.Nat.binom (q + 1) (j + 1)))
            (bernoulliSign F j)) := by
            rw [F.mul_assoc]

private theorem reflected_power_average (q : Nat) :
    finiteSum F
        (fun j : Nat =>
          F.mul
            (F.mul (nat F (Tautology.Nat.binom q j))
              (bernoulliSign F j))
            (F.inv (nat F (j + 1))))
        (q + 1) = F.inv (nat F (q + 1)) := by
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul
            (F.mul (nat F (Tautology.Nat.binom q j))
              (bernoulliSign F j))
            (F.inv (nat F (j + 1))))
        (q + 1) =
        finiteSum F
          (fun j : Nat =>
            F.mul (F.inv (nat F (q + 1)))
              (F.mul
                (nat F (Tautology.Nat.binom (q + 1) (j + 1)))
                (bernoulliSign F j)))
          (q + 1) := by
            apply finiteSum_congr_lt F
            intro j hj
            exact binomial_average_term F (by omega)
    _ = F.mul (F.inv (nat F (q + 1)))
          (finiteSum F
            (fun j : Nat =>
              F.mul
                (nat F (Tautology.Nat.binom (q + 1) (j + 1)))
                (bernoulliSign F j))
            (q + 1)) := by
            exact finiteSum_mul_left F (F.inv (nat F (q + 1)))
              (fun j : Nat =>
                F.mul
                  (nat F (Tautology.Nat.binom (q + 1) (j + 1)))
                  (bernoulliSign F j))
              (q + 1)
    _ = F.mul (F.inv (nat F (q + 1))) F.one := by
            rw [shifted_alternating_binomial_sum_one]
    _ = F.inv (nat F (q + 1)) := by rw [F.mul_one]

private theorem reflected_power_average_padded
    {q n : Nat} (hq : q <= n) :
    finiteSum F
        (fun j : Nat =>
          F.mul
            (F.mul (nat F (Tautology.Nat.binom q j))
              (bernoulliSign F j))
            (F.inv (nat F (j + 1))))
        (n + 1) = F.inv (nat F (q + 1)) := by
  let term : Nat -> alpha :=
    fun j : Nat =>
      F.mul
        (F.mul (nat F (Tautology.Nat.binom q j))
          (bernoulliSign F j))
        (F.inv (nat F (j + 1)))
  have hlen : n + 1 = (q + 1) + (n - q) := by omega
  have htail :
      finiteSum F (fun r : Nat => term (q + 1 + r)) (n - q) =
        F.zero := by
    apply finiteSum_eq_zero F
    intro r hr
    unfold term
    rw [Tautology.Nat.binom_eq_zero_of_lt (by omega)]
    rw [nat_zero]
    rw [F.zero_mul]
    rw [F.zero_mul]
  calc
    finiteSum F term (n + 1) =
        finiteSum F term ((q + 1) + (n - q)) := by rw [<- hlen]
    _ = F.add (finiteSum F term (q + 1))
          (finiteSum F (fun r : Nat => term (q + 1 + r))
            (n - q)) := by
          exact finiteSum_add_length F term (q + 1) (n - q)
    _ = finiteSum F term (q + 1) := by rw [htail, F.add_zero]
    _ = F.inv (nat F (q + 1)) := reflected_power_average F q

private theorem reflectedCoefficient_average
    (coefficient : Nat -> alpha) (n : Nat) :
    finiteCoefficientAverage F
        (reflectedCoefficient F coefficient n) n =
      finiteCoefficientAverage F coefficient n := by
  unfold finiteCoefficientAverage reflectedCoefficient
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul
            (finiteSum F
              (fun q : Nat =>
                F.mul
                  (F.mul (coefficient q)
                    (nat F (Tautology.Nat.binom q j)))
                  (bernoulliSign F j))
              (n + 1))
            (F.inv (nat F (j + 1))))
        (n + 1) =
        finiteSum F
          (fun j : Nat =>
            finiteSum F
              (fun q : Nat =>
                F.mul
                  (F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                  (F.inv (nat F (j + 1))))
              (n + 1))
          (n + 1) := by
            apply finiteSum_congr F
            intro j
            exact Eq.symm
              (finiteSum_mul_right F
                (fun q : Nat =>
                  F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                (F.inv (nat F (j + 1))) (n + 1))
    _ = finiteSum F
          (fun q : Nat =>
            finiteSum F
              (fun j : Nat =>
                F.mul
                  (F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                  (F.inv (nat F (j + 1))))
              (n + 1))
          (n + 1) := by
            exact finiteSum_fubini F
              (fun j q : Nat =>
                F.mul
                  (F.mul
                    (F.mul (coefficient q)
                      (nat F (Tautology.Nat.binom q j)))
                    (bernoulliSign F j))
                  (F.inv (nat F (j + 1))))
              (n + 1) (n + 1)
    _ = finiteSum F
          (fun q : Nat =>
            F.mul (coefficient q)
              (finiteSum F
                (fun j : Nat =>
                  F.mul
                    (F.mul
                      (nat F (Tautology.Nat.binom q j))
                      (bernoulliSign F j))
                    (F.inv (nat F (j + 1))))
                (n + 1)))
          (n + 1) := by
            apply finiteSum_congr F
            intro q
            calc
              finiteSum F
                  (fun j : Nat =>
                    F.mul
                      (F.mul
                        (F.mul (coefficient q)
                          (nat F (Tautology.Nat.binom q j)))
                        (bernoulliSign F j))
                      (F.inv (nat F (j + 1))))
                  (n + 1) =
                  finiteSum F
                    (fun j : Nat =>
                      F.mul (coefficient q)
                        (F.mul
                          (F.mul
                            (nat F (Tautology.Nat.binom q j))
                            (bernoulliSign F j))
                          (F.inv (nat F (j + 1)))))
                    (n + 1) := by
                      apply finiteSum_congr F
                      intro j
                      calc
                        F.mul
                            (F.mul
                              (F.mul (coefficient q)
                                (nat F (Tautology.Nat.binom q j)))
                              (bernoulliSign F j))
                            (F.inv (nat F (j + 1))) =
                            F.mul
                              (F.mul (coefficient q)
                                (F.mul
                                  (nat F (Tautology.Nat.binom q j))
                                  (bernoulliSign F j)))
                              (F.inv (nat F (j + 1))) := by
                                congr 1
                                exact F.mul_assoc
                                  (coefficient q)
                                  (nat F (Tautology.Nat.binom q j))
                                  (bernoulliSign F j)
                        _ = F.mul (coefficient q)
                              (F.mul
                                (F.mul
                                  (nat F (Tautology.Nat.binom q j))
                                  (bernoulliSign F j))
                                (F.inv (nat F (j + 1)))) := by
                                exact F.mul_assoc
                                  (coefficient q)
                                  (F.mul
                                    (nat F (Tautology.Nat.binom q j))
                                    (bernoulliSign F j))
                                  (F.inv (nat F (j + 1)))
              _ = F.mul (coefficient q)
                    (finiteSum F
                      (fun j : Nat =>
                        F.mul
                          (F.mul
                            (nat F (Tautology.Nat.binom q j))
                            (bernoulliSign F j))
                          (F.inv (nat F (j + 1))))
                      (n + 1)) := by
                      exact finiteSum_mul_left F (coefficient q)
                        (fun j : Nat =>
                          F.mul
                            (F.mul
                              (nat F (Tautology.Nat.binom q j))
                              (bernoulliSign F j))
                            (F.inv (nat F (j + 1))))
                        (n + 1)
    _ = finiteSum F
          (fun q : Nat =>
            F.mul (coefficient q) (F.inv (nat F (q + 1))))
          (n + 1) := by
            apply finiteSum_congr_lt F
            intro q hq
            rw [reflected_power_average_padded
              (F := F) (q := q) (n := n) (by omega)]

private theorem finiteCoefficientAverage_split_first
    (coefficient : Nat -> alpha) (n : Nat) :
    finiteCoefficientAverage F coefficient n =
      F.add (coefficient 0)
        (finiteSum F
          (fun j : Nat =>
            F.mul (coefficient (j + 1))
              (F.inv (nat F (j + 2))))
          n) := by
  unfold finiteCoefficientAverage
  rw [finiteSum_split_first F
    (fun j : Nat =>
      F.mul (coefficient j) (F.inv (nat F (j + 1)))) n]
  rw [nat_one]
  rw [inv_one F]
  rw [F.mul_one]

private theorem finiteCoefficient_eq_of_derivative_and_average
    (c d : Nat -> alpha) (n : Nat)
    (hderivative : forall j : Nat, j < n ->
      F.mul (nat F (j + 1)) (c (j + 1)) =
        F.mul (nat F (j + 1)) (d (j + 1)))
    (haverage :
      finiteCoefficientAverage F c n =
        finiteCoefficientAverage F d n) :
    forall j : Nat, j < n + 1 -> c j = d j := by
  have hpositive : forall j : Nat, j < n -> c (j + 1) = d (j + 1) := by
    intro j hj
    exact mul_left_cancel_of_ne_zero F
      (nat_ne_zero_of_ne_zero F (by omega))
      (hderivative j hj)
  have htail :
      finiteSum F
          (fun j : Nat =>
            F.mul (c (j + 1)) (F.inv (nat F (j + 2)))) n =
        finiteSum F
          (fun j : Nat =>
            F.mul (d (j + 1)) (F.inv (nat F (j + 2)))) n := by
    apply finiteSum_congr_lt F
    intro j hj
    rw [hpositive j hj]
  have hzero : c 0 = d 0 := by
    rw [finiteCoefficientAverage_split_first] at haverage
    rw [finiteCoefficientAverage_split_first] at haverage
    rw [htail] at haverage
    exact add_right_cancel F haverage
  intro j hj
  cases j with
  | zero => exact hzero
  | succ j => exact hpositive j (by omega)

private def formalDerivativeCoefficient
    (coefficient : Nat -> alpha) (j : Nat) : alpha :=
  F.mul (nat F (j + 1)) (coefficient (j + 1))

private theorem reflectedCoefficient_derivative_term
    (coefficient : Nat -> alpha) {q j : Nat} :
    F.mul (nat F (j + 1))
        (F.mul
          (F.mul (coefficient (q + 1))
            (nat F (Tautology.Nat.binom (q + 1) (j + 1))))
          (bernoulliSign F (j + 1))) =
      F.neg
        (F.mul
          (F.mul (formalDerivativeCoefficient F coefficient q)
            (nat F (Tautology.Nat.binom q j)))
          (bernoulliSign F j)) := by
  by_cases hjq : j <= q
  · have hweighted :
        F.mul (nat F (j + 1))
            (nat F (Tautology.Nat.binom (q + 1) (j + 1))) =
          F.mul (nat F (q + 1))
            (nat F (Tautology.Nat.binom q j)) := by
      calc
        F.mul (nat F (j + 1))
            (nat F (Tautology.Nat.binom (q + 1) (j + 1))) =
            nat F
              ((j + 1) * Tautology.Nat.binom (q + 1) (j + 1)) := by
                rw [nat_mul]
        _ = nat F ((q + 1) * Tautology.Nat.binom q j) := by
                rw [Tautology.Nat.succ_mul_binom_succ hjq]
        _ = F.mul (nat F (q + 1))
              (nat F (Tautology.Nat.binom q j)) := by
                rw [nat_mul]
    rw [bernoulliSign_succ]
    rw [mul_neg F]
    rw [mul_neg F]
    congr 1
    unfold formalDerivativeCoefficient
    let A : alpha := nat F (j + 1)
    let B : alpha := nat F (q + 1)
    let C : alpha := nat F (Tautology.Nat.binom (q + 1) (j + 1))
    let D : alpha := nat F (Tautology.Nat.binom q j)
    let X : alpha := coefficient (q + 1)
    let S : alpha := bernoulliSign F j
    change F.mul A (F.mul (F.mul X C) S) =
      F.mul (F.mul (F.mul B X) D) S
    calc
      F.mul A (F.mul (F.mul X C) S) =
          F.mul (F.mul A (F.mul X C)) S := by
            exact Eq.symm (F.mul_assoc A (F.mul X C) S)
      _ = F.mul (F.mul (F.mul A X) C) S := by
            congr 1
            exact Eq.symm (F.mul_assoc A X C)
      _ = F.mul (F.mul (F.mul X A) C) S := by
            congr 1
            congr 1
            exact F.mul_comm A X
      _ = F.mul (F.mul X (F.mul A C)) S := by
            congr 1
            exact F.mul_assoc X A C
      _ = F.mul (F.mul X (F.mul B D)) S := by
            rw [hweighted]
      _ = F.mul (F.mul (F.mul X B) D) S := by
            congr 1
            exact Eq.symm (F.mul_assoc X B D)
      _ = F.mul (F.mul (F.mul B X) D) S := by
            congr 1
            congr 1
            exact F.mul_comm X B
  · have hqj : q < j := by omega
    rw [Tautology.Nat.binom_eq_zero_of_lt (by omega)]
    rw [Tautology.Nat.binom_eq_zero_of_lt hqj]
    rw [nat_zero]
    rw [F.mul_zero]
    rw [F.zero_mul]
    rw [F.mul_zero]
    rw [F.mul_zero]
    rw [F.zero_mul]
    rw [neg_zero F]

private theorem reflectedCoefficient_derivative
    (coefficient : Nat -> alpha) (n j : Nat) :
    F.mul (nat F (j + 1))
        (reflectedCoefficient F coefficient (n + 1) (j + 1)) =
      F.neg
        (reflectedCoefficient F
          (formalDerivativeCoefficient F coefficient) n j) := by
  unfold reflectedCoefficient
  rw [finiteSum_split_first F
    (fun q : Nat =>
      F.mul
        (F.mul (coefficient q)
          (nat F (Tautology.Nat.binom q (j + 1))))
        (bernoulliSign F (j + 1)))
    (n + 1)]
  rw [Tautology.Nat.binom_zero_succ]
  rw [nat_zero]
  rw [F.mul_zero]
  rw [F.zero_mul]
  rw [F.zero_add]
  rw [<- finiteSum_mul_left]
  calc
    finiteSum F
        (fun q : Nat =>
          F.mul (nat F (j + 1))
            (F.mul
              (F.mul (coefficient (q + 1))
                (nat F (Tautology.Nat.binom (q + 1) (j + 1))))
              (bernoulliSign F (j + 1))))
        (n + 1) =
        finiteSum F
          (fun q : Nat =>
            F.neg
              (F.mul
                (F.mul (formalDerivativeCoefficient F coefficient q)
                  (nat F (Tautology.Nat.binom q j)))
                (bernoulliSign F j)))
          (n + 1) := by
            apply finiteSum_congr F
            intro q
            exact reflectedCoefficient_derivative_term F coefficient
    _ = F.neg
          (finiteSum F
            (fun q : Nat =>
              F.mul
                (F.mul (formalDerivativeCoefficient F coefficient q)
                  (nat F (Tautology.Nat.binom q j)))
                (bernoulliSign F j))
            (n + 1)) := by
            exact finiteSum_neg F
              (fun q : Nat =>
                F.mul
                  (F.mul (formalDerivativeCoefficient F coefficient q)
                    (nat F (Tautology.Nat.binom q j)))
                  (bernoulliSign F j))
              (n + 1)

private theorem reflectedCoefficient_congr
    {c d : Nat -> alpha} (n j : Nat)
    (h : forall q : Nat, q < n + 1 -> c q = d q) :
    reflectedCoefficient F c n j = reflectedCoefficient F d n j := by
  unfold reflectedCoefficient
  apply finiteSum_congr_lt F
  intro q hq
  rw [h q hq]

private theorem reflectedCoefficient_scale
    (a : alpha) (coefficient : Nat -> alpha) (n j : Nat) :
    reflectedCoefficient F
        (fun q : Nat => F.mul a (coefficient q)) n j =
      F.mul a (reflectedCoefficient F coefficient n j) := by
  unfold reflectedCoefficient
  calc
    finiteSum F
        (fun q : Nat =>
          F.mul
            (F.mul (F.mul a (coefficient q))
              (nat F (Tautology.Nat.binom q j)))
            (bernoulliSign F j))
        (n + 1) =
        finiteSum F
          (fun q : Nat =>
            F.mul a
              (F.mul
                (F.mul (coefficient q)
                  (nat F (Tautology.Nat.binom q j)))
                (bernoulliSign F j)))
          (n + 1) := by
            apply finiteSum_congr F
            intro q
            calc
              F.mul
                  (F.mul (F.mul a (coefficient q))
                    (nat F (Tautology.Nat.binom q j)))
                  (bernoulliSign F j) =
                  F.mul
                    (F.mul a
                      (F.mul (coefficient q)
                        (nat F (Tautology.Nat.binom q j))))
                    (bernoulliSign F j) := by
                      congr 1
                      exact F.mul_assoc a (coefficient q)
                        (nat F (Tautology.Nat.binom q j))
              _ = F.mul a
                    (F.mul
                      (F.mul (coefficient q)
                        (nat F (Tautology.Nat.binom q j)))
                      (bernoulliSign F j)) := by
                      exact F.mul_assoc a
                        (F.mul (coefficient q)
                          (nat F (Tautology.Nat.binom q j)))
                        (bernoulliSign F j)
    _ = F.mul a
          (finiteSum F
            (fun q : Nat =>
              F.mul
                (F.mul (coefficient q)
                  (nat F (Tautology.Nat.binom q j)))
                (bernoulliSign F j))
            (n + 1)) := by
            exact finiteSum_mul_left F a
              (fun q : Nat =>
                F.mul
                  (F.mul (coefficient q)
                    (nat F (Tautology.Nat.binom q j)))
                  (bernoulliSign F j))
              (n + 1)

private theorem finiteCoefficientAverage_scale
    (a : alpha) (coefficient : Nat -> alpha) (n : Nat) :
    finiteCoefficientAverage F
        (fun j : Nat => F.mul a (coefficient j)) n =
      F.mul a (finiteCoefficientAverage F coefficient n) := by
  unfold finiteCoefficientAverage
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul (F.mul a (coefficient j))
            (F.inv (nat F (j + 1))))
        (n + 1) =
        finiteSum F
          (fun j : Nat =>
            F.mul a
              (F.mul (coefficient j)
                (F.inv (nat F (j + 1)))))
          (n + 1) := by
            apply finiteSum_congr F
            intro j
            exact F.mul_assoc a (coefficient j)
              (F.inv (nat F (j + 1)))
    _ = F.mul a
          (finiteSum F
            (fun j : Nat =>
              F.mul (coefficient j) (F.inv (nat F (j + 1))))
            (n + 1)) := by
            exact finiteSum_mul_left F a
              (fun j : Nat =>
                F.mul (coefficient j) (F.inv (nat F (j + 1))))
              (n + 1)

private theorem finiteCoefficientValue_scale
    (a : alpha) (coefficient : Nat -> alpha) (n : Nat) (t : alpha) :
    finiteCoefficientValue F
        (fun j : Nat => F.mul a (coefficient j)) n t =
      F.mul a (finiteCoefficientValue F coefficient n t) := by
  unfold finiteCoefficientValue
  calc
    finiteSum F
        (fun j : Nat =>
          F.mul (F.mul a (coefficient j)) (bernoulliPower F t j))
        (n + 1) =
        finiteSum F
          (fun j : Nat =>
            F.mul a
              (F.mul (coefficient j) (bernoulliPower F t j)))
          (n + 1) := by
            apply finiteSum_congr F
            intro j
            exact F.mul_assoc a (coefficient j) (bernoulliPower F t j)
    _ = F.mul a
          (finiteSum F
            (fun j : Nat =>
              F.mul (coefficient j) (bernoulliPower F t j))
            (n + 1)) := by
            exact finiteSum_mul_left F a
              (fun j : Nat =>
                F.mul (coefficient j) (bernoulliPower F t j))
              (n + 1)

private theorem reflected_bernoulliCoefficient :
    forall m j : Nat, j < m + 1 ->
      reflectedCoefficient F (bernoulliCoefficient F m) m j =
        F.mul (bernoulliSign F m) (bernoulliCoefficient F m j)
  | 0, j, hj => by
      have hj0 : j = 0 := by omega
      subst j
      unfold reflectedCoefficient bernoulliCoefficient
      rw [finiteSum_one]
      rw [Tautology.Nat.binom_zero_zero]
      rw [nat_one]
      rw [bernoulliSign_zero]
      rw [F.mul_one]
      rw [F.mul_one]
      rw [F.one_mul]
      rw [F.one_mul]
  | m + 1, j, hj => by
      let c : Nat -> alpha :=
        reflectedCoefficient F (bernoulliCoefficient F (m + 1)) (m + 1)
      let d : Nat -> alpha :=
        fun r : Nat =>
          F.mul (bernoulliSign F (m + 1))
            (bernoulliCoefficient F (m + 1) r)
      have hderivative : forall r : Nat, r < m + 1 ->
          F.mul (nat F (r + 1)) (c (r + 1)) =
            F.mul (nat F (r + 1)) (d (r + 1)) := by
        intro r hr
        unfold c d
        calc
          F.mul (nat F (r + 1))
              (reflectedCoefficient F
                (bernoulliCoefficient F (m + 1))
                (m + 1) (r + 1)) =
              F.neg
                (reflectedCoefficient F
                  (formalDerivativeCoefficient F
                    (bernoulliCoefficient F (m + 1))) m r) := by
                    exact reflectedCoefficient_derivative F
                      (bernoulliCoefficient F (m + 1)) m r
          _ = F.neg
                (reflectedCoefficient F
                  (fun q : Nat =>
                    F.mul (nat F (m + 1))
                      (bernoulliCoefficient F m q)) m r) := by
                    congr 1
                    apply reflectedCoefficient_congr F
                    intro q hq
                    unfold formalDerivativeCoefficient
                    exact bernoulliCoefficient_derivative F (by omega)
          _ = F.neg
                (F.mul (nat F (m + 1))
                  (reflectedCoefficient F
                    (bernoulliCoefficient F m) m r)) := by
                    rw [reflectedCoefficient_scale]
          _ = F.neg
                (F.mul (nat F (m + 1))
                  (F.mul (bernoulliSign F m)
                    (bernoulliCoefficient F m r))) := by
                    rw [reflected_bernoulliCoefficient m r (by omega)]
          _ = F.neg
                (F.mul (bernoulliSign F m)
                  (F.mul (nat F (m + 1))
                    (bernoulliCoefficient F m r))) := by
                    congr 1
                    calc
                      F.mul (nat F (m + 1))
                          (F.mul (bernoulliSign F m)
                            (bernoulliCoefficient F m r)) =
                          F.mul
                            (F.mul (nat F (m + 1))
                              (bernoulliSign F m))
                            (bernoulliCoefficient F m r) := by
                              rw [F.mul_assoc]
                      _ = F.mul
                            (F.mul (bernoulliSign F m)
                              (nat F (m + 1)))
                            (bernoulliCoefficient F m r) := by
                              rw [F.mul_comm
                                (nat F (m + 1))
                                (bernoulliSign F m)]
                      _ = F.mul (bernoulliSign F m)
                            (F.mul (nat F (m + 1))
                              (bernoulliCoefficient F m r)) := by
                              rw [F.mul_assoc]
          _ = F.neg
                (F.mul (bernoulliSign F m)
                  (F.mul (nat F (r + 1))
                    (bernoulliCoefficient F (m + 1) (r + 1)))) := by
                    rw [bernoulliCoefficient_derivative F (by omega)]
          _ = F.neg
                (F.mul (nat F (r + 1))
                  (F.mul (bernoulliSign F m)
                    (bernoulliCoefficient F (m + 1) (r + 1)))) := by
                    congr 1
                    calc
                      F.mul (bernoulliSign F m)
                          (F.mul (nat F (r + 1))
                            (bernoulliCoefficient F (m + 1) (r + 1))) =
                          F.mul
                            (F.mul (bernoulliSign F m)
                              (nat F (r + 1)))
                            (bernoulliCoefficient F (m + 1) (r + 1)) := by
                              rw [F.mul_assoc]
                      _ = F.mul
                            (F.mul (nat F (r + 1))
                              (bernoulliSign F m))
                            (bernoulliCoefficient F (m + 1) (r + 1)) := by
                              rw [F.mul_comm
                                (bernoulliSign F m)
                                (nat F (r + 1))]
                      _ = F.mul (nat F (r + 1))
                            (F.mul (bernoulliSign F m)
                              (bernoulliCoefficient F (m + 1) (r + 1)) ) := by
                              rw [F.mul_assoc]
          _ = F.mul (nat F (r + 1))
                (F.neg
                  (F.mul (bernoulliSign F m)
                    (bernoulliCoefficient F (m + 1) (r + 1)))) := by
                    exact Eq.symm
                      (mul_neg F (nat F (r + 1))
                        (F.mul (bernoulliSign F m)
                          (bernoulliCoefficient F (m + 1) (r + 1))))
          _ = F.mul (nat F (r + 1))
                (F.mul (F.neg (bernoulliSign F m))
                  (bernoulliCoefficient F (m + 1) (r + 1))) := by
                    rw [neg_mul F]
          _ = F.mul (nat F (r + 1))
                (F.mul (bernoulliSign F (m + 1))
                  (bernoulliCoefficient F (m + 1) (r + 1))) := by
                    rw [bernoulliSign_succ]
      have hcAverage : finiteCoefficientAverage F c (m + 1) = F.zero := by
        unfold c
        rw [reflectedCoefficient_average]
        exact bernoulliCoefficient_average_zero F (by omega)
      have hdAverage : finiteCoefficientAverage F d (m + 1) = F.zero := by
        unfold d
        rw [finiteCoefficientAverage_scale]
        rw [bernoulliCoefficient_average_zero F (by omega)]
        rw [F.mul_zero]
      exact finiteCoefficient_eq_of_derivative_and_average F c d (m + 1)
        hderivative (by rw [hcAverage, hdAverage]) j hj

private theorem bernoulliSign_eq_natRec :
    forall n : Nat,
      bernoulliSign F n =
        Nat.rec F.one (fun (_ : Nat) (s : alpha) => F.neg s) n
  | 0 => rfl
  | n + 1 => by
      rw [bernoulliSign_succ]
      rw [bernoulliSign_eq_natRec n]

/-- Reflection about the midpoint of the unit interval: the value at
`1 - t` is the value at `t` up to an alternating sign, `+1` on even indices
and `-1` on odd ones, the sign spelled as a `Nat.rec` alternation because no
power notation exists at this level. The proof compares coefficient
sequences: the reflected coefficients are shown to be the alternated
originals by matching their scaled derivatives and their averages. -/
theorem bernoulliPolynomialValue_reflection (m : Nat) (t : alpha) :
    bernoulliPolynomialValue F m (F.sub F.one t) =
      F.mul (Nat.rec F.one (fun (_ : Nat) (s : alpha) => F.neg s) m)
        (bernoulliPolynomialValue F m t) := by
  calc
    bernoulliPolynomialValue F m (F.sub F.one t) =
        finiteCoefficientValue F (bernoulliCoefficient F m) m
          (F.sub F.one t) := by
            exact bernoulliPolynomialValue_eq_coefficientValue F m
              (F.sub F.one t)
    _ = finiteCoefficientValue F
          (reflectedCoefficient F (bernoulliCoefficient F m) m) m t := by
            exact Eq.symm
              (reflectedCoefficient_value F
                (bernoulliCoefficient F m) m t)
    _ = finiteCoefficientValue F
          (fun j : Nat =>
            F.mul (bernoulliSign F m) (bernoulliCoefficient F m j))
          m t := by
            unfold finiteCoefficientValue
            apply finiteSum_congr_lt F
            intro j hj
            rw [reflected_bernoulliCoefficient F m j hj]
    _ = F.mul (bernoulliSign F m)
          (finiteCoefficientValue F (bernoulliCoefficient F m) m t) := by
            exact finiteCoefficientValue_scale F
              (bernoulliSign F m) (bernoulliCoefficient F m) m t
    _ = F.mul (bernoulliSign F m)
          (bernoulliPolynomialValue F m t) := by
            rw [bernoulliPolynomialValue_eq_coefficientValue]
    _ = F.mul
          (Nat.rec F.one (fun (_ : Nat) (s : alpha) => F.neg s) m)
          (bernoulliPolynomialValue F m t) := by
            rw [bernoulliSign_eq_natRec]

private theorem bernoulliSign_even :
    forall r : Nat, bernoulliSign F (2 * r) = F.one
  | 0 => rfl
  | r + 1 => by
      have hindex : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
      rw [hindex]
      rw [bernoulliSign_succ]
      rw [bernoulliSign_succ]
      rw [bernoulliSign_even r]
      rw [neg_neg F]

private theorem natRec_sign_odd (r : Nat) :
    Nat.rec F.one (fun (_ : Nat) (s : alpha) => F.neg s)
        (2 * r + 1) =
      F.neg F.one := by
  calc
    Nat.rec F.one (fun (_ : Nat) (s : alpha) => F.neg s)
        (2 * r + 1) = bernoulliSign F (2 * r + 1) := by
          exact Eq.symm (bernoulliSign_eq_natRec F (2 * r + 1))
    _ = F.neg (bernoulliSign F (2 * r)) := by
          exact bernoulliSign_succ F (2 * r)
    _ = F.neg F.one := by rw [bernoulliSign_even]

/-- Every Bernoulli number of odd index past the first vanishes. The argument
evaluates the reflection symmetry at `t = 0` and reads off `B m = -B m` for
odd `m`, using the endpoint equality `bernoulliPolynomialValue_one_eq`; the
factor `2` is then cancelled. The index `1` is the exception, its value
being `-1 / 2`. -/
theorem bernoulliNumber_odd_eq_zero {r : Nat} (hr : 0 < r) :
    bernoulliNumber F (2 * r + 1) = F.zero := by
  let m := 2 * r + 1
  have hm : 2 <= m := by omega
  have hreflection := bernoulliPolynomialValue_reflection F m F.zero
  rw [sub_zero F] at hreflection
  rw [bernoulliPolynomialValue_one_eq F hm] at hreflection
  rw [bernoulliPolynomialValue_zero] at hreflection
  rw [natRec_sign_odd F r] at hreflection
  rw [neg_mul F] at hreflection
  rw [F.one_mul] at hreflection
  have hadd :
      F.add (bernoulliNumber F m) (bernoulliNumber F m) = F.zero := by
    calc
      F.add (bernoulliNumber F m) (bernoulliNumber F m) =
          F.add (bernoulliNumber F m)
            (F.neg (bernoulliNumber F m)) := by
              congr 1
      _ = F.zero := by rw [F.add_neg]
  apply eq_zero_of_mul_eq_zero_left F
    (nat_ne_zero_of_ne_zero F (n := 2) (by omega))
  calc
    F.mul (nat F 2) (bernoulliNumber F m) =
        F.add (bernoulliNumber F m) (bernoulliNumber F m) := by
          rw [nat_succ F 1]
          rw [nat_one]
          rw [F.add_mul]
          rw [F.one_mul]
    _ = F.zero := hadd

/-- The envelope of the `m`-th polynomial: the binomially weighted absolute
values of the numbers `B k`, `k <= m`, summed. It carries no dependence on
`t`, so a single field element bounds the polynomial on the whole unit
interval, by the theorem below. -/
noncomputable def bernoulliAbsEnvelope (m : Nat) : alpha :=
  finiteSum F
    (fun k : Nat =>
      F.mul (nat F (Tautology.Nat.binom m k))
        (abs F (bernoulliNumber F k)))
    (m + 1)

theorem bernoulliAbsEnvelope_nonneg (m : Nat) :
    F.le F.zero (bernoulliAbsEnvelope F m) := by
  unfold bernoulliAbsEnvelope
  have hzero :
      finiteSum F (fun _ : Nat => F.zero) (m + 1) = F.zero := by
    apply finiteSum_eq_zero F
    intro k hk
    rfl
  rw [<- hzero]
  exact finiteSum_le_of_pointwise_le F
    (fun _ : Nat => F.zero)
    (fun k : Nat =>
      F.mul (nat F (Tautology.Nat.binom m k))
        (abs F (bernoulliNumber F k)))
    (m + 1)
    (fun k _hk =>
      F.mul_nonneg
        (nat_nonneg F (Tautology.Nat.binom m k))
        (abs_nonneg F (bernoulliNumber F k)))

private theorem bernoulliPower_nonneg
    {t : alpha} (ht : F.le F.zero t) :
    forall n : Nat,
      F.le F.zero (bernoulliPower F t n)
  | 0 => by
      rw [bernoulliPower_zero]
      exact zero_le_one F
  | n + 1 => by
      rw [bernoulliPower_succ]
      exact F.mul_nonneg ht (bernoulliPower_nonneg ht n)

private theorem bernoulliPower_le_one
    {t : alpha} (ht0 : F.le F.zero t) (ht1 : F.le t F.one) :
    forall n : Nat,
      F.le (bernoulliPower F t n) F.one
  | 0 => by
      rw [bernoulliPower_zero]
      exact F.le_refl F.one
  | n + 1 => by
      rw [bernoulliPower_succ]
      have hfirst :
          F.le (F.mul t (bernoulliPower F t n))
            (F.mul F.one (bernoulliPower F t n)) :=
        mul_le_mul_nonneg_right F ht1
          (bernoulliPower_nonneg F ht0 n)
      rw [F.one_mul] at hfirst
      exact F.le_trans hfirst (bernoulliPower_le_one ht0 ht1 n)

private theorem abs_bernoulliPower_le_one
    {t : alpha} (ht0 : F.le F.zero t) (ht1 : F.le t F.one)
    (n : Nat) :
    F.le (abs F (bernoulliPower F t n)) F.one := by
  rw [abs_of_nonneg F (bernoulliPower_nonneg F ht0 n)]
  exact bernoulliPower_le_one F ht0 ht1 n

private theorem abs_bernoulliPolynomial_term_le
    {m : Nat} {t : alpha}
    (ht0 : F.le F.zero t) (ht1 : F.le t F.one)
    (k : Nat) :
    F.le
      (abs F
        (F.mul
          (F.mul (nat F (Tautology.Nat.binom m k))
            (bernoulliNumber F k))
          (bernoulliPower F t (m - k))))
      (F.mul (nat F (Tautology.Nat.binom m k))
        (abs F (bernoulliNumber F k))) := by
  rw [abs_mul F]
  rw [abs_mul F]
  rw [abs_of_nonneg F
    (nat_nonneg F (Tautology.Nat.binom m k))]
  let C : alpha :=
    F.mul (nat F (Tautology.Nat.binom m k))
      (abs F (bernoulliNumber F k))
  change
    F.le
      (F.mul C (abs F (bernoulliPower F t (m - k)))) C
  have hC : F.le F.zero C := by
    unfold C
    exact F.mul_nonneg
      (nat_nonneg F (Tautology.Nat.binom m k))
      (abs_nonneg F (bernoulliNumber F k))
  have hmul :
      F.le (F.mul C (abs F (bernoulliPower F t (m - k))))
        (F.mul C F.one) :=
    mul_le_mul_nonneg_left F
      (abs_bernoulliPower_le_one F ht0 ht1 (m - k)) hC
  rwa [F.mul_one] at hmul

/-- One bound for the whole unit interval: the absolute value of the `m`-th
polynomial at any `t` between zero and one stays under the envelope. The
price of a `t`-independent bound is that all cancellation is discarded -- the
estimate is the triangle inequality plus the fact that a power of `t` is at
most one on the unit interval. -/
theorem abs_bernoulliPolynomialValue_le_envelope
    {m : Nat} {t : alpha}
    (ht0 : F.le F.zero t) (ht1 : F.le t F.one) :
    F.le (abs F (bernoulliPolynomialValue F m t))
      (bernoulliAbsEnvelope F m) := by
  unfold bernoulliPolynomialValue bernoulliAbsEnvelope
  let term : Nat -> alpha :=
    fun k : Nat =>
      F.mul
        (F.mul (nat F (Tautology.Nat.binom m k))
          (bernoulliNumber F k))
        (bernoulliPower F t (m - k))
  exact F.le_trans
    (abs_finiteSum_le_finiteSum_abs F term (m + 1))
    (finiteSum_le_of_pointwise_le F
      (fun k : Nat => abs F (term k))
      (fun k : Nat =>
        F.mul (nat F (Tautology.Nat.binom m k))
          (abs F (bernoulliNumber F k)))
      (m + 1)
      (fun k hk => abs_bernoulliPolynomial_term_le F ht0 ht1 k))

end IsOrderedFieldBaseLike
end Tautology
