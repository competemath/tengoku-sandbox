import Init.Data.Nat.Lemmas

/-!
# The factorial, and the one estimate the library needs from it

The definition and its small identities take a few lines; the rest of the file
exists for `exists_mul_pow_two_mul_lt_factorial_two_mul`, which says that for
any positive `a` and `m` there is a positive `n` with
`m * a ^ (2 * n) < factorial (2 * n)`. In words: the factorial eventually
beats any geometric progression, however large its ratio and however large a
constant multiple it is given, and it does so at an even index.

That last clause is not decoration. The consumer is
`Tautology.RealDerivative.Integral.Applications.PiSquaredIrrational`, where
Niven's proof needs the estimate at `2 * n` precisely because its auxiliary
polynomial has even degree.

## Why `factorialTail` exists

Comparing a factorial with a power directly is awkward, so the argument splits
`factorial (s + t)` into `factorialTail s t * factorial s`, where
`factorialTail s t` is the product of the `t` factors above `s`. Each of those
factors is at least `s + 1`, which gives `(s + 1) ^ t <= factorialTail s t` --
a geometric lower bound on a piece of the factorial, and the step that turns
the comparison into arithmetic. Setting `s = t = n` and choosing `n` past
`m * a * a` then closes the estimate.

## Position in the development

Bottom of the dependency order, on `Nat` alone. Besides Niven's proof its
consumers are `Tautology.RealDerivative.Taylor.Basic` (the factorial in the
remainder terms), `Tautology.RealBootstrap.Formal.Bell.Exponential` and
`Tautology.RealDerivative.FaaDiBruno.InverseEuler`.

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

/-- The factorial by structural recursion: `1` at zero and
`(n + 1) * factorial n` at a successor, so each step multiplies in the new
largest factor. -/
def factorial : _root_.Nat -> _root_.Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_zero :
    factorial 0 = 1 :=
  rfl

theorem factorial_succ (n : _root_.Nat) :
    factorial (n + 1) = (n + 1) * factorial n :=
  rfl

theorem factorial_one :
    factorial 1 = 1 := by
  rw [factorial_succ]
  rw [factorial_zero]

theorem factorial_two :
    factorial 2 = 2 := by
  rw [factorial_succ]
  rw [factorial_one]

theorem factorial_ne_zero :
    forall n : _root_.Nat, Not (factorial n = 0)
  | 0 => by
      rw [factorial_zero]
      exact _root_.Nat.succ_ne_zero 0
  | n + 1 => by
      rw [factorial_succ]
      intro h
      have hleft : Not (n + 1 = 0) := _root_.Nat.succ_ne_zero n
      have hright : Not (factorial n = 0) := factorial_ne_zero n
      exact Or.elim (_root_.Nat.mul_eq_zero.mp h)
        (fun hzero => hleft hzero)
        (fun hzero => hright hzero)

/-- The block of the `t` factors just above `s`, from `s + 1` to `s + t`, so
that `factorial (s + t) = factorialTail s t * factorial s`. Every factor is
at least `s + 1`, which is what turns a comparison with a power into
arithmetic. -/
def factorialTail (s : _root_.Nat) : _root_.Nat -> _root_.Nat
  | 0 => 1
  | t + 1 => (s + t + 1) * factorialTail s t

/-- The splitting identity behind the estimate: a factorial at a sum factors
into the block above `s` and the factorial of `s` itself. Induction on `t`,
one factor per step. -/
theorem factorial_add_eq_factorialTail_mul
    (s t : _root_.Nat) :
    factorial (s + t) = factorialTail s t * factorial s := by
  induction t with
  | zero =>
      rw [_root_.Nat.add_zero, factorialTail, _root_.Nat.one_mul]
  | succ t ih =>
      rw [show s + (t + 1) = (s + t) + 1 by omega]
      rw [factorial_succ, factorialTail, ih, _root_.Nat.mul_assoc]

private theorem pow_succ_le_factorialTail
    (s t : _root_.Nat) :
    (s + 1) ^ t <= factorialTail s t := by
  induction t with
  | zero =>
      exact _root_.Nat.le_refl 1
  | succ t ih =>
      rw [factorialTail, _root_.Nat.pow_succ]
      have hfactor : s + 1 <= s + t + 1 := by omega
      calc
        (s + 1) ^ t * (s + 1) =
            (s + 1) * (s + 1) ^ t :=
          _root_.Nat.mul_comm _ _
        _ <= (s + t + 1) * factorialTail s t :=
          _root_.Nat.mul_le_mul hfactor ih

private theorem self_le_pow_of_pos_of_pos
    (a n : _root_.Nat) (ha : 0 < a) (hn : 0 < n) :
    a <= a ^ n := by
  cases n with
  | zero => omega
  | succ k =>
      rw [_root_.Nat.pow_succ]
      exact _root_.Nat.le_mul_of_pos_left a (_root_.Nat.pow_pos ha)

private theorem pow_lt_factorial_two_mul
    (n : _root_.Nat) (hn : 0 < n) :
    n ^ n < factorial (2 * n) := by
  have hnne : Not (n = 0) := by omega
  have hfactorialPos : 0 < factorial n := by
    have hfactorialOne : 1 <= factorial n :=
      _root_.Nat.one_le_iff_ne_zero.mpr (factorial_ne_zero n)
    omega
  calc
    n ^ n < (n + 1) ^ n :=
      _root_.Nat.pow_lt_pow_left (_root_.Nat.lt_succ_self n) hnne
    _ <= factorialTail n n := pow_succ_le_factorialTail n n
    _ <= factorialTail n n * factorial n :=
      _root_.Nat.le_mul_of_pos_right (factorialTail n n) hfactorialPos
    _ = factorial (2 * n) := by
      rw [show 2 * n = n + n by omega]
      exact (factorial_add_eq_factorialTail_mul n n).symm

/-- The factorial eventually beats any geometric progression, constant
multiplier included: for positive `a` and `m` there is a positive `n` with
`m * a ^ (2 * n) < factorial (2 * n)`. The index is even because the
consumer, Niven's proof in
`Tautology.RealDerivative.Integral.Applications.PiSquaredIrrational`, reads the
estimate at the even degree of its auxiliary polynomial. The witness is
`m * a * a + 1`, which first overpowers the geometric side at `n ^ n` and
then hands over to the factorial comparison. -/
theorem exists_mul_pow_two_mul_lt_factorial_two_mul
    (a m : _root_.Nat) (ha : 0 < a) (hm : 0 < m) :
    Exists (fun n : _root_.Nat =>
      And (0 < n) (m * a ^ (2 * n) < factorial (2 * n))) := by
  let n := m * a * a + 1
  have hn : 0 < n := by
    have hproduct : 0 < m * a * a :=
      _root_.Nat.mul_pos (_root_.Nat.mul_pos hm ha) ha
    dsimp [n]
    omega
  refine Exists.intro n (And.intro hn ?_)
  have hgeometric : m * a ^ (2 * n) < n ^ n := by
    have hbase : m * (a * a) < n := by
      dsimp [n]
      rw [<- _root_.Nat.mul_assoc]
      omega
    have hmpow : m <= m ^ n :=
      self_le_pow_of_pos_of_pos m n hm hn
    have hmulPower :
        m * (a * a) ^ n <= (m * (a * a)) ^ n := by
      calc
        m * (a * a) ^ n <= m ^ n * (a * a) ^ n :=
          _root_.Nat.mul_le_mul_right ((a * a) ^ n) hmpow
        _ = (m * (a * a)) ^ n :=
          (_root_.Nat.mul_pow m (a * a) n).symm
    have hstrict : (m * (a * a)) ^ n < n ^ n :=
      _root_.Nat.pow_lt_pow_left hbase (by omega)
    calc
      m * a ^ (2 * n) = m * (a * a) ^ n := by
        rw [show 2 * n = n + n by omega]
        rw [_root_.Nat.pow_add, _root_.Nat.mul_pow]
      _ <= (m * (a * a)) ^ n := hmulPower
      _ < n ^ n := hstrict
  have hfactorial : n ^ n < factorial (2 * n) :=
    pow_lt_factorial_two_mul n hn
  exact _root_.Nat.lt_trans hgeometric hfactorial

end Nat
end Tautology
