import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra
import Tengoku.Tautology.Tautology.RealBootstrap.InternalNat

/-!
# Finite sums

Sums of the first `n` terms of a sequence, defined by recursion, together with
the whole calculus of manipulating them: congruence, additivity, scalar
factors, pointwise comparison, telescoping, splitting and reindexing, Fubini
for double sums, and the even-odd pairing.

This is deliberately not a theory of series. There is no limit anywhere in the
file; a finite sum is a finite object, and every statement is an identity or an
inequality between finite objects. That is what lets the library talk about
budgets and estimates -- in `Tautology.RealSequence.PositiveSeries`, in the
null-set covers of `RealNegligibility` -- without any convergence theory being
available yet.

## Position and role

Implementation module over an arbitrary ordered field, built on
`Tautology.RealBootstrap.OrderAlgebra` and
`Tautology.RealBootstrap.InternalNat`. It is the base of the Bernoulli
development and of the truncated power series machinery.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The sum of the first `n` terms of `term`, by primitive recursion on `n`,
with the new summand added on the right. Both defining equations hold by
`rfl` and are restated as `finiteSum_zero` and `finiteSum_succ` so that every
later argument can rewrite with them. -/
def finiteSum (term : Nat -> alpha) : Nat -> alpha
  | 0 => F.zero
  | n + 1 => F.add (finiteSum term n) (term n)

theorem finiteSum_zero (term : Nat -> alpha) :
    finiteSum F term 0 = F.zero := rfl

theorem finiteSum_succ (term : Nat -> alpha) (n : Nat) :
    finiteSum F term (n + 1) =
      F.add (finiteSum F term n) (term n) := rfl

theorem finiteSum_one (term : Nat -> alpha) :
    finiteSum F term 1 = term 0 := by
  rw [finiteSum_succ, finiteSum_zero]
  rw [F.zero_add]

theorem finiteSum_congr
    {term term' : Nat -> alpha}
    (h : forall k : Nat, term k = term' k) :
    forall n : Nat, finiteSum F term n = finiteSum F term' n
  | 0 => rfl
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_succ]
      rw [finiteSum_congr h n, h n]

theorem finiteSum_congr_lt
    {term term' : Nat -> alpha} :
    forall n : Nat,
      (forall k : Nat, k < n -> term k = term' k) ->
      finiteSum F term n = finiteSum F term' n
  | 0, _ => rfl
  | n + 1, h => by
      rw [finiteSum_succ, finiteSum_succ]
      rw [finiteSum_congr_lt n
        (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
      rw [h n (Nat.lt_succ_self n)]

theorem finiteSum_add (u v : Nat -> alpha) :
    forall n : Nat,
      finiteSum F (fun k : Nat => F.add (u k) (v k)) n =
        F.add (finiteSum F u n) (finiteSum F v n)
  | 0 => by
      rw [finiteSum_zero, finiteSum_zero, finiteSum_zero]
      rw [F.add_zero]
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_succ, finiteSum_succ]
      rw [finiteSum_add u v n]
      exact add_add_add_comm F
        (finiteSum F u n) (finiteSum F v n) (u n) (v n)

theorem finiteSum_le_of_pointwise_le
    (u v : Nat -> alpha) :
    forall n : Nat,
      (forall k : Nat, k < n -> F.le (u k) (v k)) ->
        F.le (finiteSum F u n) (finiteSum F v n)
  | 0, _ => by
      rw [finiteSum_zero, finiteSum_zero]
      exact F.le_refl F.zero
  | n + 1, hle => by
      rw [finiteSum_succ, finiteSum_succ]
      exact add_le_add F
        (finiteSum_le_of_pointwise_le u v n
          (fun k hk => hle k
            (Nat.lt_trans hk (Nat.lt_succ_self n))))
        (hle n (Nat.lt_succ_self n))

theorem finiteSum_mul_left (c : alpha) (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F (fun k : Nat => F.mul c (term k)) n =
        F.mul c (finiteSum F term n)
  | 0 => by
      rw [finiteSum_zero, finiteSum_zero]
      exact Eq.symm (F.mul_zero c)
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_succ]
      rw [finiteSum_mul_left c term n]
      rw [F.mul_add]

theorem finiteSum_mul_right (term : Nat -> alpha) (c : alpha) :
    forall n : Nat,
      finiteSum F (fun k : Nat => F.mul (term k) c) n =
        F.mul (finiteSum F term n) c
  | 0 => by
      rw [finiteSum_zero, finiteSum_zero]
      exact Eq.symm (zero_mul F c)
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_succ]
      rw [finiteSum_mul_right term c n]
      rw [F.add_mul]

theorem finiteSum_eq_zero
    {term : Nat -> alpha} :
    forall n : Nat,
      (forall k : Nat, k < n -> term k = F.zero) ->
        finiteSum F term n = F.zero
  | 0, _ => rfl
  | n + 1, h => by
      rw [finiteSum_succ]
      rw [finiteSum_eq_zero n
        (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
      rw [h n (Nat.lt_succ_self n)]
      rw [F.add_zero]

/-- A sum collapses to its one nonzero summand: if `k` lies inside the window
and every other summand below `n` vanishes, the total is `term k` alone. This
is the device that lets a single term be compared against a whole sum, as in
`finiteSum_term_le_of_nonneg` below. -/
theorem finiteSum_eq_single_of_eq_zero_off
    {term : Nat -> alpha} :
    forall {n k : Nat},
      k < n ->
      (forall j : Nat, j < n -> Not (j = k) ->
        term j = F.zero) ->
      finiteSum F term n = term k
  | 0, k, hk, _ => by
      exact False.elim (Nat.not_lt_zero k hk)
  | n + 1, k, hk, hzero => by
      by_cases hkn : k = n
      case pos =>
        rw [hkn]
        rw [finiteSum_succ]
        have hprefix_zero :
            finiteSum F term n = F.zero :=
          finiteSum_eq_zero F (term := term) n
            (fun j hj =>
              hzero j (Nat.lt_trans hj (Nat.lt_succ_self n)) (by
                intro hbad
                omega))
        rw [hprefix_zero, F.zero_add]
      case neg =>
        have hk_lt_n : k < n := by
          omega
        rw [finiteSum_succ]
        have hlast_zero : term n = F.zero :=
          hzero n (Nat.lt_succ_self n) (by
            intro hbad
            exact hkn hbad.symm)
        rw [hlast_zero, F.add_zero]
        exact finiteSum_eq_single_of_eq_zero_off hk_lt_n
          (fun j hj hne =>
            hzero j (Nat.lt_trans hj (Nat.lt_succ_self n)) hne)

theorem finiteSum_nonneg
    (term : Nat -> alpha) (n : Nat)
    (hnonneg : forall k : Nat, k < n -> F.le F.zero (term k)) :
    F.le F.zero (finiteSum F term n) := by
  have hzero :
      finiteSum F (fun _ : Nat => F.zero) n = F.zero :=
    finiteSum_eq_zero F n (fun _ _ => rfl)
  rw [← hzero]
  exact finiteSum_le_of_pointwise_le F
    (fun _ : Nat => F.zero) term n hnonneg

theorem finiteSum_term_le_of_nonneg
    (term : Nat -> alpha) {n k : Nat}
    (hk : k < n)
    (hnonneg : forall j : Nat, j < n -> F.le F.zero (term j)) :
    F.le (term k) (finiteSum F term n) := by
  let singleton : Nat -> alpha :=
    fun j => if j = k then term k else F.zero
  have hsingleton : finiteSum F singleton n = term k := by
    simpa [singleton] using
      (finiteSum_eq_single_of_eq_zero_off F
        (term := singleton) hk (by
          intro j _hj hne
          simp [singleton, hne]))
  rw [← hsingleton]
  apply finiteSum_le_of_pointwise_le F
  intro j hj
  dsimp [singleton]
  by_cases hjk : j = k
  · rw [ite_eq_left hjk, hjk]
    exact F.le_refl (term k)
  · rw [ite_eq_right hjk]
    exact hnonneg j hj

theorem finiteSum_eq_zero_of_nonneg_terms
    {term : Nat -> alpha} (n : Nat)
    (hnonneg : forall k : Nat, k < n -> F.le F.zero (term k))
    (hsum : finiteSum F term n = F.zero)
    (k : Nat) (hk : k < n) :
    term k = F.zero := by
  apply F.le_antisymm
  · rw [← hsum]
    exact finiteSum_term_le_of_nonneg F term hk hnonneg
  · exact hnonneg k hk

/-- The sum of `n` copies of `c`. The number of summands enters the field as
the embedded natural `nat F n`, which is how counting appears on the right of
an identity between field elements. -/
theorem finiteSum_const (c : alpha) :
    forall n : Nat,
      finiteSum F (fun _ : Nat => c) n =
        F.mul (nat F n) c
  | 0 => by
      rw [finiteSum_zero, nat_zero]
      exact Eq.symm (F.zero_mul c)
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_const c n]
      rw [nat_succ]
      change
        F.add (F.mul (nat F n) c) c =
          F.mul (F.add (nat F n) F.one) c
      rw [F.add_mul]
      rw [F.one_mul]

/-- Interchange of the order of summation over the full `p`-by-`q` rectangle.
Triangular windows are not rectangles and are handled separately, by the
reindexing of `finiteSum_triangle_swap` below. -/
theorem finiteSum_fubini (term : Nat -> Nat -> alpha) :
    forall p q : Nat,
      finiteSum F
        (fun i : Nat => finiteSum F (fun j : Nat => term i j) q) p =
      finiteSum F
        (fun j : Nat => finiteSum F (fun i : Nat => term i j) p) q
  | 0, q => by
      rw [finiteSum_zero]
      calc
        F.zero =
            finiteSum F (fun _ : Nat => F.zero) q := by
            rw [finiteSum_const]
            rw [F.mul_zero]
        _ =
            finiteSum F
              (fun j : Nat =>
                finiteSum F (fun i : Nat => term i j) 0) q := by
            apply finiteSum_congr F
            intro j
            rw [finiteSum_zero]
  | p + 1, q => by
      rw [finiteSum_succ]
      rw [finiteSum_fubini term p q]
      calc
        F.add
            (finiteSum F
              (fun j : Nat =>
                finiteSum F (fun i : Nat => term i j) p) q)
            (finiteSum F (fun j : Nat => term p j) q) =
            finiteSum F
              (fun j : Nat =>
                F.add
                  (finiteSum F (fun i : Nat => term i j) p)
                  (term p j)) q := by
            exact Eq.symm
              (finiteSum_add F
                (fun j : Nat =>
                  finiteSum F (fun i : Nat => term i j) p)
                (fun j : Nat => term p j) q)
        _ =
            finiteSum F
              (fun j : Nat =>
                finiteSum F (fun i : Nat => term i j) (p + 1)) q := by
            apply finiteSum_congr F
            intro j
            rw [finiteSum_succ]

/-- One growth step for a triangular double sum: enlarging the window from `m`
to `m + 1` splits it into the smaller triangle plus its new boundary row, the
entries `term m j` of first index `m`. This is the induction step behind
`finiteSum_triangle_swap`. -/
theorem finiteSum_triangle_extend
    (term : Nat -> Nat -> alpha) (m : Nat) :
    finiteSum F
        (fun j : Nat =>
          finiteSum F (fun h : Nat => term (j + h) j)
            (m + 1 - j))
        (m + 1) =
      F.add
        (finiteSum F
          (fun j : Nat =>
            finiteSum F (fun h : Nat => term (j + h) j)
              (m - j))
          m)
        (finiteSum F (fun j : Nat => term m j) (m + 1)) := by
  rw [finiteSum_succ]
  have hprefix :
      finiteSum F
          (fun j : Nat =>
            finiteSum F (fun h : Nat => term (j + h) j)
              (m + 1 - j))
          m =
        F.add
          (finiteSum F
            (fun j : Nat =>
              finiteSum F (fun h : Nat => term (j + h) j)
                (m - j))
            m)
          (finiteSum F (fun j : Nat => term m j) m) := by
    calc
      finiteSum F
          (fun j : Nat =>
            finiteSum F (fun h : Nat => term (j + h) j)
              (m + 1 - j))
          m =
          finiteSum F
            (fun j : Nat =>
              F.add
                (finiteSum F (fun h : Nat => term (j + h) j)
                  (m - j))
                (term m j))
            m := by
            apply finiteSum_congr_lt F
            intro j hj
            have hlen : m + 1 - j = (m - j) + 1 := by
              omega
            rw [hlen]
            rw [finiteSum_succ]
            have hidx : j + (m - j) = m := by
              omega
            rw [hidx]
      _ =
          F.add
            (finiteSum F
              (fun j : Nat =>
                finiteSum F (fun h : Nat => term (j + h) j)
                  (m - j))
              m)
            (finiteSum F (fun j : Nat => term m j) m) := by
            rw [finiteSum_add]
  rw [hprefix]
  have hlast :
      finiteSum F (fun h : Nat => term (m + h) m)
          (m + 1 - m) =
        term m m := by
    have hlen : m + 1 - m = 1 := by
      omega
    rw [hlen]
    rw [finiteSum_one]
    have hidx : m + 0 = m := by
      omega
    rw [hidx]
  rw [hlast]
  rw [finiteSum_succ]
  rw [F.add_assoc]

/-- A triangular double sum read column-first instead of row-first: the entry
at `(i, j)` with `j <= i` is reindexed as `(j + h, j)` with `h = i - j`, so
the inner bound becomes the outer-index-dependent `n + 1 - j`. Proved by
induction on the outer index, adding one row at a time through
`finiteSum_triangle_extend`. -/
theorem finiteSum_triangle_swap (term : Nat -> Nat -> alpha) :
    forall n : Nat,
      finiteSum F
          (fun i : Nat =>
            finiteSum F (fun j : Nat => term i j) (i + 1))
          (n + 1) =
        finiteSum F
          (fun j : Nat =>
            finiteSum F (fun h : Nat => term (j + h) j)
              (n + 1 - j))
          (n + 1)
  | 0 => by
      have houter : 0 + 1 = 1 := by
        omega
      rw [houter]
      rw [finiteSum_one (F := F)
        (term := fun i : Nat =>
          finiteSum F (fun j : Nat => term i j) (i + 1))]
      rw [finiteSum_one (F := F)
        (term := fun j : Nat => term 0 j)]
      rw [finiteSum_one (F := F)
        (term := fun j : Nat =>
          finiteSum F (fun h : Nat => term (j + h) j) (1 - j))]
      have hlen : 1 - 0 = 1 := by
        omega
      rw [hlen]
      rw [finiteSum_one (F := F)
        (term := fun h : Nat => term (0 + h) 0)]
  | n + 1 => by
      rw [finiteSum_succ]
      rw [finiteSum_triangle_swap term n]
      rw [finiteSum_triangle_extend F term (n + 1)]

theorem finiteSum_neg (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F (fun k : Nat => F.neg (term k)) n =
        F.neg (finiteSum F term n)
  | 0 => by
      rw [finiteSum_zero, finiteSum_zero]
      exact Eq.symm (neg_zero F)
  | n + 1 => by
      rw [finiteSum_succ, finiteSum_succ]
      rw [finiteSum_neg term n]
      change F.add (F.neg (finiteSum F term n)) (F.neg (term n)) =
        F.neg (F.add (finiteSum F term n) (term n))
      exact Eq.symm
        (neg_add_distrib F (finiteSum F term n) (term n))

theorem finiteSum_sub (u v : Nat -> alpha) :
    forall n : Nat,
      finiteSum F (fun k : Nat => F.sub (u k) (v k)) n =
        F.sub (finiteSum F u n) (finiteSum F v n)
  | n => by
      calc
        finiteSum F (fun k : Nat => F.sub (u k) (v k)) n =
            finiteSum F
              (fun k : Nat => F.add (u k) (F.neg (v k))) n := by
              apply finiteSum_congr F
              intro k
              exact F.sub_eq_add_neg (u k) (v k)
        _ = F.add (finiteSum F u n)
              (finiteSum F (fun k : Nat => F.neg (v k)) n) := by
              rw [finiteSum_add]
        _ = F.add (finiteSum F u n)
              (F.neg (finiteSum F v n)) := by
              rw [finiteSum_neg]
        _ = F.sub (finiteSum F u n) (finiteSum F v n) := by
              exact Eq.symm
                (F.sub_eq_add_neg (finiteSum F u n) (finiteSum F v n))

theorem finiteSum_shift_zero (term : Nat -> alpha) :
    finiteSum F (fun j : Nat => term (0 + j)) 0 = F.zero :=
  rfl

theorem finiteSum_prepend (head : alpha) (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F
        (fun k : Nat =>
          match k with
          | 0 => head
          | j + 1 => term j)
        (n + 1) =
        F.add head (finiteSum F term n)
  | 0 => by
      rw [finiteSum_succ, finiteSum_zero, finiteSum_zero]
      rw [F.zero_add, F.add_zero]
  | n + 1 => by
      rw [finiteSum_succ
        (F := F)
        (term :=
          fun k : Nat =>
            match k with
            | 0 => head
            | j + 1 => term j)
        (n := n + 1)]
      rw [finiteSum_prepend head term n]
      rw [finiteSum_succ (F := F) (term := term) (n := n)]
      rw [F.add_assoc]

theorem finiteSum_prepend_zero (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F
        (fun k : Nat =>
          match k with
          | 0 => F.zero
          | j + 1 => term j)
        (n + 1) =
        finiteSum F term n
  | 0 => by
      rw [finiteSum_succ, finiteSum_zero, finiteSum_zero]
      rw [F.add_zero]
  | n + 1 => by
      rw [finiteSum_succ
        (F := F)
        (term :=
          fun k : Nat =>
            match k with
            | 0 => F.zero
            | j + 1 => term j)
        (n := n + 1)]
      rw [finiteSum_prepend_zero term n]
      rw [finiteSum_succ (F := F) (term := term) (n := n)]

theorem finiteSum_append_zero
    (term : Nat -> alpha) {n : Nat}
    (h : term n = F.zero) :
    finiteSum F term (n + 1) =
      finiteSum F term n := by
  rw [finiteSum_succ]
  rw [h]
  rw [F.add_zero]

theorem finiteSum_telescope_sub (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F
        (fun k : Nat => F.sub (term (k + 1)) (term k)) n =
        F.sub (term n) (term 0)
  | 0 => by
      rw [finiteSum_zero]
      exact Eq.symm (sub_self F (term 0))
  | n + 1 => by
      rw [finiteSum_succ]
      rw [finiteSum_telescope_sub term n]
      calc
        F.add (F.sub (term n) (term 0))
            (F.sub (term (n + 1)) (term n)) =
            F.add (F.sub (term (n + 1)) (term n))
              (F.sub (term n) (term 0)) := by
            rw [F.add_comm]
        _ = F.sub (term (n + 1)) (term 0) := by
            exact sub_add_sub_cancel F
              (term (n + 1)) (term n) (term 0)

/-- Splitting a sum of length `a + b` at `a`: the first block is the plain
`a`-prefix, the second is reindexed so that its `j`-th entry is the original
`(a + j)`-th. `finiteSum_split_first` below is the special case `a = 1` and is
proved from this one. -/
theorem finiteSum_add_length (term : Nat -> alpha) :
    forall a b : Nat,
      finiteSum F term (a + b) =
        F.add (finiteSum F term a)
          (finiteSum F (fun j : Nat => term (a + j)) b)
  | a, 0 => by
      rw [Nat.add_zero]
      rw [finiteSum_zero]
      rw [F.add_zero]
  | a, b + 1 => by
      rw [Nat.add_succ]
      rw [finiteSum_succ]
      rw [finiteSum_add_length term a b]
      rw [finiteSum_succ]
      change
        F.add
          (F.add (finiteSum F term a)
            (finiteSum F (fun j : Nat => term (a + j)) b))
          (term (a + b)) =
          F.add (finiteSum F term a)
            (F.add
              (finiteSum F (fun j : Nat => term (a + j)) b)
              (term (a + b)))
      rw [F.add_assoc]

theorem finiteSum_split_first (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F term (n + 1) =
        F.add (term 0)
          (finiteSum F (fun j : Nat => term (j + 1)) n)
  | n => by
      have hlen : n + 1 = 1 + n := by
        omega
      rw [hlen]
      rw [finiteSum_add_length (F := F) term 1 n]
      rw [finiteSum_one]
      congr 1
      apply finiteSum_congr F
      intro j
      have hidx : 1 + j = j + 1 := by
        omega
      rw [hidx]

theorem finiteSum_reverse (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F term (n + 1) =
        finiteSum F (fun i : Nat => term (n - i)) (n + 1)
  | 0 => by
      rw [finiteSum_one]
      rw [finiteSum_one]
  | n + 1 => by
      rw [finiteSum_succ]
      rw [finiteSum_reverse term n]
      rw [finiteSum_split_first F
        (fun i : Nat => term (n + 1 - i)) (n + 1)]
      rw [Nat.sub_zero]
      have htail :
          finiteSum F
              (fun j : Nat => term (n + 1 - (j + 1))) (n + 1) =
            finiteSum F (fun i : Nat => term (n - i)) (n + 1) := by
        apply finiteSum_congr_lt F
        intro i hi
        have hidx : n + 1 - (i + 1) = n - i := by
          omega
        rw [hidx]
      rw [htail]
      rw [F.add_comm]

theorem finiteSum_shift_succ (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F (fun j : Nat => term (j + 1)) (n + 1) =
        F.add (term 1)
          (finiteSum F (fun j : Nat => term ((j + 1) + 1)) n)
  | n => by
      have hlen : n + 1 = 1 + n := by
        omega
      rw [hlen]
      rw [finiteSum_add_length (F := F)
        (fun j : Nat => term (j + 1)) 1 n]
      rw [finiteSum_one]
      change
        F.add (term (0 + 1))
          (finiteSum F (fun j : Nat => term (1 + j + 1)) n) =
        F.add (term 1)
          (finiteSum F (fun j : Nat => term (j + 1 + 1)) n)
      have h01 : 0 + 1 = 1 := by
        omega
      rw [h01]
      congr 1
      apply finiteSum_congr F
      intro j
      have hidx : 1 + j + 1 = j + 1 + 1 := by
        omega
      rw [hidx]

/-- A sum of `p * q` terms regrouped into `p` consecutive blocks of width
`q`: the factorisation of the length read as a nesting. The width-`2` case,
regrouped further into adjacent pairs, is `finiteSum_pair_even_odd` below. -/
theorem finiteSum_blocks (term : Nat -> alpha) :
    forall p q : Nat,
      finiteSum F term (p * q) =
        finiteSum F
          (fun k : Nat =>
            finiteSum F (fun j : Nat => term (k * q + j)) q)
          p
  | 0, q => by
      rw [Nat.zero_mul]
      rw [finiteSum_zero, finiteSum_zero]
  | p + 1, q => by
      rw [Nat.succ_mul]
      rw [finiteSum_add_length (F := F) term (p * q) q]
      rw [finiteSum_succ]
      rw [finiteSum_blocks term p q]

/-- The even-odd pairing of `2 n` terms: each even index is grouped with its
odd successor inside a single summand. This is the regrouping step wherever
two consecutive terms have to be handled as a unit. -/
theorem finiteSum_pair_even_odd (term : Nat -> alpha) :
    forall n : Nat,
      finiteSum F term (2 * n) =
        finiteSum F
          (fun k : Nat => F.add (term (2 * k)) (term (2 * k + 1)))
          n := by
  intro n
  have hblocks := finiteSum_blocks F term n 2
  rw [Nat.mul_comm] at hblocks
  rw [hblocks]
  apply finiteSum_congr F
  intro k
  rw [finiteSum_succ, finiteSum_succ, finiteSum_zero]
  have hzero : k * 2 + 0 = 2 * k := by omega
  have hone : k * 2 + 1 = 2 * k + 1 := by omega
  rw [hzero, hone, F.zero_add]

end IsOrderedFieldBaseLike
end Tautology
