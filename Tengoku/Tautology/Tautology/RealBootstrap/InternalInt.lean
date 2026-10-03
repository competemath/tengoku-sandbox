import Tengoku.Tautology.Tautology.RealBootstrap.InternalNat
import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra

/-!
# The integers inside the field

The same pattern as `Tautology.RealBootstrap.InternalNat` one level up: an
embedding of Lean's `Int` built by cases on sign, the predicate `InternalInt`
saying an element is an internal natural or the negation of one, and
the theorem that the predicate is exactly the image of the embedding.

The arithmetic facts here are the ones the floor construction needs: internal
integers are closed under negation, addition and subtraction, and no internal
integer lies strictly between zero and one. That last one is what makes an
integer part unique.

## Position and role

Implementation module over an arbitrary ordered field.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The canonical image of an external integer, extending `nat` along the two
constructors of `Int`: a natural maps to its image, a negative successor to
the negation of a successor's image. The predicate `InternalInt` below
describes the same collection as differences of internal naturals. -/
def int : Int -> alpha
  | Int.ofNat n => nat F n
  | Int.negSucc n => F.neg (nat F (n + 1))

theorem int_ofNat (n : Nat) :
    int F (Int.ofNat n) = nat F n :=
  rfl

theorem int_negSucc (n : Nat) :
    int F (Int.negSucc n) = F.neg (nat F (n + 1)) :=
  rfl

theorem int_neg_ofNat (n : Nat) :
    int F (-(Int.ofNat n)) = F.neg (nat F n) := by
  cases n with
  | zero =>
      unfold nat
      simp [int]
      exact (neg_zero F).symm
  | succ n =>
      rw [show -(Int.ofNat (n + 1)) = Int.negSucc n by
        rw [Int.negSucc_eq]
        rfl]
      rfl

theorem int_neg (z : Int) :
    int F (-z) = F.neg (int F z) := by
  cases z with
  | ofNat n =>
      exact int_neg_ofNat F n
  | negSucc n =>
      rw [show -(Int.negSucc n) = Int.ofNat (n + 1) by
        simp [Int.negSucc_eq]]
      change nat F (n + 1) = F.neg (F.neg (nat F (n + 1)))
      exact Eq.symm (neg_neg F (nat F (n + 1)))

theorem int_negOfNat (n : Nat) :
    int F (Int.negOfNat n) = F.neg (nat F n) := by
  rw [Int.negOfNat_eq]
  exact int_neg_ofNat F n

theorem int_mul_ofNat (z : Int) (n : Nat) :
    int F (z * Int.ofNat n) =
      F.mul (int F z) (nat F n) := by
  cases z with
  | ofNat m =>
      change int F (Int.ofNat (m * n)) =
        F.mul (nat F m) (nat F n)
      rw [int_ofNat]
      exact nat_mul F m n
  | negSucc m =>
      change int F (Int.negOfNat ((m + 1) * n)) =
        F.mul (F.neg (nat F (m + 1))) (nat F n)
      rw [int_negOfNat]
      rw [nat_mul]
      exact Eq.symm (neg_mul F (nat F (m + 1)) (nat F n))

theorem int_subNatNat (m n : Nat) :
    int F (Int.subNatNat m n) =
      F.sub (nat F m) (nat F n) := by
  exact Int.subNatNat_elim m n
    (fun m n z =>
      int F z = F.sub (nat F m) (nat F n))
    (by
      intro i n
      change nat F i = F.sub (nat F (n + i)) (nat F n)
      rw [nat_add]
      rw [F.add_comm (nat F n) (nat F i)]
      exact Eq.symm (add_sub_cancel F (nat F i) (nat F n)))
    (by
      intro i m
      rw [int_negSucc]
      have hindex : m + i + 1 = m + (i + 1) := by omega
      rw [hindex]
      change F.neg (nat F (i + 1)) =
        F.sub (nat F m) (nat F (m + (i + 1)))
      rw [show nat F (m + (i + 1)) =
          F.add (nat F m) (nat F (i + 1)) from
        nat_add F m (i + 1)]
      rw [F.sub_eq_add_neg]
      rw [neg_add_distrib F (nat F m) (nat F (i + 1))]
      symm
      calc
        F.add (nat F m)
            (F.add (F.neg (nat F m)) (F.neg (nat F (i + 1)))) =
            F.add (F.add (nat F m) (F.neg (nat F m)))
              (F.neg (nat F (i + 1))) := by
              rw [<- F.add_assoc]
        _ = F.add F.zero (F.neg (nat F (i + 1))) := by
              rw [F.add_neg]
        _ = F.neg (nat F (i + 1)) := by
              rw [F.zero_add])

theorem int_add (z w : Int) :
    int F (z + w) = F.add (int F z) (int F w) := by
  cases z with
  | ofNat m =>
      cases w with
      | ofNat n =>
          change int F (Int.ofNat (m + n)) =
            F.add (nat F m) (nat F n)
          rw [int_ofNat]
          exact nat_add F m n
      | negSucc n =>
          change int F (Int.subNatNat m (n + 1)) =
            F.add (nat F m) (F.neg (nat F (n + 1)))
          rw [int_subNatNat, F.sub_eq_add_neg]
  | negSucc m =>
      cases w with
      | ofNat n =>
          change int F (Int.subNatNat n (m + 1)) =
            F.add (F.neg (nat F (m + 1))) (nat F n)
          rw [int_subNatNat, F.sub_eq_add_neg]
          exact F.add_comm (nat F n) (F.neg (nat F (m + 1)))
      | negSucc n =>
          change int F (Int.negSucc (m + n + 1)) =
            F.add (F.neg (nat F (m + 1)))
              (F.neg (nat F (n + 1)))
          rw [int_negSucc]
          have hindex : m + n + 1 + 1 = (m + 1) + (n + 1) := by omega
          rw [hindex]
          rw [nat_add]
          exact neg_add_distrib F (nat F (m + 1)) (nat F (n + 1))

/-- The internal integers: the differences `a - b` of two internal
naturals. The closure description is the definition, not the image of the
embedding `int`; `internalInt_of_int` and `internalInt_exists_int` below
reconcile the two. -/
def InternalInt (x : alpha) : Prop :=
  Exists
    (fun a : alpha =>
      Exists
        (fun b : alpha =>
          And (InternalNat F a)
            (And (InternalNat F b) (x = F.sub a b))))

theorem internalInt_of_internalNat {x : alpha}
    (hx : InternalNat F x) :
    InternalInt F x := by
  refine Exists.intro x ?_
  refine Exists.intro F.zero ?_
  exact And.intro hx
    (And.intro (internalNat_zero F) (by
      rw [F.sub_eq_add_neg, neg_zero F, F.add_zero]))

theorem internalInt_zero : InternalInt F F.zero :=
  internalInt_of_internalNat F (internalNat_zero F)

theorem internalInt_one : InternalInt F F.one :=
  internalInt_of_internalNat F (internalNat_one F)

theorem internalInt_neg_nat (n : Nat) :
    InternalInt F (F.neg (nat F n)) := by
  refine Exists.intro F.zero ?_
  refine Exists.intro (nat F n) ?_
  exact And.intro (internalNat_zero F)
    (And.intro (internalNat_of_nat F n) (by
      rw [F.sub_eq_add_neg, F.zero_add]))

/-- The embedding lands inside the predicate: every `int F z` is a
difference of internal naturals, by cases on the two constructors of `Int`.
This is the external-to-internal half of the reconciliation;
`internalInt_exists_int` supplies the converse. -/
theorem internalInt_of_int (z : Int) :
    InternalInt F (int F z) := by
  cases z with
  | ofNat n =>
      exact internalInt_of_internalNat F (internalNat_of_nat F n)
  | negSucc n =>
      exact internalInt_neg_nat F (n + 1)

/-- Every internal integer is the image of an external `Int`, so the
difference definition is exhausted by the embedding. With
`internalInt_of_int` the two descriptions of the internal integers
coincide. -/
theorem internalInt_exists_int {x : alpha}
    (hx : InternalInt F x) :
    Exists (fun z : Int => x = int F z) := by
  cases hx with
  | intro a ha =>
      cases ha with
      | intro b hb =>
          cases internalNat_exists_nat F hb.left with
          | intro m hm =>
              cases internalNat_exists_nat F hb.right.left with
              | intro n hn =>
                  refine Exists.intro (Int.subNatNat m n) ?_
                  rw [hb.right.right, hm, hn]
                  exact Eq.symm (int_subNatNat F m n)

/-- No internal integer lies strictly between zero and one. This one-unit gap
is the discreteness fact that identifies two internal integers sharing the
same floor bounds in `Tautology.RealBootstrap.IntegerPart`. -/
theorem not_internalInt_of_zero_lt_of_lt_one {x : alpha}
    (hx0 : F.lt F.zero x) (hx1 : F.lt x F.one) :
    Not (InternalInt F x) := by
  intro hx
  cases internalInt_exists_int F hx with
  | intro z hz =>
      cases z with
      | ofNat n =>
          cases n with
          | zero =>
              rw [int_ofNat, nat_zero] at hz
              rw [hz] at hx0
              exact (lt_irrefl F F.zero) hx0
          | succ n =>
              rw [int_ofNat] at hz
              have hOneNat : F.le F.one (nat F (n + 1)) := by
                rw [<- nat_one F]
                exact nat_le_nat_of_le F (Nat.succ_le_succ (Nat.zero_le n))
              have hOneX : F.le F.one x := by
                rw [hz]
                exact hOneNat
              exact (not_le_of_lt F hx1) hOneX
      | negSucc n =>
          rw [int_negSucc] at hz
          have hNegNonpos :
              F.le (F.neg (nat F (n + 1))) F.zero := by
            have h := neg_le_neg F (nat_nonneg F (n + 1))
            rwa [neg_zero F] at h
          have hXNonpos : F.le x F.zero := by
            rw [hz]
            exact hNegNonpos
          exact (not_le_of_lt F hx0) hXNonpos

theorem internalInt_neg {x : alpha}
    (hx : InternalInt F x) :
    InternalInt F (F.neg x) := by
  cases hx with
  | intro a ha =>
      cases ha with
      | intro b hb =>
          refine Exists.intro b ?_
          refine Exists.intro a ?_
          exact And.intro hb.right.left
            (And.intro hb.left (by
              rw [hb.right.right, sub_rev_eq_neg_sub F a b]))

theorem internalInt_add {x y : alpha}
    (hx : InternalInt F x) (hy : InternalInt F y) :
    InternalInt F (F.add x y) := by
  cases hx with
  | intro a ha =>
      cases ha with
      | intro b hb =>
          cases hy with
          | intro c hc =>
              cases hc with
              | intro d hd =>
                  refine Exists.intro (F.add a c) ?_
                  refine Exists.intro (F.add b d) ?_
                  exact And.intro
                    (internalNat_add F hb.left hd.left)
                    (And.intro
                      (internalNat_add F hb.right.left hd.right.left)
                      (by
                        rw [hb.right.right, hd.right.right]
                        exact Eq.symm
                          (add_sub_add_eq_sub_add_sub F a c b d)))

theorem internalInt_sub {x y : alpha}
    (hx : InternalInt F x) (hy : InternalInt F y) :
    InternalInt F (F.sub x y) := by
  rw [F.sub_eq_add_neg]
  exact internalInt_add F hx (internalInt_neg F hy)

end IsOrderedFieldBaseLike
end Tautology
