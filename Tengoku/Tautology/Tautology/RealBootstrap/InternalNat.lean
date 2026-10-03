import Tengoku.Tautology.Tautology.RealBootstrap.PositiveOne

/-!
# The natural numbers inside the field

Two descriptions of the same thing, and the theorem that reconciles them. A
field element is an *internal natural* when it lies in every inductive subset
of the field -- a definition internal to the field, using no external type --
and separately there is the embedding `nat` that sends a Lean `Nat` to a sum of
ones. `internalNat_of_nat` and `internalNat_exists_nat` show the image of the
embedding is exactly the internal naturals.

Keeping both is the point. The inductive description gives an induction
principle usable inside the field; the embedding gives concrete elements to
compute with. Arguments upstream use whichever is convenient and cross over by
these two theorems.

Note that `InternalNat` is a predicate on field elements, not a type. Nothing
here constructs a copy of `Nat` inside the field; it identifies which elements
deserve the name.

## Position and role

Implementation module over an arbitrary ordered field, the base of the internal
number systems (`Tautology.RealBootstrap.InternalInt`, `...InternalRat`) and of
the Archimedean statements. It needs positivity of one, hence its position
directly above `Tautology.RealBootstrap.PositiveOne`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The canonical image of an external natural number in the field, built by
recursion on the `Nat` argument: zero maps to zero, a successor adds one.
The predicate `InternalNat` below describes this same collection from inside
the field. -/
def nat : Nat -> alpha
  | 0 => F.zero
  | n + 1 => F.add (nat n) F.one

theorem nat_zero : nat F 0 = F.zero :=
  rfl

theorem nat_succ (n : Nat) :
    nat F (n + 1) = F.add (nat F n) F.one :=
  rfl

/-- A predicate on the field that contains zero and is closed under adding
one. These are the sets that the definition of `InternalNat` intersects
over. -/
def InductiveSet (S : alpha -> Prop) : Prop :=
  And (S F.zero)
    (forall x : alpha, S x -> S (F.add x F.one))

/-- The internal naturals: the field elements that belong to every inductive
set. This is the intersection definition rather than the image of the
embedding `nat`, and the two descriptions are reconciled below by
`internalNat_of_nat` and `internalNat_exists_nat`. It is a predicate on
field elements; the external type `Nat` meets it only through the
embedding. -/
def InternalNat (x : alpha) : Prop :=
  forall S : alpha -> Prop, InductiveSet F S -> S x

theorem internalNat_zero : InternalNat F F.zero := by
  intro S hS
  exact hS.left

theorem internalNat_succ {x : alpha}
    (hx : InternalNat F x) :
    InternalNat F (F.add x F.one) := by
  intro S hS
  exact hS.right x (hx S hS)

theorem internalNat_inductive :
    InductiveSet F (InternalNat F) :=
  And.intro
    (internalNat_zero F)
    (fun _ hx => internalNat_succ F hx)

theorem internalNat_minimal {S : alpha -> Prop}
    (hS : InductiveSet F S) {x : alpha}
    (hx : InternalNat F x) :
    S x :=
  hx S hS

/-- Induction over the internal naturals: a predicate holding at zero and
propagating along `x + 1` holds on all of `InternalNat`. The intersection
definition offers no case analysis on members, so this scheme, proved by
applying minimality to `InternalNat` conjoined with the predicate, is how
consumers reason about them. -/
theorem internalNat_induction {P : alpha -> Prop}
    (h0 : P F.zero)
    (hsucc : forall x : alpha, InternalNat F x -> P x ->
      P (F.add x F.one)) :
    forall x : alpha, InternalNat F x -> P x := by
  let Q : alpha -> Prop := fun x => And (InternalNat F x) (P x)
  have hQ : InductiveSet F Q := by
    constructor
    · exact And.intro (internalNat_zero F) h0
    · intro x hx
      exact And.intro
        (internalNat_succ F hx.left)
        (hsucc x hx.left hx.right)
  intro x hx
  exact (internalNat_minimal F hQ hx).right

/-- The embedding lands inside the predicate: the image of every external
natural is an internal natural, by induction on the `Nat` argument. This is
the external-to-internal half of the reconciliation between the two
descriptions; `internalNat_exists_nat` supplies the converse. -/
theorem internalNat_of_nat (n : Nat) :
    InternalNat F (nat F n) := by
  induction n with
  | zero =>
      exact internalNat_zero F
  | succ n ih =>
      rw [nat_succ]
      exact internalNat_succ F ih

/-- Every internal natural is the image of an external one, so the
intersection definition is exhausted by the embedding. Together with
`internalNat_of_nat` this identifies `InternalNat` with the image of
`nat`. -/
theorem internalNat_exists_nat {x : alpha}
    (hx : InternalNat F x) :
    Exists (fun n : Nat => x = nat F n) := by
  let S : alpha -> Prop := fun y => Exists (fun n : Nat => y = nat F n)
  have hS : InductiveSet F S := by
    constructor
    · exact Exists.intro 0 rfl
    · intro y hy
      cases hy with
      | intro n hn =>
          refine Exists.intro (n + 1) ?_
          rw [hn, nat_succ]
  exact hx S hS

theorem internalNat_one : InternalNat F F.one := by
  have h := internalNat_succ F (internalNat_zero F)
  rwa [F.zero_add] at h

theorem nat_one : nat F 1 = F.one := by
  rw [nat_succ, nat_zero, F.zero_add]

/-- The embedding preserves addition, by induction on the second argument.
With `nat_mul` it says `nat` respects the two semiring operations, so a sum
or product of embedded naturals can be computed on the `Nat` side and
carried across. -/
theorem nat_add (m n : Nat) :
    nat F (m + n) = F.add (nat F m) (nat F n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero, nat_zero, F.add_zero]
  | succ n ih =>
      rw [Nat.add_succ, nat_succ, ih, nat_succ, F.add_assoc]

/-- The embedding preserves multiplication, the companion of `nat_add`; the
successor step unfolds `m * (n + 1)` into a sum and closes by that lemma. -/
theorem nat_mul (m n : Nat) :
    nat F (m * n) = F.mul (nat F m) (nat F n) := by
  induction n with
  | zero =>
      rw [Nat.mul_zero, nat_zero, mul_zero F]
  | succ n ih =>
      rw [Nat.mul_succ, nat_add, ih, nat_succ, F.mul_add, F.mul_one]

/-- The internal naturals are closed under addition. The proof runs
`internalNat_induction` on the second argument rather than passing through
the embedding, which is the pattern that induction principle exists for. -/
theorem internalNat_add {x y : alpha}
    (hx : InternalNat F x) (hy : InternalNat F y) :
    InternalNat F (F.add x y) := by
  apply internalNat_induction F
    (P := fun y => InternalNat F (F.add x y))
  · rwa [F.add_zero]
  · intro y _ ih
    have h :
        F.add x (F.add y F.one) =
          F.add (F.add x y) F.one := by
      rw [<- F.add_assoc]
    rw [h]
    exact internalNat_succ F ih
  exact hy

/-- The internal naturals are closed under multiplication, again by internal
induction on the second argument; the successor step turns `x * (y + 1)`
into `x * y + x` and closes by `internalNat_add`. -/
theorem internalNat_mul {x y : alpha}
    (hx : InternalNat F x) (hy : InternalNat F y) :
    InternalNat F (F.mul x y) := by
  apply internalNat_induction F
    (P := fun y => InternalNat F (F.mul x y))
  · rw [mul_zero F]
    exact internalNat_zero F
  · intro y _ ih
    have h :
        F.mul x (F.add y F.one) =
          F.add (F.mul x y) x := by
      rw [F.mul_add, F.mul_one]
    rw [h]
    exact internalNat_add F ih hx
  exact hy

theorem nat_nonneg (n : Nat) : F.le F.zero (nat F n) := by
  induction n with
  | zero =>
      rw [nat_zero]
      exact F.le_refl F.zero
  | succ n ih =>
      have hstep :
          F.le (nat F n) (nat F (n + 1)) := by
        have h := F.add_le_add_right (zero_le_one F) (nat F n)
        rwa [F.zero_add, F.add_comm F.one (nat F n), <- nat_succ] at h
      exact F.le_trans ih hstep

theorem nat_le_nat_succ (n : Nat) :
    F.le (nat F n) (nat F (n + 1)) := by
  have h := F.add_le_add_right (zero_le_one F) (nat F n)
  rwa [F.zero_add, F.add_comm F.one (nat F n), <- nat_succ] at h

theorem nat_lt_nat_succ (n : Nat) :
    F.lt (nat F n) (nat F (n + 1)) := by
  have h := add_lt_add_left F (zero_lt_one F) (nat F n)
  rwa [F.add_zero, <- nat_succ] at h

/-- The embedding preserves non-strict order. Together with
`le_of_nat_le_nat`, which reflects it, this makes `nat` an order embedding,
so order questions about embedded naturals can be settled on the `Nat`
side. -/
theorem nat_le_nat_of_le {m n : Nat}
    (hmn : m <= n) :
    F.le (nat F m) (nat F n) := by
  induction n with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      exact F.le_refl (nat F 0)
  | succ n ih =>
      by_cases hmn' : m <= n
      · exact F.le_trans (ih hmn') (nat_le_nat_succ F n)
      · have hm : m = n + 1 := by omega
        subst hm
        exact F.le_refl (nat F (n + 1))

theorem nat_lt_nat_of_lt {m n : Nat}
    (hmn : m < n) :
    F.lt (nat F m) (nat F n) := by
  have hsucc : m + 1 <= n := by omega
  exact lt_of_lt_of_le F
    (nat_lt_nat_succ F m)
    (nat_le_nat_of_le F hsucc)

/-- The embedding reflects non-strict order: if the images are related then
the naturals already were. This is the half that keeps the embedding from
collapsing separated naturals into one field element. -/
theorem le_of_nat_le_nat {m n : Nat}
    (hmn : F.le (nat F m) (nat F n)) :
    m <= n := by
  by_cases hle : m <= n
  · exact hle
  · have hlt : n < m := by omega
    exact False.elim
      ((not_le_of_lt F (nat_lt_nat_of_lt F hlt)) hmn)

theorem nat_succ_pos (n : Nat) :
    F.lt F.zero (nat F (n + 1)) := by
  have hstep :
      F.lt (nat F n) (nat F (n + 1)) := by
    exact nat_lt_nat_succ F n
  exact lt_of_le_of_lt F (nat_nonneg F n) hstep

theorem nat_ne_zero_of_ne_zero {n : Nat}
    (hn : Not (n = 0)) :
    Not (nat F n = F.zero) := by
  cases n with
  | zero =>
      exact False.elim (hn rfl)
  | succ n =>
      intro h
      exact ne_of_lt F (nat_succ_pos F n) h.symm

theorem nat_pos_of_ne_zero {n : Nat}
    (hn : Not (n = 0)) :
    F.lt F.zero (nat F n) := by
  cases n with
  | zero =>
      exact False.elim (hn rfl)
  | succ n =>
      exact nat_succ_pos F n

end IsOrderedFieldBaseLike
end Tautology
