import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra.AbsCore

/-!
# Order-compatible arithmetic

The file most of the library actually stands on, and the second largest of the
region by declaration count: subtraction and inequalities in every
combination, multiplication by factors of known sign, inverses and their order
reversal, halving, midpoints, and a handful of named algebraic identities.

Two groups deserve to be found rather than rediscovered. The midpoint block --
`midpoint` with its four position lemmas -- is what every bisection argument in
the library uses, from the completeness route graph to the Cantor set. And the
identities at the end (`add_square`, `sub_square`, the Brahmagupta-Fibonacci
identity, the difference-of-squares factorisation) exist because specific
proofs upstream needed exactly them; they are not a systematic development of
polynomial algebra.

## Position and role

Implementation module over an arbitrary ordered field, built on
`Tautology.RealBootstrap.OrderAlgebra.AbsCore`. It is the direct base of the
absolute value, the lattice operations, finite sums and the internal naturals.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem lt_add_of_pos {x eps : alpha}
    (heps : F.lt F.zero eps) :
    F.lt x (F.add x eps) := by
  have h := add_lt_add_left F heps x
  rwa [F.add_zero] at h

theorem le_add_one (x : alpha) :
    F.le x (F.add x F.one) := by
  have h01 : F.le F.zero F.one :=
    le_of_lt F F.zero_lt_one
  have h := add_le_add_left F h01 x
  rwa [F.add_zero] at h

theorem one_le_add_one_of_nonneg {x : alpha}
    (hx : F.le F.zero x) :
    F.le F.one (F.add x F.one) := by
  have h := F.add_le_add_right hx F.one
  rwa [F.zero_add] at h

theorem mul_mul_mul_comm (a b c d : alpha) :
    F.mul (F.mul a b) (F.mul c d) =
      F.mul (F.mul a c) (F.mul b d) := by
  calc
    F.mul (F.mul a b) (F.mul c d) =
        F.mul a (F.mul b (F.mul c d)) := by
          rw [F.mul_assoc]
    _ = F.mul a (F.mul (F.mul b c) d) := by
          rw [<- F.mul_assoc b c d]
    _ = F.mul a (F.mul (F.mul c b) d) := by
          rw [F.mul_comm b c]
    _ = F.mul a (F.mul c (F.mul b d)) := by
          rw [F.mul_assoc c b d]
    _ = F.mul (F.mul a c) (F.mul b d) := by
          rw [<- F.mul_assoc a c (F.mul b d)]

theorem sub_zero (x : alpha) : F.sub x F.zero = x := by
  rw [F.sub_eq_add_neg, neg_zero F, F.add_zero]

theorem zero_sub (x : alpha) : F.sub F.zero x = F.neg x := by
  rw [F.sub_eq_add_neg, F.zero_add]

theorem le_sub_of_add_le {x y z : alpha}
    (h : F.le (F.add x z) y) :
    F.le x (F.sub y z) := by
  apply le_of_add_le_add_right F
  change F.le (F.add x z) (F.add (F.sub y z) z)
  rwa [sub_add_cancel F y z]

theorem sub_right_le_sub_left_of_le_sub {x y z : alpha}
    (h : F.le x (F.sub y z)) :
    F.le z (F.sub y x) := by
  have hsum : F.le (F.add x z) y := by
    have h' := F.add_le_add_right h z
    change F.le (F.add x z) (F.add (F.sub y z) z) at h'
    rwa [sub_add_cancel F y z] at h'
  have hsum_comm : F.le (F.add z x) y := by
    rwa [F.add_comm z x]
  exact le_sub_of_add_le F hsum_comm

theorem add_le_add_of_sub_le_sub {u v x y : alpha}
    (h : F.le (F.sub x y) (F.sub v u)) :
    F.le (F.add u x) (F.add v y) := by
  have h' := F.add_le_add_right h (F.add u y)
  change
    F.le
      (F.add (F.sub x y) (F.add u y))
      (F.add (F.sub v u) (F.add u y)) at h'
  have hleft :
      F.add (F.sub x y) (F.add u y) = F.add u x := by
    calc
      F.add (F.sub x y) (F.add u y) =
          F.add (F.sub x y) (F.add y u) := by
            rw [F.add_comm u y]
      _ = F.add (F.add (F.sub x y) y) u := by
            rw [<- F.add_assoc]
      _ = F.add x u := by rw [sub_add_cancel F x y]
      _ = F.add u x := by rw [F.add_comm x u]
  have hright :
      F.add (F.sub v u) (F.add u y) = F.add v y := by
    calc
      F.add (F.sub v u) (F.add u y) =
          F.add (F.add (F.sub v u) u) y := by
            rw [<- F.add_assoc]
      _ = F.add v y := by rw [sub_add_cancel F v u]
  rwa [hleft, hright] at h'

theorem sub_self_sub (x y : alpha) :
    F.sub x (F.sub x y) = y := by
  apply add_right_cancel F (a := F.sub x y)
  calc
    F.add (F.sub x (F.sub x y)) (F.sub x y) =
        x := sub_add_cancel F x (F.sub x y)
    _ = F.add y (F.sub x y) := by
        rw [F.add_comm y (F.sub x y), sub_add_cancel F x y]

theorem sub_add_sub_cancel (x y z : alpha) :
    F.add (F.sub x y) (F.sub y z) = F.sub x z := by
  rw [F.sub_eq_add_neg]
  rw [F.sub_eq_add_neg]
  rw [F.sub_eq_add_neg]
  calc
    F.add (F.add x (F.neg y)) (F.add y (F.neg z)) =
        F.add x (F.add (F.neg y) (F.add y (F.neg z))) := by
          rw [F.add_assoc]
    _ = F.add x (F.add (F.add (F.neg y) y) (F.neg z)) := by
          rw [<- F.add_assoc (F.neg y) y (F.neg z)]
    _ = F.add x (F.add F.zero (F.neg z)) := by rw [F.neg_add]
    _ = F.add x (F.neg z) := by rw [F.zero_add]

theorem add_sub_right_reassociate (A t b : alpha) :
    F.sub (F.add A t) b = F.add (F.sub A b) t := by
  rw [F.sub_eq_add_neg, F.sub_eq_add_neg]
  calc
    F.add (F.add A t) (F.neg b) =
        F.add A (F.add t (F.neg b)) := F.add_assoc A t (F.neg b)
    _ = F.add A (F.add (F.neg b) t) := by
          rw [F.add_comm t (F.neg b)]
    _ = F.add (F.add A (F.neg b)) t :=
          (F.add_assoc A (F.neg b) t).symm

theorem sub_sub_eq_sub_add (x y z : alpha) :
    F.sub (F.sub x y) z = F.sub x (F.add y z) := by
  rw [F.sub_eq_add_neg]
  rw [F.sub_eq_add_neg]
  rw [F.sub_eq_add_neg]
  rw [neg_add_distrib F y z]
  calc
    F.add (F.add x (F.neg y)) (F.neg z) =
        F.add x (F.add (F.neg y) (F.neg z)) := by
          rw [F.add_assoc]

theorem sub_le_self_of_nonneg_basic {x y : alpha}
    (hy : F.le F.zero y) :
    F.le (F.sub x y) x := by
  have hneg : F.le (F.neg y) F.zero := by
    have h := F.add_le_add_right hy (F.neg y)
    rwa [F.add_neg, F.zero_add] at h
  have h := add_le_add_left F hneg x
  rwa [<- F.sub_eq_add_neg x y, F.add_zero] at h

theorem eq_of_sub_eq_zero {x y : alpha}
    (h : F.sub x y = F.zero) :
    x = y := by
  have h' := congrArg (fun t => F.add t y) h
  change F.add (F.sub x y) y = F.add F.zero y at h'
  rw [sub_add_cancel F x y, F.zero_add] at h'
  exact h'

theorem sub_lt_self_of_pos {x eps : alpha}
    (heps : F.lt F.zero eps) :
    F.lt (F.sub x eps) x := by
  have hneg : F.lt (F.neg eps) F.zero := by
    have h := add_lt_add_right F heps (F.neg eps)
    rwa [F.zero_add, F.add_neg] at h
  have h := add_lt_add_left F hneg x
  rwa [<- F.sub_eq_add_neg x eps, F.add_zero] at h

theorem sub_pos_of_lt {x y : alpha}
    (hxy : F.lt x y) :
    F.lt F.zero (F.sub y x) := by
  have h := add_lt_add_right F hxy (F.neg x)
  rwa [F.add_neg, <- F.sub_eq_add_neg y x] at h

/-- The all-tolerances criterion for a weak inequality: x <= y follows once
x < y + eps for every positive eps. The integral theory above -- Riemann,
Darboux and Henstock--Kurzweil -- closes its strict estimates this way; the
proof feeds the gap x - y back in as the eps that would contradict
irreflexivity. -/
theorem le_of_forall_lt_add_pos {x y : alpha}
    (h : forall eps : alpha,
      F.lt F.zero eps -> F.lt x (F.add y eps)) :
    F.le x y := by
  by_cases hxy : F.le x y
  case pos => exact hxy
  case neg =>
    have hyx : F.le y x := by
      cases F.le_total y x with
      | inl hle => exact hle
      | inr hle => exact False.elim (hxy hle)
    have hy_lt_x : F.lt y x :=
      lt_of_le_of_not_le F hyx hxy
    let gap := F.sub x y
    have hgap_pos : F.lt F.zero gap := by
      dsimp [gap]
      exact sub_pos_of_lt F hy_lt_x
    have hx_lt : F.lt x (F.add y gap) := h gap hgap_pos
    have hy_gap : F.add y gap = x := by
      dsimp [gap]
      rw [F.add_comm y (F.sub x y)]
      exact sub_add_cancel F x y
    rw [hy_gap] at hx_lt
    exact False.elim (lt_irrefl F x hx_lt)

theorem lt_of_sub_pos {x y : alpha}
    (h : F.lt F.zero (F.sub y x)) :
    F.lt x y := by
  have h' := add_lt_add_right F h x
  rwa [F.zero_add, sub_add_cancel F y x] at h'

theorem sub_lt_of_lt_add {x a eps : alpha}
    (h : F.lt x (F.add a eps)) :
    F.lt (F.sub x a) eps := by
  have h' := add_lt_add_right F h (F.neg a)
  have hright :
      F.add (F.add a eps) (F.neg a) = eps := by
    calc
      F.add (F.add a eps) (F.neg a) =
          F.add (F.add eps a) (F.neg a) := by
            rw [F.add_comm a eps]
      _ = eps := add_neg_cancel_right F eps a
  rwa [<- F.sub_eq_add_neg x a, hright] at h'

theorem sub_lt_of_lt_right {a x eps : alpha}
    (h : F.lt (F.sub a x) eps) :
    F.lt (F.sub a eps) x := by
  have hax : F.lt a (F.add eps x) := by
    have h' := add_lt_add_right F h x
    rwa [sub_add_cancel F a x] at h'
  have h' := add_lt_add_right F hax (F.neg eps)
  have hrhs :
      F.add (F.add eps x) (F.neg eps) = x := by
    calc
      F.add (F.add eps x) (F.neg eps) =
          F.add (F.add x eps) (F.neg eps) := by
            rw [F.add_comm eps x]
      _ = x := add_neg_cancel_right F x eps
  rwa [<- F.sub_eq_add_neg a eps, hrhs] at h'

theorem lt_sub_of_add_lt {a eps x : alpha}
    (h : F.lt (F.add a eps) x) :
    F.lt eps (F.sub x a) := by
  have h' := add_lt_add_right F h (F.neg a)
  have hleft :
      F.add (F.add a eps) (F.neg a) = eps := by
    calc
      F.add (F.add a eps) (F.neg a) =
          F.add (F.add eps a) (F.neg a) := by
            rw [F.add_comm a eps]
      _ = eps := add_neg_cancel_right F eps a
  rwa [hleft, <- F.sub_eq_add_neg x a] at h'

theorem sub_lt_of_sub_lt_left {a x eps : alpha}
    (h : F.lt (F.sub a eps) x) :
    F.lt (F.sub a x) eps := by
  have hax : F.lt a (F.add x eps) := by
    have h' := add_lt_add_right F h eps
    have hleft : F.add (F.sub a eps) eps = a :=
      sub_add_cancel F a eps
    have hright : F.add x eps = F.add x eps := rfl
    rwa [hleft, hright] at h'
  exact sub_lt_of_lt_add F hax

theorem sub_nonpos_of_le {x y : alpha}
    (hyx : F.le y x) :
    F.le (F.sub y x) F.zero := by
  have h := F.add_le_add_right hyx (F.neg x)
  rwa [F.add_neg, <- F.sub_eq_add_neg y x] at h

theorem le_of_sub_nonpos {x y : alpha}
    (h : F.le (F.sub y x) F.zero) :
    F.le y x := by
  have h' := F.add_le_add_right h x
  rwa [F.zero_add, sub_add_cancel F y x] at h'

theorem le_of_neg_le_neg {x y : alpha}
    (h : F.le (F.neg y) (F.neg x)) :
    F.le x y := by
  have h' := neg_le_neg F h
  rwa [neg_neg F x, neg_neg F y] at h'

theorem neg_lt_neg {x y : alpha}
    (hxy : F.lt x y) :
    F.lt (F.neg y) (F.neg x) := by
  apply lt_of_le_of_not_le F
  · exact neg_le_neg F (le_of_lt F hxy)
  · intro hle
    exact (not_le_of_lt F hxy) (le_of_neg_le_neg F hle)

theorem sub_lt_sub_left_of_lt {a b c : alpha}
    (hab : F.lt a b) :
    F.lt (F.sub c b) (F.sub c a) := by
  have hneg : F.lt (F.neg b) (F.neg a) :=
    neg_lt_neg F hab
  have h := add_lt_add_left F hneg c
  rwa [<- F.sub_eq_add_neg c b,
    <- F.sub_eq_add_neg c a] at h

theorem mul_sub_eq_mul_sub (x y z : alpha) :
    F.mul x (F.sub y z) =
      F.sub (F.mul x y) (F.mul x z) := by
  rw [F.sub_eq_add_neg, F.mul_add, mul_neg F, F.sub_eq_add_neg]

theorem sub_mul_eq_sub_mul (x y z : alpha) :
    F.mul (F.sub x y) z =
      F.sub (F.mul x z) (F.mul y z) := by
  rw [F.sub_eq_add_neg, F.add_mul, neg_mul F, F.sub_eq_add_neg]

theorem sub_one_mul_inv_eq_one_sub_inv
    {x : alpha} (hx : Not (x = F.zero)) :
    F.mul (F.sub x F.one) (F.inv x) =
      F.sub F.one (F.inv x) := by
  rw [sub_mul_eq_sub_mul F, F.mul_inv_cancel hx, F.one_mul]

theorem mul_sub_mul_eq_sub_mul_add_mul_sub (x y a b : alpha) :
    F.sub (F.mul x y) (F.mul a b) =
      F.add (F.mul (F.sub x a) y) (F.mul a (F.sub y b)) := by
  symm
  calc
    F.add (F.mul (F.sub x a) y) (F.mul a (F.sub y b)) =
        F.add
          (F.sub (F.mul x y) (F.mul a y))
          (F.sub (F.mul a y) (F.mul a b)) := by
            rw [sub_mul_eq_sub_mul F x a y]
            rw [mul_sub_eq_mul_sub F a y b]
    _ = F.sub (F.mul x y) (F.mul a b) :=
        sub_add_sub_cancel F (F.mul x y) (F.mul a y) (F.mul a b)

theorem mul_le_mul_nonneg_right {x y z : alpha}
    (hxy : F.le x y) (hz : F.le F.zero z) :
    F.le (F.mul x z) (F.mul y z) := by
  have hdiff : F.le F.zero (F.sub y x) :=
    sub_nonneg_of_le F hxy
  have hprod : F.le F.zero (F.mul (F.sub y x) z) :=
    F.mul_nonneg hdiff hz
  apply le_of_sub_nonneg F
  rwa [<- sub_mul_eq_sub_mul F y x z]

theorem mul_le_mul_nonneg_left {x y z : alpha}
    (hxy : F.le x y) (hz : F.le F.zero z) :
    F.le (F.mul z x) (F.mul z y) := by
  rw [F.mul_comm z x, F.mul_comm z y]
  exact mul_le_mul_nonneg_right F hxy hz

theorem mul_self_nonneg (x : alpha) :
    F.le F.zero (F.mul x x) := by
  cases F.le_total F.zero x with
  | inl hx =>
      exact F.mul_nonneg hx hx
  | inr hx =>
      have hneg : F.le F.zero (F.neg x) := by
        have h := neg_le_neg F hx
        change F.le (F.neg F.zero) (F.neg x) at h
        rwa [neg_zero F] at h
      have hprod : F.le F.zero (F.mul (F.neg x) (F.neg x)) :=
        F.mul_nonneg hneg hneg
      rwa [F.neg_mul_neg] at hprod

theorem mul_nonpos_of_nonpos_of_nonneg
    {x y : alpha}
    (hx : F.le x F.zero)
    (hy : F.le F.zero y) :
    F.le (F.mul x y) F.zero := by
  have hnegx : F.le F.zero (F.neg x) := by
    have h := neg_le_neg F hx
    change F.le (F.neg F.zero) (F.neg x) at h
    rwa [neg_zero F] at h
  have hprod : F.le F.zero (F.mul (F.neg x) y) :=
    F.mul_nonneg hnegx hy
  have hneg := neg_le_neg F hprod
  change F.le (F.neg (F.mul (F.neg x) y)) (F.neg F.zero) at hneg
  rw [neg_zero F] at hneg
  rwa [neg_mul F x y, neg_neg F (F.mul x y)] at hneg

theorem mul_nonneg_of_nonpos_of_nonpos
    {x y : alpha}
    (hx : F.le x F.zero)
    (hy : F.le y F.zero) :
    F.le F.zero (F.mul x y) := by
  have hnegx : F.le F.zero (F.neg x) := by
    have h := neg_le_neg F hx
    change F.le (F.neg F.zero) (F.neg x) at h
    rwa [neg_zero F] at h
  have hnegy : F.le F.zero (F.neg y) := by
    have h := neg_le_neg F hy
    change F.le (F.neg F.zero) (F.neg y) at h
    rwa [neg_zero F] at h
  have hprod : F.le F.zero (F.mul (F.neg x) (F.neg y)) :=
    F.mul_nonneg hnegx hnegy
  rwa [F.neg_mul_neg] at hprod

theorem mul_le_mul_nonpos_right
    {x y z : alpha}
    (hxy : F.le x y)
    (hz : F.le z F.zero) :
    F.le (F.mul y z) (F.mul x z) := by
  have hnegz : F.le F.zero (F.neg z) := by
    have h := neg_le_neg F hz
    change F.le (F.neg F.zero) (F.neg z) at h
    rwa [neg_zero F] at h
  have hmul := mul_le_mul_nonneg_right F hxy hnegz
  change F.le (F.mul x (F.neg z)) (F.mul y (F.neg z)) at hmul
  rw [F.mul_neg, F.mul_neg] at hmul
  exact le_of_neg_le_neg F hmul

theorem mul_le_mul_nonpos_left
    {x y z : alpha}
    (hxy : F.le x y)
    (hz : F.le z F.zero) :
    F.le (F.mul z y) (F.mul z x) := by
  rw [F.mul_comm z y, F.mul_comm z x]
  exact mul_le_mul_nonpos_right F hxy hz

theorem mul_lt_mul_pos_right {x y z : alpha}
    (hxy : F.lt x y) (hz : F.lt F.zero z) :
    F.lt (F.mul x z) (F.mul y z) := by
  have hdiff : F.lt F.zero (F.sub y x) :=
    sub_pos_of_lt F hxy
  have hprod : F.lt F.zero (F.mul (F.sub y x) z) :=
    mul_pos F hdiff hz
  apply lt_of_sub_pos F
  rwa [<- sub_mul_eq_sub_mul F y x z]

theorem mul_lt_mul_pos_left {x y z : alpha}
    (hxy : F.lt x y) (hz : F.lt F.zero z) :
    F.lt (F.mul z x) (F.mul z y) := by
  rw [F.mul_comm z x, F.mul_comm z y]
  exact mul_lt_mul_pos_right F hxy hz

theorem lt_of_mul_lt_mul_pos_right {x y z : alpha}
    (h : F.lt (F.mul x z) (F.mul y z))
    (hz : F.lt F.zero z) :
    F.lt x y := by
  have hnot : Not (F.le y x) := by
    intro hyx
    have hmul : F.le (F.mul y z) (F.mul x z) :=
      mul_le_mul_nonneg_right F hyx (le_of_lt F hz)
    exact (not_le_of_lt F h) hmul
  cases F.le_total x y with
  | inl hxy =>
      exact lt_of_le_of_not_le F hxy hnot
  | inr hyx =>
      exact False.elim (hnot hyx)

theorem lt_of_mul_lt_mul_pos_left {x y z : alpha}
    (h : F.lt (F.mul z x) (F.mul z y))
    (hz : F.lt F.zero z) :
    F.lt x y := by
  apply lt_of_mul_lt_mul_pos_right F (z := z) ?_ hz
  rwa [F.mul_comm x z, F.mul_comm y z]

theorem inv_neg_of_ne_zero
    {x : alpha}
    (hx : Not (x = F.zero)) :
    F.inv (F.neg x) = F.neg (F.inv x) := by
  symm
  apply eq_inv_of_mul_eq_one_left F
  · intro hneg
    have h := congrArg F.neg hneg
    rw [neg_neg F x, neg_zero F] at h
    exact hx h
  · rw [F.neg_mul_neg]
    exact F.mul_inv_cancel hx

theorem inv_nonpos_of_neg
    {x : alpha}
    (hx : F.lt x F.zero) :
    F.le (F.inv x) F.zero := by
  have hx_ne : Not (x = F.zero) := by
    intro hzero
    rw [hzero] at hx
    exact lt_irrefl F F.zero hx
  have hnegx_pos : F.lt F.zero (F.neg x) := by
    have h := neg_lt_neg F hx
    change F.lt (F.neg F.zero) (F.neg x) at h
    rwa [neg_zero F] at h
  have hinv_negx_nonneg : F.le F.zero (F.inv (F.neg x)) :=
    le_of_lt F (inv_pos F hnegx_pos)
  have hinv_neg : F.inv (F.neg x) = F.neg (F.inv x) :=
    inv_neg_of_ne_zero F hx_ne
  have hneg_inv_nonneg : F.le F.zero (F.neg (F.inv x)) := by
    rwa [hinv_neg] at hinv_negx_nonneg
  have h := neg_le_neg F hneg_inv_nonneg
  change F.le (F.neg (F.neg (F.inv x))) (F.neg F.zero) at h
  rwa [neg_neg F (F.inv x), neg_zero F] at h

theorem neg_one_mul_eq_neg (x : alpha) :
    F.mul (F.neg F.one) x = F.neg x :=
  Eq.symm (neg_eq_neg_one_mul F x)

theorem value_sub_left_of_eq_add
    {x y z : alpha}
    (h : x = F.add y z) :
    z = F.sub x y := by
  calc
    z = F.add F.zero z := by rw [F.zero_add]
    _ = F.add (F.add (F.neg y) y) z := by rw [F.neg_add]
    _ = F.add (F.neg y) (F.add y z) := by rw [F.add_assoc]
    _ = F.add (F.neg y) x := by rw [← h]
    _ = F.add x (F.neg y) := by rw [F.add_comm]
    _ = F.sub x y := by rw [← F.sub_eq_add_neg]

theorem inv_le_inv_of_le_pos {a b : alpha}
    (ha : F.lt F.zero a)
    (hb : F.lt F.zero b)
    (hab : F.le a b) :
    F.le (F.inv b) (F.inv a) := by
  by_cases hle : F.le (F.inv b) (F.inv a)
  · exact hle
  · have hlt : F.lt (F.inv a) (F.inv b) := by
      cases F.le_total (F.inv a) (F.inv b) with
      | inl h =>
          exact lt_of_le_of_not_le F h hle
      | inr h =>
          exact False.elim (hle h)
    have ha_ne : Not (a = F.zero) := by
      intro h
      exact ne_of_lt F ha h.symm
    have hb_ne : Not (b = F.zero) := by
      intro h
      exact ne_of_lt F hb h.symm
    have hinvb_pos : F.lt F.zero (F.inv b) := inv_pos F hb
    have hmul_lt :
        F.lt (F.mul a (F.inv a)) (F.mul a (F.inv b)) :=
      mul_lt_mul_pos_left F hlt ha
    have hmul_le :
        F.le (F.mul a (F.inv b)) (F.mul b (F.inv b)) :=
      mul_le_mul_nonneg_right F hab (le_of_lt F hinvb_pos)
    have hone_lt :
        F.lt F.one (F.mul a (F.inv b)) := by
      rwa [F.mul_inv_cancel ha_ne] at hmul_lt
    have hle_one :
        F.le (F.mul a (F.inv b)) F.one := by
      rwa [F.mul_inv_cancel hb_ne] at hmul_le
    exact False.elim ((not_le_of_lt F hone_lt) hle_one)

theorem inv_lt_inv_of_lt_pos {a b : alpha}
    (ha : F.lt F.zero a)
    (hb : F.lt F.zero b)
    (hab : F.lt a b) :
    F.lt (F.inv b) (F.inv a) := by
  have hle :
      F.le (F.inv b) (F.inv a) :=
    inv_le_inv_of_le_pos F ha hb (le_of_lt F hab)
  apply lt_of_le_of_not_le F hle
  intro hrev
  have ha_nonneg : F.le F.zero a := le_of_lt F ha
  have hb_ne : Not (b = F.zero) := by
    intro h
    exact ne_of_lt F hb h.symm
  have ha_ne : Not (a = F.zero) := by
    intro h
    exact ne_of_lt F ha h.symm
  have hleft :
      F.le (F.mul a (F.inv a)) (F.mul a (F.inv b)) :=
    mul_le_mul_nonneg_left F hrev ha_nonneg
  have hleft_one :
      F.le F.one (F.mul a (F.inv b)) := by
    rwa [F.mul_inv_cancel ha_ne] at hleft
  have hinvb_pos : F.lt F.zero (F.inv b) := inv_pos F hb
  have hright :
      F.lt (F.mul a (F.inv b)) (F.mul b (F.inv b)) :=
    mul_lt_mul_pos_right F hab hinvb_pos
  have hright_one :
      F.lt (F.mul a (F.inv b)) F.one := by
    rwa [F.mul_inv_cancel hb_ne] at hright
  exact (not_le_of_lt F hright_one) hleft_one

theorem half_add (x y : alpha) :
    half F (F.add x y) =
      F.add (half F x) (half F y) := by
  unfold half
  exact F.add_mul x y (F.inv (two F))

theorem half_one_mul (x : alpha) :
    F.mul (half F F.one) x = half F x := by
  unfold half
  rw [F.one_mul]
  exact F.mul_comm (F.inv (two F)) x

theorem add_self_cancel {a b : alpha}
    (h : F.add a a = F.add b b) :
    a = b := by
  have hmul :
      F.mul (two F) a = F.mul (two F) b := by
    unfold two
    rw [F.add_mul, F.add_mul, F.one_mul, F.one_mul]
    exact h
  exact mul_left_cancel_of_ne_zero F (two_ne_zero F) hmul

theorem half_nonneg {eps : alpha}
    (heps : F.le F.zero eps) :
    F.le F.zero (half F eps) := by
  unfold half
  exact F.mul_nonneg heps
    (le_of_lt F (inv_pos F (zero_lt_two F)))

/-- The two one-sided descriptions of the midpoint agree: with
h = half (a - b), adding h to b and subtracting h from a give the same
point. The midpoint block below reaches the right endpoint through this, and
it is why no point can lie strictly between the two descriptions. -/
theorem add_half_sub_eq_sub_half (a b : alpha) :
    F.add b (half F (F.sub a b)) =
      F.sub a (half F (F.sub a b)) := by
  let eps := half F (F.sub a b)
  change F.add b eps = F.sub a eps
  apply add_right_cancel F (a := eps)
  calc
    F.add (F.add b eps) eps =
        F.add b (F.add eps eps) := by rw [F.add_assoc]
    _ = F.add b (F.sub a b) := by rw [half_add_half F (F.sub a b)]
    _ = F.add (F.sub a b) b := by rw [F.add_comm b (F.sub a b)]
    _ = a := sub_add_cancel F a b
    _ = F.add (F.sub a eps) eps := by rw [sub_add_cancel F a eps]

/-- No point lies strictly between a - half (a - b) and b + half (a - b): the
two endpoints are the same point, so this is irreflexivity of the strict order.
The limsup squeeze arguments above (`Tautology.RealSequence.Limsup`,
`Tautology.RealFunction.Limsup`) use it to refute a value pinned below one
description of the midpoint and above the other. -/
theorem not_between_sub_add_half {a b x : alpha}
    (hleft :
      F.lt (F.sub a (half F (F.sub a b))) x)
    (hright :
      F.lt x (F.add b (half F (F.sub a b)))) :
    False := by
  have hlt :
      F.lt (F.sub a (half F (F.sub a b)))
        (F.add b (half F (F.sub a b))) :=
    lt_trans F hleft hright
  rw [add_half_sub_eq_sub_half F a b] at hlt
  exact (lt_irrefl F (F.sub a (half F (F.sub a b)))) hlt

theorem sub_half_self (x : alpha) :
    F.sub x (half F x) = half F x := by
  apply add_right_cancel F (a := half F x)
  calc
    F.add (F.sub x (half F x)) (half F x) =
        x := sub_add_cancel F x (half F x)
    _ = F.add (half F x) (half F x) := by
        rw [half_add_half F x]

theorem add_half_add_half (x eps : alpha) :
    F.add (F.add x (half F eps)) (half F eps) =
      F.add x eps := by
  calc
    F.add (F.add x (half F eps)) (half F eps) =
        F.add x (F.add (half F eps) (half F eps)) := by
          rw [F.add_assoc]
    _ = F.add x eps := by
          rw [half_add_half F eps]

theorem sub_half_add_self (x eps : alpha) :
    F.add (F.sub x (half F eps)) eps =
      F.add x (half F eps) := by
  calc
    F.add (F.sub x (half F eps)) eps =
        F.add (F.sub x (half F eps))
          (F.add (half F eps) (half F eps)) := by
          rw [half_add_half F eps]
    _ = F.add (F.add (F.sub x (half F eps)) (half F eps))
        (half F eps) := by
          rw [<- F.add_assoc]
    _ = F.add x (half F eps) := by
          rw [sub_add_cancel F x (half F eps)]

theorem half_lt_self {x : alpha}
    (hx : F.lt F.zero x) :
    F.lt (half F x) x := by
  have hhalf : F.lt F.zero (half F x) :=
    half_pos F hx
  have h := add_lt_add_left F hhalf (half F x)
  rwa [F.add_zero, half_add_half F x] at h

/-- The midpoint of x and y, anchored at the left endpoint: x plus half of
y - x, so that the offset from x is available without further rewriting
(`midpoint_sub_left`). The mirrored description from y is recovered by
`midpoint_eq_sub_half`, and the bisection arguments of the library take
their nested intervals from these four position facts. -/
def midpoint (x y : alpha) : alpha :=
  F.add x (half F (F.sub y x))

theorem midpoint_sub_left (x y : alpha) :
    F.sub (midpoint F x y) x = half F (F.sub y x) := by
  unfold midpoint
  rw [F.add_comm x (half F (F.sub y x))]
  exact add_sub_cancel F (half F (F.sub y x)) x

theorem midpoint_eq_sub_half (x y : alpha) :
    midpoint F x y = F.sub y (half F (F.sub y x)) := by
  unfold midpoint
  exact add_half_sub_eq_sub_half F y x

theorem right_sub_midpoint (x y : alpha) :
    F.sub y (midpoint F x y) = half F (F.sub y x) := by
  rw [midpoint_eq_sub_half]
  exact sub_self_sub F y (half F (F.sub y x))

theorem left_le_midpoint {x y : alpha}
    (hxy : F.le x y) :
    F.le x (midpoint F x y) := by
  apply le_of_sub_nonneg F
  rw [midpoint_sub_left]
  exact half_nonneg F (sub_nonneg_of_le F hxy)

theorem midpoint_le_right {x y : alpha}
    (hxy : F.le x y) :
    F.le (midpoint F x y) y := by
  apply le_of_sub_nonneg F
  rw [right_sub_midpoint]
  exact half_nonneg F (sub_nonneg_of_le F hxy)

theorem left_lt_midpoint {x y : alpha}
    (hxy : F.lt x y) :
    F.lt x (midpoint F x y) := by
  apply lt_of_sub_pos F
  rw [midpoint_sub_left]
  exact half_pos F (sub_pos_of_lt F hxy)

theorem midpoint_lt_right {x y : alpha}
    (hxy : F.lt x y) :
    F.lt (midpoint F x y) y := by
  apply lt_of_sub_pos F
  rw [right_sub_midpoint]
  exact half_pos F (sub_pos_of_lt F hxy)

theorem add_left_comm (x y z : alpha) :
    F.add x (F.add y z) = F.add y (F.add x z) := by
  calc
    F.add x (F.add y z) = F.add (F.add x y) z := by
      rw [<- F.add_assoc]
    _ = F.add (F.add y x) z := by rw [F.add_comm x y]
    _ = F.add y (F.add x z) := by rw [F.add_assoc]

theorem add_add_sub_cancel_same (A B C : alpha) :
    F.add (F.add A C) (F.sub B C) = F.add A B := by
  calc
    F.add (F.add A C) (F.sub B C) =
        F.add A (F.add C (F.sub B C)) := by rw [F.add_assoc]
    _ = F.add A (F.add (F.sub B C) C) := by
      rw [F.add_comm C (F.sub B C)]
    _ = F.add A B := by rw [sub_add_cancel F B C]

theorem sub_add_add_cancel_same (A C : alpha) :
    F.add (F.sub A C) (F.add C C) = F.add A C := by
  calc
    F.add (F.sub A C) (F.add C C) =
        F.add (F.add (F.sub A C) C) C := by rw [<- F.add_assoc]
    _ = F.add A C := by rw [sub_add_cancel F A C]

private theorem add_four_reorder (A B C D : alpha) :
    F.add (F.add A D) (F.add C B) =
      F.add (F.add A B) (F.add C D) := by
  calc
    F.add (F.add A D) (F.add C B) =
        F.add A (F.add D (F.add C B)) := by rw [F.add_assoc]
    _ = F.add A (F.add C (F.add D B)) := by
      rw [add_left_comm F D C B]
    _ = F.add A (F.add C (F.add B D)) := by rw [F.add_comm D B]
    _ = F.add A (F.add B (F.add C D)) := by
      rw [add_left_comm F C B D]
    _ = F.add (F.add A B) (F.add C D) := by rw [<- F.add_assoc]

private theorem add_square_raw (a b : alpha) :
    F.mul (F.add a b) (F.add a b) =
      F.add (F.add (F.mul a a) (F.mul a b))
        (F.add (F.mul b a) (F.mul b b)) := by
  rw [F.mul_add, F.add_mul, F.add_mul]
  calc
    F.add (F.add (F.mul a a) (F.mul b a))
        (F.add (F.mul a b) (F.mul b b)) =
        F.add (F.mul a a)
          (F.add (F.mul b a) (F.add (F.mul a b) (F.mul b b))) := by
            rw [F.add_assoc]
    _ = F.add (F.mul a a)
          (F.add (F.mul a b) (F.add (F.mul b a) (F.mul b b))) := by
            rw [add_left_comm F (F.mul b a) (F.mul a b) (F.mul b b)]
    _ = F.add (F.add (F.mul a a) (F.mul a b))
          (F.add (F.mul b a) (F.mul b b)) := by rw [<- F.add_assoc]

theorem add_square (a b : alpha) :
    F.mul (F.add a b) (F.add a b) =
      F.add (F.add (F.mul a a) (F.mul b b))
        (F.add (F.mul a b) (F.mul b a)) := by
  rw [add_square_raw F a b]
  let A := F.mul a a
  let B := F.mul a b
  let C := F.mul b a
  let D := F.mul b b
  change F.add (F.add A B) (F.add C D) =
    F.add (F.add A D) (F.add B C)
  calc
    F.add (F.add A B) (F.add C D) = F.add A (F.add B (F.add C D)) := by
      rw [F.add_assoc]
    _ = F.add A (F.add (F.add B C) D) := by rw [<- F.add_assoc B C D]
    _ = F.add A (F.add D (F.add B C)) := by rw [F.add_comm (F.add B C) D]
    _ = F.add (F.add A D) (F.add B C) := by rw [<- F.add_assoc]

theorem sub_square (a b : alpha) :
    F.mul (F.sub a b) (F.sub a b) =
      F.sub (F.add (F.mul a a) (F.mul b b))
        (F.add (F.mul a b) (F.mul b a)) := by
  rw [F.sub_eq_add_neg, F.add_mul, F.mul_add, F.mul_add]
  rw [mul_neg F, neg_mul F, F.neg_mul_neg]
  rw [F.sub_eq_add_neg, neg_add_distrib F]
  let aa := F.mul a a
  let ab := F.mul a b
  let ba := F.mul b a
  let bb := F.mul b b
  change F.add (F.add aa (F.neg ab)) (F.add (F.neg ba) bb) =
    F.add (F.add aa bb) (F.add (F.neg ab) (F.neg ba))
  calc
    F.add (F.add aa (F.neg ab)) (F.add (F.neg ba) bb) =
        F.add aa (F.add (F.neg ab) (F.add (F.neg ba) bb)) := by
          rw [F.add_assoc]
    _ = F.add aa (F.add (F.add (F.neg ab) (F.neg ba)) bb) := by
      rw [<- F.add_assoc (F.neg ab) (F.neg ba) bb]
    _ = F.add aa (F.add bb (F.add (F.neg ab) (F.neg ba))) := by
      rw [F.add_comm (F.add (F.neg ab) (F.neg ba)) bb]
    _ = F.add (F.add aa bb) (F.add (F.neg ab) (F.neg ba)) := by
      rw [<- F.add_assoc]

theorem add_sub_add_sub_eq_sub_add (A B C D : alpha) :
    F.add (F.sub A B) (F.sub C D) =
      F.sub (F.add A C) (F.add B D) := by
  exact (add_sub_add_eq_sub_add_sub F A C B D).symm

theorem sub_sub_add_eq_sub_sub_add (A B C D : alpha) :
    F.sub (F.sub A B) (F.add C D) =
      F.sub (F.sub A D) (F.add B C) := by
  rw [F.sub_eq_add_neg A B]
  rw [F.sub_eq_add_neg (F.add A (F.neg B)) (F.add C D)]
  rw [neg_add_distrib F C D]
  rw [F.sub_eq_add_neg A D]
  rw [F.sub_eq_add_neg (F.add A (F.neg D)) (F.add B C)]
  rw [neg_add_distrib F B C]
  calc
    F.add (F.add A (F.neg B)) (F.add (F.neg C) (F.neg D)) =
        F.add A (F.add (F.neg B) (F.add (F.neg C) (F.neg D))) := by
          rw [F.add_assoc]
    _ = F.add A (F.add (F.neg D) (F.add (F.neg B) (F.neg C))) := by
      rw [<- F.add_assoc (F.neg B) (F.neg C) (F.neg D)]
      rw [F.add_comm (F.add (F.neg B) (F.neg C)) (F.neg D)]
    _ = F.add (F.add A (F.neg D)) (F.add (F.neg B) (F.neg C)) := by
      rw [<- F.add_assoc]

private theorem sub_sub_sub_eq_add_sub_add (A B C D : alpha) :
    F.sub (F.sub A B) (F.sub C D) =
      F.sub (F.add A D) (F.add B C) := by
  rw [F.sub_eq_add_neg A B, F.sub_eq_add_neg C D]
  rw [F.sub_eq_add_neg (F.add A (F.neg B)) (F.add C (F.neg D))]
  rw [neg_add_distrib F C (F.neg D), neg_neg F D]
  rw [F.sub_eq_add_neg (F.add A D) (F.add B C)]
  rw [neg_add_distrib F B C]
  calc
    F.add (F.add A (F.neg B)) (F.add (F.neg C) D) =
        F.add (F.add A D) (F.add (F.neg C) (F.neg B)) := by
          exact Eq.symm (add_four_reorder F A (F.neg B) (F.neg C) D)
    _ = F.add (F.add A D) (F.add (F.neg B) (F.neg C)) := by
      rw [F.add_comm (F.neg C) (F.neg B)]

theorem sub_mul_sub (a b c d : alpha) :
    F.mul (F.sub a b) (F.sub c d) =
      F.sub (F.add (F.mul a c) (F.mul b d))
        (F.add (F.mul a d) (F.mul b c)) := by
  rw [sub_mul_eq_sub_mul F a b (F.sub c d)]
  rw [mul_sub_eq_mul_sub F a c d, mul_sub_eq_mul_sub F b c d]
  exact sub_sub_sub_eq_add_sub_add F
    (F.mul a c) (F.mul a d) (F.mul b c) (F.mul b d)

private theorem cross_terms_eq (a b c d : alpha) :
    F.add (F.mul (F.mul a b) (F.mul c d))
        (F.mul (F.mul c d) (F.mul a b)) =
      F.add (F.mul (F.mul c b) (F.mul a d))
        (F.mul (F.mul a d) (F.mul c b)) := by
  calc
    F.add (F.mul (F.mul a b) (F.mul c d))
        (F.mul (F.mul c d) (F.mul a b)) =
        F.add (F.mul (F.mul a c) (F.mul b d))
          (F.mul (F.mul c a) (F.mul d b)) := by
            rw [mul_mul_mul_comm F a b c d, mul_mul_mul_comm F c d a b]
    _ = F.add (F.mul (F.mul a c) (F.mul b d))
        (F.mul (F.mul a c) (F.mul b d)) := by
          rw [F.mul_comm c a, F.mul_comm d b]
    _ = F.add (F.mul (F.mul c b) (F.mul a d))
        (F.mul (F.mul a d) (F.mul c b)) := by
          rw [mul_mul_mul_comm F c b a d, mul_mul_mul_comm F a d c b]
          rw [F.mul_comm c a, F.mul_comm d b]

private theorem sum_squares_pair_identity (a b c d : alpha) :
    F.add
        (F.add (F.mul (F.mul a b) (F.mul a b))
          (F.mul (F.mul c d) (F.mul c d)))
        (F.add (F.mul (F.mul c b) (F.mul c b))
          (F.mul (F.mul a d) (F.mul a d))) =
      F.mul (F.add (F.mul a a) (F.mul c c))
        (F.add (F.mul b b) (F.mul d d)) := by
  rw [mul_mul_mul_comm F a b a b, mul_mul_mul_comm F c d c d]
  rw [mul_mul_mul_comm F c b c b, mul_mul_mul_comm F a d a d]
  let A := F.mul (F.mul a a) (F.mul b b)
  let B := F.mul (F.mul a a) (F.mul d d)
  let C := F.mul (F.mul c c) (F.mul b b)
  let D := F.mul (F.mul c c) (F.mul d d)
  change F.add (F.add A D) (F.add C B) =
    F.mul (F.add (F.mul a a) (F.mul c c))
      (F.add (F.mul b b) (F.mul d d))
  calc
    F.add (F.add A D) (F.add C B) = F.add (F.add A B) (F.add C D) := by
      exact add_four_reorder F A B C D
    _ = F.mul (F.add (F.mul a a) (F.mul c c))
        (F.add (F.mul b b) (F.mul d d)) := by
          symm
          rw [F.add_mul, F.mul_add, F.mul_add]

/-- The two-squares identity: (ab + cd) squared plus (bc - ad) squared equals
(a^2 + c^2) times (b^2 + d^2) -- a product of sums of two squares is again a
sum of two squares. Upstream it serves the lemniscatic addition theory
(`Tautology.RealElliptic.Lemniscatic`) and the arcsine substitution
(`Tautology.RealDerivative.Integral.Riemann.Substitution.Classical.Arcsine`).
-/
theorem brahmagupta_fibonacci_identity (a b c d : alpha) :
    F.add
        (F.mul (F.add (F.mul a b) (F.mul c d))
          (F.add (F.mul a b) (F.mul c d)))
        (F.mul (F.sub (F.mul c b) (F.mul a d))
          (F.sub (F.mul c b) (F.mul a d))) =
      F.mul (F.add (F.mul a a) (F.mul c c))
        (F.add (F.mul b b) (F.mul d d)) := by
  let p := F.mul a b
  let q := F.mul c d
  let r := F.mul c b
  let s := F.mul a d
  change F.add (F.mul (F.add p q) (F.add p q))
      (F.mul (F.sub r s) (F.sub r s)) =
    F.mul (F.add (F.mul a a) (F.mul c c))
      (F.add (F.mul b b) (F.mul d d))
  rw [add_square F p q, sub_square F r s]
  rw [<- cross_terms_eq F a b c d]
  calc
    F.add
        (F.add (F.add (F.mul p p) (F.mul q q))
          (F.add (F.mul p q) (F.mul q p)))
        (F.sub (F.add (F.mul r r) (F.mul s s))
          (F.add (F.mul p q) (F.mul q p))) =
        F.add (F.add (F.mul p p) (F.mul q q))
          (F.add (F.mul r r) (F.mul s s)) := by
            exact add_add_sub_cancel_same F
              (F.add (F.mul p p) (F.mul q q))
              (F.add (F.mul r r) (F.mul s s))
              (F.add (F.mul p q) (F.mul q p))
    _ = F.mul (F.add (F.mul a a) (F.mul c c))
        (F.add (F.mul b b) (F.mul d d)) := by
          exact sum_squares_pair_identity F a b c d

/-- A difference rewritten as a difference of squares over the sum: a - b
equals (a * a - b * b) times inv (a + b), whenever the sum is nonzero. The
lemniscatic theory (`Tautology.RealElliptic.Lemniscatic`) and the arcsine
substitution
(`Tautology.RealDerivative.Integral.Riemann.Substitution.Classical.Arcsine`)
both trade through it. -/
theorem difference_eq_square_difference_mul_inv_sum
    {a b : alpha} (hsum : Not (F.add a b = F.zero)) :
    F.sub a b = F.mul (F.sub (F.mul a a) (F.mul b b))
      (F.inv (F.add a b)) := by
  have hsquare :
      F.sub (F.mul a a) (F.mul b b) =
        F.mul (F.sub a b) (F.add a b) := by
    rw [mul_sub_mul_eq_sub_mul_add_mul_sub F a a b b]
    rw [F.mul_add, F.mul_comm b (F.sub a b)]
  rw [hsquare]
  exact Eq.symm (mul_mul_inv_cancel_right F (F.sub a b) hsum)

end IsOrderedFieldBaseLike
end Tautology
