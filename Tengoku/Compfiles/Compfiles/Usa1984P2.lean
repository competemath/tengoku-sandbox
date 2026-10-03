/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1984, Problem 2

Can one find a set of n distinct positive integers such that the
geometric mean of any (non-empty, finite) subset is an integer?
Can one find an infinite set with this property?
-/

namespace Usa1984P2

open scoped Nat

/-- The key divisibility fact for the second part: if `y * C` and `z * C`
(with `y`, `z`, `C` positive) are both `k`-th powers, then `k` divides the
difference of the multiplicities of any number `p` in the prime
factorizations of `y` and `z`. -/
theorem factorization_eq_of_pow (k : ℕ) (hk : 0 < k) (y z C : ℕ)
    (hy : y ≠ 0) (hz : z ≠ 0) (hC : C ≠ 0)
    (u : ℕ) (hu : u ^ k = y * C) (v : ℕ) (hv : v ^ k = z * C) (p : ℕ) :
    (k : ℤ) ∣ (Nat.factorization y p : ℤ) - Nat.factorization z p := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hu
    exact mul_ne_zero hy hC hu.symm
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hv
    exact mul_ne_zero hz hC hv.symm
  have eu : Nat.factorization (u ^ k) p = k * Nat.factorization u p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have ev : Nat.factorization (v ^ k) p = k * Nat.factorization v p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hu, Nat.factorization_mul hy hC, Finsupp.add_apply] at eu
  rw [hv, Nat.factorization_mul hz hC, Finsupp.add_apply] at ev
  use (Nat.factorization u p : ℤ) - Nat.factorization v p
  have e1 : (k : ℤ) * Nat.factorization u p =
      Nat.factorization y p + Nat.factorization C p := by
    exact_mod_cast eu.symm
  have e2 : (k : ℤ) * Nat.factorization v p =
      Nat.factorization z p + Nat.factorization C p := by
    exact_mod_cast ev.symm
  linear_combination e2 - e1

abbrev does_exist_finite : Bool := true

abbrev does_exist_infinite : Bool := false

end Usa1984P2
