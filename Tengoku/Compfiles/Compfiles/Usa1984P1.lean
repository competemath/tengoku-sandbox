/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1984, Problem 1

Two roots of the real quartic x⁴ - 18x³ + ax² + 200x - 1984 = 0
have product -32. Find a.
-/

namespace Usa1984P1

open Polynomial

abbrev solution : ℝ := 86

/-- A monic quadratic polynomial is determined by its lower coefficients. -/
theorem eq_X_sq_add_of_monic_of_natDegree_eq_two {R : Type*} [CommRing R] {q : R[X]}
    (hm : q.Monic) (hd : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow, hd]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  have hc2 : q.coeff 2 = 1 := by
    have h := hm.coeff_natDegree
    rwa [hd] at h
  simp only [hc2, map_one]
  ring

end Usa1984P1
