/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1989, Problem 3

Let P(z) = zⁿ + c₁zⁿ⁻¹ + ⋯ + cₙ be a polynomial in the complex variable z,
with real coefficients cₖ. Suppose that |P(i)| < 1. Prove that there exist
real numbers a and b such that P(a + bi) = 0 and (a² + b² + 1)² < 4b² + 1.
-/

namespace Usa1989P3

open Polynomial

/-- Evaluating a polynomial whose coefficients are all real at the conjugate
of `z` is the same as conjugating its value at `z`. -/
theorem star_eval {P : ℂ[X]} (hreal : ∀ n : ℕ, (P.coeff n).im = 0) (z : ℂ) :
    star (P.eval z) = P.eval (star z) := by
  have h : (starRingEnd ℂ) (P.eval z) = P.eval ((starRingEnd ℂ) z) := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow]
    congr 1
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im]
    exact hreal k
  exact h

/-- For a complex number `r`, the product of the squared distances from `r`
to `i` and to `-i` equals `(r.re² + r.im² + 1)² - 4 r.im²`. -/
theorem normSq_I_sub_mul_normSq_I_add (r : ℂ) :
    Complex.normSq (Complex.I - r) * Complex.normSq (Complex.I + r) =
      (r.re ^ 2 + r.im ^ 2 + 1) ^ 2 - 4 * r.im ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im]
  ring

/-- The squared distances from the roots of a monic polynomial to a point `z`
multiply to the squared norm of the value of the polynomial at `z`. -/
theorem prod_normSq_sub_roots {P : ℂ[X]} (hsplit : P.Splits) (hmonic : P.Monic) (z : ℂ) :
    (P.roots.map fun r ↦ Complex.normSq (z - r)).prod =
      Complex.normSq (P.eval z) := by
  rw [hsplit.eval_eq_prod_roots_of_monic hmonic, map_multiset_prod, Multiset.map_map]
  rfl

/-- The squared distances from the roots of a monic polynomial to a point `z`,
with signs flipped, again multiply to the squared norm of the value of the
polynomial at `-z`. -/
theorem prod_normSq_add_roots {P : ℂ[X]} (hsplit : P.Splits) (hmonic : P.Monic) (z : ℂ) :
    (P.roots.map fun r ↦ Complex.normSq (z + r)).prod =
      Complex.normSq (P.eval (-z)) := by
  have h1 : (fun r : ℂ ↦ Complex.normSq (z + r)) = fun r ↦ Complex.normSq (-z - r) := by
    funext r
    have h2 : z + r = -(-z - r) := by ring
    rw [h2, Complex.normSq_neg]
  rw [h1, prod_normSq_sub_roots hsplit hmonic (-z)]

end Usa1989P3
