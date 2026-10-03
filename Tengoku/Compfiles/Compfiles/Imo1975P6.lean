/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1975, Problem 6

Find all polynomials P, in two variables, with the following properties:

(i) for a positive integer n and all real t, x, y
  P(tx, ty) = tⁿP(x, y)
(that is, P is homogeneous of degree n),

(ii) for all real a, b, c,
  P(b + c, a) + P(c + a, b) + P(a + b, c) = 0,

(iii) P(1, 0) = 1.
-/

namespace Imo1975P6

open Polynomial
open Polynomial.Bivariate

abbrev solution_set : Set (ℝ[X][Y]) := {P | ∃ n : ℕ, P = (C X - 2 * Y)*(C X + Y)^n}

lemma mul_pow_eq_pow_succ {n : ℕ} (hn : 0 < n) (t : ℝ) : t * t^(n - 1) = t^n := by
  rw [←(pow_mul_comm' t (n - 1)), ← pow_succ, Nat.sub_add_cancel hn]

lemma eq_if_continuous_and_eq_almost_everywhere {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : ℚ, f x = g x) : ∀ x, f x = g x := by
  have hrat : Set.range Rat.cast ⊆ {x | f x = g x} := fun x hx ↦ by grind
  have hclosure := (isClosed_eq hf hg).closure_subset_iff.mpr hrat
  exact fun _ ↦ hclosure (by simp [Rat.denseRange_cast.closure_eq])

lemma eq_if_continuous_and_eq_except_one_point {f g : ℝ → ℝ} {a : ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, x ≠ a → f x = g x) : f = g := by
  have hDense : Dense {x | x ≠ a} := by
    have h : {x : ℝ | x ≠ a} = {a}ᶜ := by ext x; simp
    rw [h]
    exact dense_compl_singleton a
  exact Continuous.ext_on hDense hf hg h

lemma eq_if_evalEval_eq {P Q : ℝ[X][Y]} (h : ∀ x y, P.evalEval x y = Q.evalEval x y) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq P Q
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Polynomial.C_injective)
  intro z hz
  rcases hz with ⟨y, rfl⟩
  exact Polynomial.funext (fun x ↦ h x y)

lemma aux₁ {n : ℕ} (h : 1 < n) : (2 : ℝ) ^ n + 2 * (-1)^n ≠ 0 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa using ne_of_gt (by positivity)
  · apply ne_of_gt
    rw [pow_add (-1), pow_mul]
    norm_num
    nth_rw 1 [← pow_one 2]
    exact pow_lt_pow_right₀ one_lt_two h

lemma aux₂ {a b c : ℝ} {n : ℕ} (h : b ≠ 0): a = b⁻¹^n * c → a * b^n = c := by
  intro h1
  rw [h1, mul_assoc, mul_comm, mul_assoc]
  aesop

lemma linear_int {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) :
    ∀ (n : ℤ) {x : ℝ}, f (n * x) = n * f x := by
  intro n
  induction' n using Int.induction_on with n ih n ih
  · grind [h 0 0]
  all_goals
    intro x
    simp_all
    grind [h (n * x) x, h (-(n * x)) (-x), h x (-x), h 0 0]

lemma linear_inv {f : ℝ → ℝ} (h : ∀ (n : ℤ) {x : ℝ}, f (n * x) = n * f x) :
    ∀ (n : ℤ), f (1 / n) = (1 / n) * f 1 := by
  intro n
  by_cases hn : n = 0 <;> grind only

lemma linear_rat {f : ℝ → ℝ} (h : ∀ (n : ℤ) {x : ℝ}, f (n * x) = n * f x) :
    ∀ (x : ℚ), f x = f 1 * x := by
  intro x
  have h1 := h x.num (x := 1 / x.den)
  have h2 : ((x.den : ℤ) : ℝ) = (x.den : ℝ) := AddCommGroupWithOne.intCast_ofNat x.den
  have h3 : (x.num : ℝ) * (1 / x.den) = x := by rw [Field.ratCast_def x] ; ring
  rwa [h3, ← h2, linear_inv h x.den, ← mul_assoc, h2, h3, mul_comm] at h1

end Imo1975P6
