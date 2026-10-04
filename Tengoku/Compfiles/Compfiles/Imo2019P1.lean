/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2019, Problem 1
Let ℤ be the set of integers. Determine all functions f : ℤ → ℤ such that,
for all integers a and b,￼

   f(2 * a) + 2 * f(b) = f(f(a + b)).
-/

namespace Imo2019P1

-- proof of the following lemma suggested on Zulip by Riccardo Brasca
lemma additive_to_int_linear (f : ℤ → ℤ) (h: ∀ (x y : ℤ), f (x + y) = f x + f y):
   ∃ c, ∀ a, f a = c * a := by
  let g := AddMonoidHom.toIntLinearMap <| AddMonoidHom.mk' f h
  refine ⟨f 1, fun a => ?_⟩
  change g a = g 1 * a
  exact (Dual.apply_one_mul_eq g a).symm

abbrev solution_set : Set (ℤ → ℤ) :=
  { f | (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c }

end Imo2019P1
