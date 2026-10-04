/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256, hillosanation
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2007 P5
Prove that for every nonnegative integer n, the number 7^7^n + 1 is the product of at
least 2n + 3 (not necessarily distinct) primes.
-/

namespace USA2007P5
open Nat
/-Proof ideas derived from an assortment of posts on https://artofproblemsolving.com/community/c6h145849p825508
  Several lemmas might be useful, such as any natural number having at least one prime factor and any composite having at least two.
-/

lemma factor_poly_an (t : ℕ) : t^7 + 1 = (t + 1) * ((t^6 - t^5) + (t^4 - t^3) + (t^2 - t) + 1) := by
  cases t
  · decide
  · grind [add_mul, Nat.mul_add, Nat.mul_sub]

lemma factor_poly_bn (t : ℕ) : ((t^6 - t^5) + (t^4 - t^3) + (t^2 - t) + 1) = (t+1)^6 - (7*t)*(t^2+t+1)^2 := by
  cases t
  · decide
  · lia

end USA2007P5
