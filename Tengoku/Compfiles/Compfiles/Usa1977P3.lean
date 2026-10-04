/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1977, Problem 3

Prove that the product of the two real roots of x⁴ + x³ - 1 = 0
is a root of x⁶ + x⁴ + x³ - x² - 1 = 0.
-/

namespace Usa1977P3

/--
Suppose that `x ^ 4 + x ^ 3 - 1` is divisible by the quadratic
`x ^ 2 - s * x + p`, i.e. both coefficients of the remainder
`(s ^ 3 + s ^ 2 - 2 * p * s - p) * x + (p ^ 2 - p * (s ^ 2 + s) - 1)`
of the long division vanish. Then `p` is a root of the sextic
`x ^ 6 + x ^ 4 + x ^ 3 - x ^ 2 - 1`.

This is the Vieta elimination step of the problem: writing the four roots
of the quartic as `a, b, c, d` with `s = a + b` and `p = a * b`, the two
remainder relations are exactly the third and fourth elementary symmetric
relations between the roots.
-/
lemma sextic_of_zero_remainder {s p : ℝ}
    (hr1 : s ^ 3 + s ^ 2 - 2 * p * s - p = 0)
    (hr0 : p ^ 2 - p * (s ^ 2 + s) - 1 = 0) :
    p ^ 6 + p ^ 4 + p ^ 3 - p ^ 2 - 1 = 0 := by
  -- Rewrite the two remainder relations.
  have hB : p * (s ^ 2 + s) = p ^ 2 - 1 := by linear_combination -hr0
  have hs : s * (s ^ 2 + s - 2 * p) = p := by linear_combination hr1
  -- In particular `p` cannot vanish.
  have hp : p ≠ 0 := by
    intro h
    rw [h] at hB
    norm_num at hB
  -- Eliminate `s`: use `s * (s ^ 2 + s - 2 * p) = p` twice in
  -- `(s ^ 2 + s) * (s ^ 2 + s - 2 * p) ^ 2 = s * (s + 1) * (s ^ 2 + s - 2 * p) ^ 2`.
  have h4 : (s ^ 2 + s) * (s ^ 2 + s - 2 * p) ^ 2 = p * (s ^ 2 + s - p) := by
    linear_combination (p + (s + 1) * (s ^ 2 + s - 2 * p)) * hs
  -- Combine with `hB` to get `(s ^ 2 + s) * (s ^ 2 + s - 2 * p) ^ 2 = -1`.
  have h4' : (s ^ 2 + s) * (s ^ 2 + s - 2 * p) ^ 2 = -1 := by
    linear_combination h4 + hB
  -- Now `s ^ 2 + s = (p ^ 2 - 1) / p`, and substituting gives the sextic.
  have hu : s ^ 2 + s = (p ^ 2 - 1) / p := by
    field_simp
    linear_combination hB
  rw [hu] at h4'
  field_simp at h4'
  linear_combination h4'

end Usa1977P3
