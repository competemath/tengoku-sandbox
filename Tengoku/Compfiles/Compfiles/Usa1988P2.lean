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
# USA Mathematical Olympiad 1988, Problem 2

The cubic x^3 + ax^2 + bx + c has real coefficients and three real roots
r ≥ s ≥ t. Show that k = a^2 - 3b ≥ 0 and that √k ≤ r - t.
-/

namespace Usa1988P2

open Polynomial

-- Solution adapted from https://prase.cz/kalva/usa/usoln/usol882.html
-- By Vieta's formulas a = -(r + s + t) and b = rs + st + tr, so
-- a^2 - 3b = r^2 + s^2 + t^2 - (rs + st + tr), a sum of squares,
-- and (r - t)^2 - (a^2 - 3b) = (r - s)(s - t) ≥ 0.

-- Vieta's formulas for a and b, obtained by differentiating the
-- polynomial identity once resp. twice and evaluating at 0.
lemma vieta (a b c r s t : ℝ)
    (h : (X - C r) * (X - C s) * (X - C t) = X ^ 3 + C a * X ^ 2 + C b * X + C c) :
    a = -(r + s + t) ∧ b = r * s + s * t + t * r := by
  constructor
  · apply_fun (·.derivative.derivative.eval 0) at h
    simp at h
    linarith
  · apply_fun (·.derivative.eval 0) at h
    simp at h
    linarith

end Usa1988P2
