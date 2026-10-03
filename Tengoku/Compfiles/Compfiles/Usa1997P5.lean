/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1997, Problem 5

Let a, b, c be positive reals.
Prove that
1 / (a³ + b³ + abc) + 1 / (b³ + c³ + abc) + 1 / (c³ + a³ + abc) ≤ 1 / abc
-/

open Real

namespace Usa1997P5

variable {a b c : ℝ}

-- Follows the solution at https://web.evanchen.cc/exams/USAMO-1997-notes.pdf
-- One just cyclically sums 1 / (a³ + b³ + abc) ≤ 1 / (ab(a+b) + abc)

-- Bounding the individual fraction
lemma bound (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a*b*c) ≤ 1 / (a^2*b + a*b^2 + a*b*c) := by
  field_simp -- clear denominators
  have h : 0 ≤ (a-b)^2*(a+b) := by positivity
  linarith

-- Add the three bounds together
theorem main_sum (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) +
      (1 / (b ^ 3 + c ^ 3 + b * c * a) + 1 / (c ^ 3 + a ^ 3 + c * a * b)) ≤
    1 / (a ^ 2 * b + a * b ^ 2 + a * b * c) +
      (1 / (b ^ 2 * c + b * c ^ 2 + b * c * a) +
         1 / (c ^ 2 * a + c * a ^ 2 + c * a * b)):=
  let h1 := bound ha hb hc
  let h2 := bound hb hc ha
  let h3 := bound hc ha hb
  add_le_add h1 (add_le_add h2 h3)

end Usa1997P5
