/-
Copyright (c) 2025 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1961, Problem 2

Let $a, b, c$ be the sides of a triangle, and $T$ its area. Prove:
$$ a^2 + b^2 + c^2 \ge 4\sqrt{3} T $$
Equality holds if and only if the triangle is equilateral.
-/

namespace Imo1961P2

/-
## Proof strategy

We use Heron's formula to express the area $T$ in terms of the sides $a, b, c$.
The inequality is then equivalent to the algebraic inequality:
$$(a^2 + b^2 + c^2)^2 \ge 48 T^2$$
Substituting Heron's formula leads to a sum of squares identity.
-/

/--
Helper lemma: The key algebraic identity for Weitzenböck's inequality.
(a^2 + b^2 + c^2)^2 - 48 T^2 = 2((a^2-b^2)^2 + (b^2-c^2)^2 + (c^2-a^2)^2)
-/
lemma weitzenbock_identity (a b c T : ℝ)
    (h_area : 16 * T^2 = (a + b + c) * (a + b - c) * (a - b + c) * (-a + b + c)) :
    (a^2 + b^2 + c^2)^2 - 48 * T^2 =
    2 * ((a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2) := by
  have h48T : 48 * T^2 = 3 * (16 * T^2) := by ring
  rw [h48T, h_area]
  ring

end Imo1961P2
