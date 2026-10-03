/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1963, Problem 1

Find all real roots of the equation

  √(x²-p) + 2√(x²-1) = x

where *p* is a real parameter.
-/

namespace Imo1963P1

lemma iff_comm {a b c : Prop} : (a → c) → (b → c) → (c → (a ↔ b)) → (a ↔ b) := by
  grind

abbrev f (p : ℝ) : Set ℝ :=
  if 0 ≤ p ∧ p ≤ (4 : ℝ) / 3
  then { (4 - p) / (2 * Real.sqrt (4 - 2 * p)) }
  else ∅

end Imo1963P1
