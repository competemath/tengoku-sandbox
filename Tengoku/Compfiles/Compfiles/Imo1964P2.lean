/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1964, Problem 2

Suppose that a,b,c are the side lengths of a triangle. Prove that

   a²(b + c - a) + b²(c + a - b) + c²(a + b - c) ≤ 3abc.
-/

namespace Imo1964P2

-- TODO: get this into mathlib in some form
lemma schur {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  -- from https://artofproblemsolving.com/wiki/index.php/Schur%27s_Inequality
  wlog Hcb : c ≤ b with h1
  · have h3 : b ≤ c := le_of_not_ge Hcb
    linarith [h1 ha hc hb h3]
  wlog Hba : b ≤ a with h2
  · have h4 : a ≤ b := le_of_not_ge Hba
    obtain hca | hac : c ≤ a ∨ a ≤ c := le_total c a
    · have := h2 hb ha hc hca h4
      linarith only [this]
    · have := h2 hb hc ha hac Hcb
      linarith only [this]
  have h5 : a * (a - b) * (a - c) + b * (b - a) * (b - c) =
            (a - b) * (a * (a - c) - b * (b - c)) := by ring

  have h6 : 0 ≤ (a - b) * (a * (a - c) - b * (b - c)) := by bound

  rw [← h5] at h6
  have h12 : 0 ≤ (c - a) * (c - b) := by nlinarith only [Hba, Hcb]
  have h13 : 0 ≤ c * (c - a) * (c - b) := by nlinarith only [hc, h12]
  positivity

end Imo1964P2
