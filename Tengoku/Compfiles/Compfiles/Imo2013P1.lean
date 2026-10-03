/-
Copyright (c) 2021 David Renshaw. All rights reserved.
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
# International Mathematical Olympiad 2013, Problem 1

Prove that for any pair of positive integers k and n, there exist k positive integers
m₁, m₂, ..., mₖ (not necessarily different) such that

  1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).

-/

namespace Imo2013P1

/-
# Solution

Adaptation of the solution found in https://www.imo-official.org/problems/IMO2013SL.pdf

We prove a slightly more general version where k does not need to be strictly positive.
-/

theorem prod_lemma (m : ℕ → ℕ+) (k : ℕ) (nm : ℕ+) :
    ∏ i ∈ Finset.range k, ((1 : ℚ) + 1 / ↑(if i < k then m i else nm)) =
      ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by
  suffices ∀ i, i ∈ Finset.range k → (1 : ℚ) + 1 / ↑(if i < k then m i else nm) = 1 + 1 / m i from
    Finset.prod_congr rfl this
  intro i hi
  simp [Finset.mem_range.mp hi]

end Imo2013P1
