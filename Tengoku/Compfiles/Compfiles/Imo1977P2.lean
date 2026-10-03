/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1977, Problem 2

In a finite sequence of real numbers the sum of any seven successive terms is negative and the sum of any eleven successive terms is positive.
Determine the maximum number of terms in the sequence.

-/

namespace Imo1977P2

def sum_successive_terms {α : Type} [AddCommMonoid α] {n : ℕ} (s : Fin n → α) (start : Fin n) (count : ℕ) [NeZero count] (h : start+count-1 < n) : α :=
  ∑ i ∈ Finset.Icc start ⟨start+count-1, h⟩, s i

open Matrix

@[coe]
def coeFunctionInt2Real {α : Type*} (f : α → ℤ) : (α → ℝ) := fun x => (f x).cast

instance {α : Type*} : Coe (α → ℤ) (α → ℝ) := {
  coe := coeFunctionInt2Real
}

theorem sum_successive_terms_intCast {n : ℕ} (s : Fin n → ℤ) (start : Fin n) (count : ℕ) [NeZero count] (h : start+count-1 < n) :
    sum_successive_terms s start count h = (sum_successive_terms s start count h : ℝ) := by
  unfold sum_successive_terms coeFunctionInt2Real
  simp

def example_16_int : Fin 16 → ℤ := ![5, 5, -13, 5, 5, 5, -13, 5, 5, -13, 5, 5, 5, -13, 5, 5]

def example_16 : Fin 16 → ℝ := (example_16_int : Fin 16 → ℝ)

abbrev max_num_terms : ℕ := 16

end Imo1977P2
