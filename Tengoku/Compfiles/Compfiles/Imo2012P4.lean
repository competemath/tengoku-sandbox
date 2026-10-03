/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: spinylobster, ondanaoto, Seasawher
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 2012, Problem 4

Determine all functions f : ℤ → ℤ such that for all integers a,b,c with a + b + c = 0,
the following equality holds:
  f(a)² + f(b)² + f(c)² = 2f(a)f(b) + 2f(b)f(c) + 2f(c)f(a).
-/

namespace Imo2012P4

def odd_const : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ,
    (Odd x → f x = c) ∧ (Even x → f x = 0)

def mod4_cycle : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ, f x =
  match x % 4 with
    | 0 => 0
    | 2 => 4 * c
    | _ => c

def square_set : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ, f x = x ^ 2 * c

theorem sub_sq'' {x y : Int} : x ^ 2 + y ^ 2 = (2 * x * y) ↔ x = y := by
  rw [← sub_eq_zero, ← sub_sq', sq_eq_zero_iff, sub_eq_zero]

theorem myInduction
  {motive : ℤ → Prop}
  (P0 : motive 0) (P1 : motive 1) (P2 : motive 2) (P3 : motive 3)
  (add4 : ∀ x, motive (x + 4) = motive x)
  : ∀ x, motive x := by
    -- shifting by any multiple of 4 preserves the motive
    have shift : ∀ (k r : ℤ), motive r → motive (r + 4 * k) := by
      intro k
      induction k using Int.induction_on with
      | zero => intro r h; simpa using h
      | succ i ih =>
          intro r h
          rw [show r + 4 * ((i : ℤ) + 1) = (r + 4 * i) + 4 by ring, add4]
          exact ih r h
      | pred i ih =>
          intro r h
          rw [show r + 4 * (-(i : ℤ) - 1) = (r + 4 * (-(i : ℤ)) - 4) by ring,
              ← add4 (r + 4 * (-(i : ℤ)) - 4),
              show (r + 4 * (-(i : ℤ)) - 4) + 4 = r + 4 * (-(i : ℤ)) by ring]
          exact ih r h
    intro x
    have e : x % 4 + 4 * (x / 4) = x := by lia
    mod_cases h : x % 4 <;> rw [← e, h]
    · exact shift _ _ P0
    · exact shift _ _ P1
    · exact shift _ _ P2
    · exact shift _ _ P3

abbrev solution_set : Set (ℤ → ℤ) := odd_const ∪ mod4_cycle ∪ square_set

end Imo2012P4
