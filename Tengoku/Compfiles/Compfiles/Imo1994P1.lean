/-
Copyright (c) 2021 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathmatical Olympiad 1994, Problem 1

Let `m` and `n` be two positive integers.
Let `a₁, a₂, ..., aₘ` be `m` different numbers from the set `{1, 2, ..., n}`
such that for any two indices `i` and `j` with `1 ≤ i ≤ j ≤ m` and `aᵢ + aⱼ ≤ n`,
there exists an index `k` such that `aᵢ + aⱼ = aₖ`.
Show that `(a₁+a₂+...+aₘ)/m ≥ (n+1)/2`
-/

open Finset

namespace Imo1994P1

/-
# Sketch of solution

We can order the numbers so that `a₁ ≤ a₂ ≤ ... ≤ aₘ`.
The key idea is to pair the numbers in the sum and show that `aᵢ + aₘ₊₁₋ᵢ ≥ n+1`.
Indeed, if we had `aᵢ + aₘ₊₁₋ᵢ ≤ n`, then `a₁ + aₘ₊₁₋ᵢ, a₂ + aₘ₊₁₋ᵢ, ..., aᵢ + aₘ₊₁₋ᵢ`
would be `m` elements of the set of `aᵢ`'s all larger than `aₘ₊₁₋ᵢ`, which is impossible.
-/

theorem tedious (m : ℕ) (k : Fin (m + 1)) : m - ((m + 1 - ↑k) + m) % (m + 1) = ↑k := by
  obtain ⟨k, hk⟩ := k
  rw [Nat.lt_succ_iff, le_iff_exists_add] at hk
  rcases hk with ⟨c, rfl⟩
  have : (k + c + 1 - k) + (k + c) = c + (k + c + 1) := by lia
  rw [Fin.val_mk, this, Nat.add_mod_right, Nat.mod_eq_of_lt, Nat.add_sub_cancel]
  lia

end Imo1994P1
