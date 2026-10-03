/-
Copyright (c) 2023 David Renshaw. All rights reserved.
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
# USA Mathematical Olympiad 2003, Problem 1

Prove that for every positive integer n there exists an n-digit
number divisible by 5ⁿ, all of whose digits are odd.
-/

namespace Usa2003P1

lemma nat_mod_inv (a : ℕ) : ∃ b, (a + b) % 5 = 0 := ⟨5 - (a % 5), by lia⟩

lemma lemma2 (a b c : ℕ) (hb : 0 < b) (h : Nat.Coprime a b) : ∃ k, k < b ∧ a * k ≡ c [MOD b] := by
  let ⟨N, HN1, HN2⟩ := Nat.chineseRemainder h 0 c
  have ⟨x, hx⟩ : a ∣ N := Nat.modEq_zero_iff_dvd.mp HN1
  use x % b
  constructor
  · exact Nat.mod_lt _ hb
  · change N % b = c % b at HN2
    change (a * (x % b)) % b = c % b
    rw [← HN2, hx, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

end Usa2003P1
