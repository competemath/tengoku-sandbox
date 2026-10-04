/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azhdarov
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2014, Problem 2

Let ℤ be the set of integers. Find all functions f : ℤ → ℤ such that
x * f(2 * f(y) - x) + y ^ 2 * f(2 * x - f(y)) = (f(x) ^ 2) / x + f(y * f(y))
for all x, y ∈ ℤ with x ≠ 0.
-/

namespace Usa2014P2

def P (f : ℤ → ℤ) :=
    ∀ x y, x ≠ 0 → x * f (2 * f y - x) + y ^ 2 * f (2 * x - f y) = (f x ^ 2 : ℚ) / x + f (y * f y)

abbrev S : Set (ℤ → ℤ) := {0, fun x ↦ x ^ 2}

lemma mpr {f : ℤ → ℤ} : f ∈ S → P f := by
  intro h x y hx
  rcases h with rfl | rfl
  · simp
  · grind

lemma exists_prime_and_not_dvd {n : ℤ} (hn : n ≠ 0) : ∃ p, Prime p ∧ ¬ p ∣ n := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  refine ⟨p, Nat.prime_iff_prime_int.mp hp2, ?_⟩
  rw [Nat.succ_le_iff] at hp1
  intro hpn
  rw [← Int.dvd_natAbs, Int.ofNat_dvd] at hpn
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hn) at hpn
  lia

end Usa2014P2
