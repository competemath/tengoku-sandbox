/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 2025, Problem 1

Fix positive integers k and d. Prove that for all sufficiently large odd
positive integers n, the digits of the base-2n representation of n ^ k are
all greater than d.
-/

namespace Usa2025P1

/-- For odd `n` and `1 ≤ ℓ ≤ k`, the residue of `n ^ k` modulo `(2 * n) ^ ℓ`
has the form `c * n ^ ℓ` for an odd `c` (so in particular `1 ≤ c`).
In other words, the `ℓ` rightmost base-`(2 * n)` digits of `n ^ k` are the
base-`(2 * n)` digits of `c * n ^ ℓ`. -/
lemma residue_mod {n k ℓ : ℕ} (hodd : Odd n) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    ∃ c : ℕ, Odd c ∧ 1 ≤ c ∧ n ^ k % (2 * n) ^ ℓ = c * n ^ ℓ := by
  have hn0 : 0 < n := hodd.pos
  have hc_odd : Odd (n ^ (k - ℓ) % 2 ^ ℓ) := by
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by lia : ℓ ≠ 0))]
    exact Nat.odd_iff.mp hodd.pow
  refine ⟨n ^ (k - ℓ) % 2 ^ ℓ, hc_odd, hc_odd.pos, ?_⟩
  have hdvd : (2 * n) ^ ℓ ∣ n ^ k - (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ := by
    rw [mul_pow]
    have h1 : 2 ^ ℓ * n ^ ℓ ∣ (n ^ (k - ℓ) - n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ :=
      mul_dvd_mul_right (Nat.dvd_sub_mod _) _
    have h2 : (n ^ (k - ℓ) - n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ
        = n ^ k - (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ := by
      rw [Nat.sub_mul, ← pow_add, Nat.sub_add_cancel hℓk]
    rwa [h2] at h1
  obtain ⟨q, hq⟩ := hdvd
  have hle : (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ ≤ n ^ k := by
    calc (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ ≤ n ^ (k - ℓ) * n ^ ℓ :=
        Nat.mul_le_mul (Nat.mod_le _ _) le_rfl
      _ = n ^ k := by rw [← pow_add, Nat.sub_add_cancel hℓk]
  have hlt : (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ < (2 * n) ^ ℓ := by
    rw [mul_pow]
    exact mul_lt_mul_of_pos_right
      (Nat.mod_lt _ (Nat.pow_pos (by lia : (0 : ℕ) < 2))) (Nat.pow_pos hn0)
  have hnk : n ^ k = (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ + (2 * n) ^ ℓ * q := by
    rw [← hq]
    exact (Nat.add_sub_cancel' hle).symm
  rw [hnk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The `i`-th base-`b` digit of `m` (counting from the right, starting at `0`)
equals `E / b ^ i`, where `E = m % b ^ (i + 1)` is the residue of `m` modulo
the next power of `b`. -/
lemma digit_of_mod {m b E i : ℕ} (hb : 1 < b) (hm : m % b ^ (i + 1) = E) :
    m / b ^ i % b = E / b ^ i := by
  have hb0 : 0 < b := by lia
  have hE : E < b ^ (i + 1) := by
    rw [← hm]
    exact Nat.mod_lt _ (Nat.pow_pos hb0)
  have hbl : b ^ (i + 1) = b ^ i * b := pow_succ b i
  have hE' : E < b ^ i * b := by rwa [hbl] at hE
  have h := Nat.div_add_mod m (b ^ (i + 1))
  rw [hm] at h
  set q := m / b ^ (i + 1) with hq_def
  -- h : b ^ (i + 1) * q + E = m
  have hm' : m = E + b ^ i * (b * q) := by
    rw [← h, hbl]
    ring
  have hdiv : m / b ^ i = E / b ^ i + b * q := by
    rw [hm']
    exact Nat.add_mul_div_left _ _ (Nat.pow_pos hb0)
  rw [hdiv, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hE')

end Usa2025P1
