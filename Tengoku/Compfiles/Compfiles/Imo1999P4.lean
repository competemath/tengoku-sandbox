/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1999, Problem 4

Determine all pairs of positive integers (n,p) such that p is
a prime, n not exceeded 2p, and (p-1)ⁿ + 1 is divisible by of nᵖ⁻¹.
-/

namespace Imo1999P4

lemma exists_least_prime_factor {n : ℕ} (hn : n ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q := by
  use Nat.minFac n, Nat.minFac_prime hn, Nat.minFac_dvd n
  intro q hq hqn
  exact Nat.minFac_le_of_dvd hq.two_le hqn

lemma padicValNat_le_padicValNat_of_dvd {p a b : ℕ} (hb : b ≠ 0) (hp : p.Prime) (hab : a ∣ b) :
    padicValNat p a ≤ padicValNat p b := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  rw [← padicValNat_dvd_iff_le hb]
  apply dvd_trans _ hab
  exact pow_padicValNat_dvd

lemma aux₁ {a p n : ℕ} (hp : p.Prime) (hp' : 2 < p) (hn : 0 < n)
    (hnp : (p - 1).Coprime n) (hpa: p ∣ a ^ n + 1) :
    p ∣ a + 1 := by
  have := Fact.mk hp
  -- Since $p \nmid a$, we have $a^n \equiv -1 \pmod{p}$, which implies that the order of
  -- $a$ modulo $p$ divides $2n$ but not $n$.
  have h_order : orderOf (a : ZMod p) ∣ 2 * n ∧ ¬(orderOf (a : ZMod p) ∣ n) := by
    simp only [orderOf_dvd_iff_pow_eq_one]
    simp_all only [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow,
      Nat.cast_one, pow_mul', sq_eq_one_iff]
    constructor
    · right; exact eq_neg_of_add_eq_zero_left hpa
    · intro h₁
      rw [h₁] at hpa
      rcases p with ( _ | _ | _ | p ) <;> cases hpa <;> contradiction
  -- Since the order of $a$ modulo $p$ divides $2n$ but not $n$, it must divide $2$.
  have h_order_div_2 : orderOf (a : ZMod p) ∣ 2 := by
    -- Since the order of $a$ modulo $p$ divides $2n$ and $\gcd(p-1, n) = 1$, it must divide $2$.
    have h_order_div_2 : orderOf (a : ZMod p) ∣ p - 1 := by
      rw [orderOf_dvd_iff_pow_eq_one, ZMod.pow_card_sub_one_eq_one]
      cases n <;> aesop
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ h_order.1
    exact Nat.Coprime.coprime_dvd_left h_order_div_2 hnp
  rw [← ZMod.natCast_eq_zero_iff]
  simp_all only [orderOf_dvd_iff_pow_eq_one, sq_eq_one_iff]
  aesop

lemma aux₂ {p n: ℕ} (hp : p.Prime) (hpn : ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q) :
    (p - 1).Coprime n := by
  apply Nat.coprime_of_dvd'
  intro p' hp'₁ hp'₂ hp'₃
  exfalso
  have hp'p := hpn p' hp'₁ hp'₃
  have hp' := hp.two_le
  apply Nat.le_of_dvd (by lia) at hp'₂
  lia

abbrev SolutionSet : Set (ℕ × ℕ) := {(2,2), (3,3)} ∪ {(n,p) | n = 1 ∧ p.Prime}

end Imo1999P4
