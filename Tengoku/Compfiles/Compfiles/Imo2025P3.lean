/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg (Problem statement) , Shahar Blumentzvaig
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2025, Problem 3

Let N denote the set of positive integers.

A function f : N → N is said to be bonza if f(a) divides b ^ a − f(b) ^ f(a) for
all positive integers a and b.

Determine the smallest real constant c such that f(n) ⩽ cn for all bonza functions f
and all positive integers n.
-/
open Int

lemma fermat_little_theorem: ∀p:ℕ+, (Nat.Prime (p:ℕ)) → (∀a:ℕ, (a^(p:ℕ)≡a [MOD p])) := by
  intro p hp a
  by_cases h1:(p:ℕ)∣a
  · rw [← Nat.modEq_zero_iff_dvd] at h1
    have h2: a ^ (p:ℕ) ≡ 0 ^ (p:ℕ) [MOD p] := by
      exact Nat.ModEq.pow (p:ℕ) h1
    simp at h2
    apply Nat.ModEq.symm at h1
    exact Nat.ModEq.trans h2 h1
  · have h2 : (p:ℕ).Coprime a := (Nat.Prime.coprime_iff_not_dvd hp).mpr h1
    apply Nat.Coprime.symm at h2
    have h3 := Nat.ModEq.pow_totient h2
    rw [Nat.totient_prime hp] at h3
    have h4 : a≡a [MOD p] := Nat.ModEq.rfl
    have h5 := Nat.ModEq.mul h3 h4
    simp at h5
    exact h5

lemma fermat_little_theorem2: ∀p:ℕ+, (Nat.Prime (p:ℕ)) → (∀a:ℕ, ∀k:ℕ, (a^((p:ℕ)^k)≡a [MOD p])) := by
  intro p hp a k
  induction k with
  | zero =>
    simp
    rfl
  | succ d hd =>
    rw [Nat.pow_add,Nat.mul_comm,Nat.pow_mul]
    simp
    have g1 := fermat_little_theorem p hp a
    have g2 := Nat.ModEq.pow ((p:ℕ) ^ d) g1
    exact Nat.ModEq.trans g2 hd

lemma int_dvd_to_nat_dvd : ∀a:ℕ+, ∀ b:ℕ , (a:ℤ)∣(b:ℤ) → (a:ℕ)∣b := by
  intro a b h1
  exact ofNat_dvd.mp h1

def Bonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+,
    (f a : Int) ∣ ((b : Int) ^ (a: ℕ) - (f b : Int) ^ ((f a): ℕ))

def is_valid_c (c : ℝ) : Prop :=
  ∀ (f : ℕ+ → ℕ+), Bonza f → ∀ n, (f n : ℝ) ≤ c * (n : ℝ)

abbrev answer : ℝ := 4
