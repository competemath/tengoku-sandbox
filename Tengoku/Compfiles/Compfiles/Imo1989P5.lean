/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1989, Problem 5

Prove that for each positive integer n there exist n consecutive positive
integers, none of which is an integral power of a prime number.
-/

namespace Imo1989P5

structure ChinesePair where
  modulus : ℕ
  remainder : ℕ

lemma general_chinese_remainder (xs : List ChinesePair)
    (x_coprime : xs.Pairwise (fun x y ↦ Nat.Coprime x.modulus y.modulus)) :
    ∃ m : ℕ, ∀ x ∈ xs, m ≡ x.remainder [MOD x.modulus] := by
  induction xs with
  | nil => use 0; decide
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := ih x_coprime.tail
    clear ih
    -- then we use Nat.chineseRemainder on x and ⟨List.prod(xs.map modulus), b⟩
    rw [List.pairwise_cons] at x_coprime
    -- need that `Nat.Coprime x.modulus y`
    have h1 := (Nat.coprime_list_prod_right_iff
                   (k := x.modulus) (l := xs.map (·.modulus))).mpr
                   (by intro z hz; aesop)
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h1 x.remainder b
    use k
    intro z hz
    cases hz with
    | head => exact hk1
    | tail w hw =>
      have h2 := hb z hw
      have h4 := Nat.ModEq.of_dvd (List.dvd_prod (List.mem_map_of_mem hw)) hk2
      exact h4.trans h2

lemma list_upper_bound (l : List ℕ) : ∃ m : ℕ, ∀ x ∈ l, x ≤ m := by
  use List.foldr max ⊥ l
  intro a ha
  exact List.le_max_of_le ha (le_refl _)

theorem get_primes (n m : ℕ) :
    ∃ lst : List ℕ, lst.length = n ∧ lst.Nodup ∧
               ∀ x ∈ lst, x.Prime ∧ m ≤ x := by
  induction n with
  | zero => use ∅; simp
  | succ n ih =>
    obtain ⟨l', hl', hlnd, hlp⟩ := ih
    obtain ⟨mx, hmx⟩ := list_upper_bound l'
    obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes (max m (mx + 1))
    use p :: l'
    constructor
    · exact Iff.mpr Nat.succ_inj hl'
    · constructor
      · rw [List.nodup_cons]
        constructor
        · intro hpl
          exact Iff.mpr Nat.not_le (le_of_max_le_right hpm) (hmx p hpl)
        · exact hlnd
      · aesop

lemma not_prime_power_of_two_factors
     {n p q : ℕ}
     (hp : Nat.Prime p) (hq : Nat.Prime q)
     (hpq : p ≠ q)
     (hpn : p ∣ n) (hqn : q ∣ n) : ¬IsPrimePow n := by
   intro hpp
   have h0 : n ≠ 0 := IsPrimePow.ne_zero hpp
   obtain ⟨r, k, hr, hk, hrk⟩ := hpp
   rw [← Nat.prime_iff] at hr
   rw [← hrk] at hqn hpn h0; clear hrk
   have h1 := (Nat.mem_primeFactorsList h0).mpr ⟨hp, hpn⟩
   rw [Nat.Prime.primeFactorsList_pow hr] at h1
   have h3 := (List.mem_replicate.mp h1).2
   have h2 := (Nat.mem_primeFactorsList h0).mpr ⟨hq, hqn⟩
   rw [Nat.Prime.primeFactorsList_pow hr] at h2
   have h4 := (List.mem_replicate.mp h2).2
   rw [h3, h4] at hpq
   exact hpq rfl

lemma lemma1 {p1 p2 q : ℕ}
    (hp1 : Nat.Prime p1)
    (hp2 : Nat.Prime p2)
    (hq : Nat.Prime q)
    (hp1q : p1 ≠ q)
    (hp2q : p2 ≠ q) :
    Nat.Coprime (p1 * p2) q := by
  have h1 : Nat.Coprime p1 q := Iff.mpr (Nat.coprime_primes hp1 hq) hp1q
  have h2 : Nat.Coprime p2 q := Iff.mpr (Nat.coprime_primes hp2 hq) hp2q
  exact Nat.Coprime.mul_left h1 h2

lemma lemma2 {p1 q1 p2 q2 : ℕ}
    (hp1 : Nat.Prime p1)
    (hq1 : Nat.Prime q1)
    (hp2 : Nat.Prime p2)
    (hq2 : Nat.Prime q2)
    (hp1q1 : p1 ≠ q1)
    (hp1q2 : p1 ≠ q2)
    (hp2q1 : p2 ≠ q1)
    (hp2q2 : p2 ≠ q2) :
    Nat.Coprime (p1 * p2) (q1 * q2) := by
  have h1 := lemma1 hp1 hp2 hq1 hp1q1 hp2q1
  have h2 := lemma1 hp1 hp2 hq2 hp1q2 hp2q2
  exact Nat.Coprime.mul_right h1 h2

lemma lemma3 {α : Type} (l : List α)
    (hl : List.Nodup l)
    {i j : Fin l.length}
    (hij : i ≠ j)
    : l.get i ≠ l.get j := by
  intro hij'
  --TODO why do neither aesop nor library_search succeed here?
  exact hij (List.nodup_iff_injective_get.mp hl hij')

end Imo1989P5
