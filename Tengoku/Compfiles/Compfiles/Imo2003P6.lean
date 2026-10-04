/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Zhiyi Luo
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2003, Problem 6

Let p be a prime number. Prove that there exists a prime number q
such that for every integer n, the number nᵖ - p is not divisible
by q.
-/

namespace Imo2003P6

lemma exists_prime_mod_m_ne_1_and_dvd
    {n m : Nat} (npos : n ≠ 0) (hn : n % m ≠ 1) (hm : m ≠ 1)
    : ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % m ≠ 1 := by
  by_contra! h
  let l := n.primeFactorsList
  have : ∀ p ∈ l, p % m = 1 := by
    intro p pl
    exact h _ (Nat.prime_of_mem_primeFactorsList pl) (Nat.dvd_of_mem_primeFactorsList pl)
  have : n % m = 1 := calc n % m
    _ = l.prod % m := by rw [Nat.prod_primeFactorsList npos]
    _ = (l.map (fun p ↦ p % m)).prod % m := List.prod_nat_mod l m
    _ = (l.map (fun p ↦ 1)).prod % m := by rw [List.map_inj_left.mpr this]
    _ = 1 % m := by rw [List.prod_eq_one (by simp)]
    _ = 1 := Nat.one_mod_eq_one.mpr hm
  contradiction

end Imo2003P6
