/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1984, Problem 6

Let a, b, c, and d be odd integers such that 0 < a < b < c < d and ad = bc.
Prove that if a + d = 2ᵏ and b + c = 2ᵐ for some integers k and m, then
a = 1.
-/

namespace Imo1984P6

/-- If `2^m` divides `(y - x) * (y + x)` for odd `x < y`, then almost all of
the factors of 2 land in one of the two factors, since
`gcd (y - x) (y + x) = 2`. -/
lemma two_pow_dvd_or {x y m : ℕ} (hx : Odd x) (hy : Odd y) (hxy : x < y)
    (hdvd : 2 ^ m ∣ (y - x) * (y + x)) :
    2 ^ (m - 1) ∣ y - x ∨ 2 ^ (m - 1) ∣ y + x := by
  obtain hm | hm : m ≤ 1 ∨ 2 ≤ m := by lia
  · -- for m ≤ 1 the claim is trivial, since then 2 ^ (m - 1) = 1
    left
    have h0 : m - 1 = 0 := by lia
    rw [h0, pow_zero]
    exact one_dvd _
  obtain ⟨u, hu⟩ := Nat.Odd.sub_odd hy hx
  obtain ⟨v, hv⟩ := Odd.add_odd hy hx
  obtain ⟨t, ht⟩ := hdvd
  -- u * v = 2 ^ (m - 2) * t, and u + v = y is odd
  have h4 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show m = 2 + (m - 2) by lia, pow_add]
    norm_num
  have h44 : 4 * (u * v) = 4 * (2 ^ (m - 2) * t) := by
    rw [show 4 * (2 ^ (m - 2) * t) = (4 * 2 ^ (m - 2)) * t by ring, ← h4, ← ht]
    rw [hu, hv]
    ring
  have huv : u * v = 2 ^ (m - 2) * t := Nat.eq_of_mul_eq_mul_left (by norm_num) h44
  have hy2 := Nat.odd_iff.mp hy
  have hm1 : m - 1 = (m - 2) + 1 := by lia
  obtain hu2 | hu2 := Nat.even_or_odd u
  · -- u even forces v odd, so 2^(m-2) ∣ u and hence 2^(m-1) ∣ y - x
    have hv2 : Odd v := by
      rw [Nat.odd_iff]
      have h1 := Nat.even_iff.mp hu2
      lia
    have hco : Nat.Coprime (2 ^ (m - 2)) v :=
      Nat.Coprime.pow_left _ hv2.coprime_two_left
    obtain ⟨s, hs⟩ := hco.dvd_of_dvd_mul_right ⟨t, huv⟩
    exact Or.inl ⟨s, by rw [hu, hs, hm1, pow_succ]; ring⟩
  · -- u odd, so 2^(m-2) ∣ v and hence 2^(m-1) ∣ y + x
    have hco : Nat.Coprime (2 ^ (m - 2)) u :=
      Nat.Coprime.pow_left _ hu2.coprime_two_left
    obtain ⟨s, hs⟩ := hco.dvd_of_dvd_mul_left ⟨t, huv⟩
    exact Or.inr ⟨s, by rw [hv, hs, hm1, pow_succ]; ring⟩

end Imo1984P6
