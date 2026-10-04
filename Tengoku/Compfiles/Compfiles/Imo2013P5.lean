/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2013, Problem 5

Let ℚ>₀ be the set of positive rational numbers. Let f: ℚ>₀ → ℝ be a function satisfying
the conditions

  (1) f(x) * f(y) ≥ f(x * y)
  (2) f(x + y)    ≥ f(x) + f(y)

for all x,y ∈ ℚ>₀. Given that f(a) = a for some rational a > 1, prove that f(x) = x for
all x ∈ ℚ>₀.

-/

namespace Imo2013P5

/-
# Solution

We provide a direct translation of the solution found in
https://www.imo-official.org/problems/IMO2013SL.pdf
-/

lemma le_of_all_pow_lt_succ {x y : ℝ} (hx : 1 < x) (hy : 0 < y)
    (h : ∀ n : ℕ, 0 < n → x^n - 1 < y^n) :
    x ≤ y := by
  by_contra! hxy
  -- Compare x against z = max y 1, which satisfies 1 ≤ z < x and y^n ≤ z^n. Since (x/z)^n is
  -- unbounded, some x^n exceeds 2 * z^n ≥ z^n + 1 ≥ y^n + 1, contradicting the hypothesis.
  have hz0 : (0:ℝ) < max y 1 := lt_max_of_lt_right zero_lt_one
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (2:ℝ) < (x / max y 1) ^ n :=
    pow_unbounded_of_one_lt 2 ((one_lt_div hz0).mpr (max_lt hxy hx))
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hn)
  have h_mul : 2 * max y 1 ^ n < x ^ n := by
    rwa [div_pow, lt_div_iff₀ (pow_pos hz0 n)] at hn
  have hyz : y ^ n ≤ max y 1 ^ n := pow_le_pow_left₀ hy.le (le_max_left y 1) n
  have h1z : 1 ≤ max y 1 ^ n := one_le_pow₀ (le_max_right y 1)
  linarith [h n hn0]

lemma f_pos_of_pos {f : ℚ → ℝ} {q : ℚ} (hq : 0 < q)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
    0 < f q := by
  have hfqn := calc f q.num = f (q * q.den) := by rw [← Rat.mul_den_eq_num]
                    _ ≤ f q * f q.den := H1 q q.den hq (Nat.cast_pos.mpr q.pos)

  -- Now we just need to show that `f q.num` and `f q.denom` are positive.
  have num_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hqfn' : (q.num : ℝ) ≤ f q.num := by
    rw [← Int.natAbs_of_nonneg num_pos.le]
    exact H4 q.num.natAbs (Int.natAbs_pos.mpr (ne_of_gt num_pos))

  have f_num_pos : 0 < f q.num :=
    lt_of_lt_of_le (mod_cast num_pos) hqfn'
  have f_den_pos : 0 < f q.den :=
    lt_of_lt_of_le (mod_cast q.pos) (H4 q.den q.pos)
  exact pos_of_mul_pos_left (f_num_pos.trans_le hfqn) f_den_pos.le

lemma fx_gt_xm1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 ≤ x)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
    (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
    (x - 1 : ℝ) < f x := by
  have hx0 :=
    calc (x - 1 : ℝ)
          < ⌊x⌋₊   := mod_cast Nat.sub_one_lt_floor x
        _ ≤ f ⌊x⌋₊ := H4 _ (Nat.floor_pos.2 hx)

  obtain h_eq | h_lt := (Nat.floor_le <| zero_le_one.trans hx).eq_or_lt
  · rwa [h_eq] at hx0
  calc (x - 1 : ℝ) < f ⌊x⌋₊ := hx0
    _ < f (x - ⌊x⌋₊) + f ⌊x⌋₊ := lt_add_of_pos_left _ (f_pos_of_pos (sub_pos.mpr h_lt) H1 H4)
    _ ≤ f (x - ⌊x⌋₊ + ⌊x⌋₊)   := H2 _ _ (sub_pos.mpr h_lt) (Nat.cast_pos.2 (Nat.floor_pos.2 hx))
    _ = f x                   := by rw [sub_add_cancel]

lemma pow_f_le_f_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n) {x : ℚ} (hx : 1 < x)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
    f (x^n) ≤ (f x)^n := by
  have hxp : 0 < x := zero_lt_one.trans hx
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [pow_succ x n, pow_succ (f x) n]
    calc f ((x ^ n) * x)
        ≤ f (x ^ n) * f x := H1 (x ^ n) x (pow_pos hxp n) hxp
      _ ≤ (f x) ^ n * f x := mul_le_mul_of_nonneg_right ih (f_pos_of_pos hxp H1 H4).le

lemma fixed_point_of_pos_nat_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)
    (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x)
    {a : ℚ} (ha1 : 1 < a) (hae : f a = a) :
    f (a^n) = a^n := by
  have hh0 : (a : ℝ) ^ n ≤ f (a ^ n) :=
    mod_cast H5 (a ^ n) (one_lt_pow₀ ha1 hn.ne')

  have hh1 := calc f (a^n) ≤ (f a)^n := pow_f_le_f_pow hn ha1 H1 H4
                   _ = (a : ℝ)^n     := by rw [← hae]
  exact mod_cast hh1.antisymm hh0

lemma fixed_point_of_gt_1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 < x)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
    (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)
    (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x)
    {a : ℚ} (ha1 : 1 < a) (hae : f a = a) :
    f x = x := by
  -- Choose n such that 1 + x < a^n.
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 + x) ha1
  have h_big_enough : (1:ℚ) < a^N - x := lt_sub_iff_add_lt.mpr hN
  have h1 := calc (x : ℝ) + ((a^N - x) : ℚ)
                ≤ f x + ((a^N - x) : ℚ) := add_le_add_left (H5 x hx) _
              _ ≤ f x + f (a^N - x)     := add_le_add_right (H5 _ h_big_enough) _
  have hxp : 0 < x := zero_lt_one.trans hx
  have hNp : 0 < N :=
    Nat.pos_of_ne_zero (by rintro rfl; rw [pow_zero] at hN; linarith)

  have h2 := calc f x + f (a^N - x)
                ≤ f (x + (a^N - x)) := H2 x (a^N - x) hxp (zero_lt_one.trans h_big_enough)
              _ = f (a^N)           := by ring_nf
              _ = (a^N : ℝ)         := fixed_point_of_pos_nat_pow hNp H1 H4 H5 ha1 hae
              _ = (x:ℝ) + ((a^N:ℝ) - (x:ℝ))     := by ring

  have heq := h1.antisymm (mod_cast h2)
  linarith [H5 x hx, H5 _ h_big_enough]

end Imo2013P5
