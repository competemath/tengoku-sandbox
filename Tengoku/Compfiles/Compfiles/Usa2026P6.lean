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
# USA Mathematical Olympiad 2026, Problem 6

Let a and b be positive integers such that φ(ab + 1) divides a² + b² + 1.
Prove that a and b are Fibonacci numbers.
-/

namespace Usa2026P6

/-
Mathematical solution sketch by Evan Chen:
https://web.evanchen.cc/exams/USAMO-2026-notes.pdf

* A parity argument shows `ab + 1` must be a prime power `p^e`.
* If `e = 1`, then `ab ∣ a² + b² + 1` and a Vieta jumping argument shows that
  `{a, b} = {F_{2k-1}, F_{2k+1}}`.
* If `e ≥ 2`, write `ab = p^e - 1`; reducing `a² + b² + 1 ≡ 0` mod `p^(e-1)`
  gives `p^(e-1) ∣ (a² + a + 1)(a² - a + 1)`, and the two factors are coprime.
  Since `x² ± x + 1` has a root mod `p` only when `p = 3` or `p ≡ 1 (mod 3)`,
  and `p ≡ 1 (mod 3)` contradicts `3 ∣ a² + b² + 1` (which forces `3 ∤ ab`),
  we must have `p = 3`. Since `9 ∤ x² ± x + 1`, we get `e = 2`, so `ab = 8`,
  and only `(a, b) = (1, 8)` works.
-/

/-- The classification of solutions of `a^2 + b^2 + 1 = 3 * a * b`:
either `a = b = 1`, or `{a, b} = {F_{2k-1}, F_{2k+1}}` for some `k ≥ 1`. -/
def FibPair (a b : ℕ) : Prop :=
  (a = 1 ∧ b = 1) ∨
    ∃ k : ℕ, 1 ≤ k ∧
      ((a = Nat.fib (2 * k - 1) ∧ b = Nat.fib (2 * k + 1)) ∨
        (a = Nat.fib (2 * k + 1) ∧ b = Nat.fib (2 * k - 1)))

/-- Vieta jumping step: if `a * b ∣ a^2 + b^2 + 1` with `0 < a ≤ b`, then the quotient
equals `3`. Strong induction on the sum (the induction hypothesis is passed explicitly). -/
lemma quotient_eq_three_aux {s : ℕ}
    (IH : ∀ t : ℕ, t < s → ∀ a b : ℕ, a + b = t → 0 < a → 0 < b →
      a * b ∣ a ^ 2 + b ^ 2 + 1 → (a ^ 2 + b ^ 2 + 1) / (a * b) = 3)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b = s) (hle : a ≤ b)
    (hdvd : a * b ∣ a ^ 2 + b ^ 2 + 1) : (a ^ 2 + b ^ 2 + 1) / (a * b) = 3 := by
  obtain ⟨k, hk⟩ := hdvd
  have hkq : (a ^ 2 + b ^ 2 + 1) / (a * b) = k := by
    rw [hk, Nat.mul_div_right _ (mul_pos ha hb)]
  rw [hkq]
  -- the other Vieta root `b' = k * a - b`
  have hbk : b ≤ k * a := by
    have h1 : b * b ≤ a * b * k := by
      have h2 : b * b ≤ a ^ 2 + b ^ 2 + 1 := by nlinarith [sq_nonneg a]
      rwa [hk] at h2
    have h3 : b * b ≤ b * (k * a) := by
      convert h1 using 1
      ring
    exact le_of_mul_le_mul_left h3 hb
  have hbb' : b * (k * a - b) = a ^ 2 + 1 := by
    rw [Nat.mul_sub_left_distrib]
    have h2 : b * (k * a) = a * b * k := by ring
    rw [h2, ← hk, pow_two b]
    lia
  have hb'pos : 0 < k * a - b := by
    rcases Nat.eq_zero_or_pos (k * a - b) with h0 | hpos
    · rw [h0, mul_zero] at hbb'
      lia
    · exact hpos
  -- the descended pair `(a, b')` satisfies the same equation with the same `k`
  have hveq : a ^ 2 + (k * a - b) ^ 2 + 1 = a * (k * a - b) * k := by
    have hbb : k * a - b + b = k * a := Nat.sub_add_cancel hbk
    have h1 : a ^ 2 + (k * a - b) ^ 2 + 1 =
        b * (k * a - b) + (k * a - b) * (k * a - b) := by
      rw [pow_two (k * a - b)]
      lia
    rw [h1]
    calc b * (k * a - b) + (k * a - b) * (k * a - b)
        = (k * a - b) * (b + (k * a - b)) := by ring
      _ = (k * a - b) * (k * a) := by rw [add_comm b (k * a - b), hbb]
      _ = a * (k * a - b) * k := by ring
  rcases le_or_gt b (k * a - b) with hcase | hcase
  · -- `b ≤ b'` forces `a = b = 1` and `k = 3`
    have h1 : b * b ≤ a ^ 2 + 1 := by
      have h2 : b * b ≤ b * (k * a - b) := Nat.mul_le_mul_left b hcase
      rwa [hbb'] at h2
    have hab_eq : a = b := by
      by_contra hne
      have hlt : a < b := lt_of_le_of_ne hle hne
      have h3 : (a + 1) * (a + 1) ≤ b * b := Nat.mul_le_mul hlt hlt
      nlinarith [h1, h3, ha]
    subst hab_eq
    have hdv1 : a * a ∣ 1 := by
      have haa : a * a ∣ 2 * (a * a) + 1 := by
        refine ⟨k, ?_⟩
        rw [pow_two a] at hk
        lia
      have hd2 : a * a ∣ 2 * (a * a) := dvd_mul_left (a * a) 2
      exact (Nat.dvd_add_iff_right hd2).mpr haa
    have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right (Nat.dvd_one.mp hdv1)
    subst ha1
    lia
  · -- `b' < b`: descend and use the induction hypothesis
    have hsum' : a + (k * a - b) < s := by rw [← hsum]; lia
    have hIH := IH (a + (k * a - b)) hsum' a (k * a - b) rfl ha hb'pos ⟨k, hveq⟩
    have hkq2 : (a ^ 2 + (k * a - b) ^ 2 + 1) / (a * (k * a - b)) = k := by
      rw [hveq, Nat.mul_div_right _ (mul_pos ha hb'pos)]
    lia

/-- If `a * b ∣ a^2 + b^2 + 1` for positive naturals `a, b`, then the quotient is `3`. -/
lemma quotient_eq_three {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hdvd : a * b ∣ a ^ 2 + b ^ 2 + 1) : (a ^ 2 + b ^ 2 + 1) / (a * b) = 3 := by
  have key : ∀ s : ℕ, ∀ a b : ℕ, a + b = s → 0 < a → 0 < b →
      a * b ∣ a ^ 2 + b ^ 2 + 1 → (a ^ 2 + b ^ 2 + 1) / (a * b) = 3 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s IH =>
      intro a b hsum ha hb hdvd
      rcases le_or_gt a b with hle | hlt
      · exact quotient_eq_three_aux IH ha hb hsum hle hdvd
      · have hdvd' : b * a ∣ b ^ 2 + a ^ 2 + 1 := by
          rw [mul_comm b a, add_comm (b ^ 2) (a ^ 2)]
          exact hdvd
        have h := quotient_eq_three_aux IH hb ha (by lia) (le_of_lt hlt) hdvd'
        rwa [mul_comm b a, add_comm (b ^ 2) (a ^ 2)] at h
  exact key (a + b) a b rfl ha hb hdvd

/-- The Fibonacci recurrence over four steps: `F_{n+4} + F_n = 3 * F_{n+2}`. -/
lemma fib_add_four (n : ℕ) : Nat.fib (n + 4) + Nat.fib n = 3 * Nat.fib (n + 2) := by
  have h1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    have h := @Nat.fib_add_two (n + 2)
    rwa [show n + 2 + 2 = n + 4 by lia, show n + 2 + 1 = n + 3 by lia] at h
  have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    have h := @Nat.fib_add_two (n + 1)
    rwa [show n + 1 + 2 = n + 3 by lia, show n + 1 + 1 = n + 2 by lia] at h
  have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  lia

/-- Vieta jumping for the equation `a^2 + b^2 + 1 = 3 * a * b` with `0 < a ≤ b`:
the pair is a `FibPair`. -/
lemma fib_pair_aux {s : ℕ}
    (IH : ∀ t : ℕ, t < s → ∀ a b : ℕ, a + b = t → 0 < a → 0 < b →
      a ^ 2 + b ^ 2 + 1 = 3 * a * b → FibPair a b)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b = s) (hle : a ≤ b)
    (h : a ^ 2 + b ^ 2 + 1 = 3 * a * b) : FibPair a b := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- `a = b` gives `a = b = 1`
    subst heq
    left
    have h1 : a * a = 1 := by
      have h2 : a * a + a * a + 1 = 3 * (a * a) := by
        rw [← mul_assoc 3 a a, ← h, pow_two a]
      lia
    have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right h1
    exact ⟨ha1, ha1⟩
  · -- `a < b`: jump down to `(b', a)` with `b' = 3a - b ≤ a`
    have hbk : b ≤ 3 * a := by
      have h1 : b * b ≤ b * (3 * a) := by
        have h2 : b * b ≤ 3 * a * b := by
          have h3 : b * b ≤ a ^ 2 + b ^ 2 + 1 := by nlinarith [sq_nonneg a]
          rwa [h] at h3
        convert h2 using 1
        ring
      exact le_of_mul_le_mul_left h1 hb
    have hbb' : b * (3 * a - b) = a ^ 2 + 1 := by
      rw [Nat.mul_sub_left_distrib]
      have h2 : b * (3 * a) = 3 * a * b := by ring
      rw [h2, ← h, pow_two b]
      lia
    have hb'pos : 0 < 3 * a - b := by
      rcases Nat.eq_zero_or_pos (3 * a - b) with h0 | hpos
      · rw [h0, mul_zero] at hbb'
        lia
      · exact hpos
    have hb'le : 3 * a - b ≤ a := by
      by_contra hcon
      push Not at hcon
      have h1 : (a + 1) * (a + 1) ≤ b * (3 * a - b) := Nat.mul_le_mul hlt hcon
      rw [hbb'] at h1
      nlinarith [h1, ha]
    have hbb : 3 * a - b + b = 3 * a := Nat.sub_add_cancel hbk
    have hveq : a ^ 2 + (3 * a - b) ^ 2 + 1 = 3 * a * (3 * a - b) := by
      have h1 : a ^ 2 + (3 * a - b) ^ 2 + 1 =
          b * (3 * a - b) + (3 * a - b) * (3 * a - b) := by
        rw [pow_two (3 * a - b)]
        lia
      rw [h1]
      calc b * (3 * a - b) + (3 * a - b) * (3 * a - b)
          = (3 * a - b) * (b + (3 * a - b)) := by ring
        _ = (3 * a - b) * (3 * a) := by rw [add_comm b (3 * a - b), hbb]
        _ = 3 * a * (3 * a - b) := by ring
    have hsum' : (3 * a - b) + a < s := by rw [← hsum]; lia
    have hIH := IH ((3 * a - b) + a) hsum' (3 * a - b) a rfl hb'pos ha (by
      rw [add_comm ((3 * a - b) ^ 2) (a ^ 2), hveq]; ring)
    rcases hIH with h11 | ⟨k, hk1, hcase⟩
    · -- `b' = 1`, `a = 1`, so `b = 2 = F_3`
      obtain ⟨hb'1, ha1⟩ := h11
      have hb2 : b = 2 := by lia
      right
      refine ⟨1, le_rfl, Or.inl ⟨ha1, ?_⟩⟩
      show b = Nat.fib (2 * 1 + 1)
      rw [hb2]
      decide
    · rcases hcase with ⟨hb'e, hae⟩ | ⟨hb'e, hae⟩
      · -- `b' = F_{2k-1}`, `a = F_{2k+1}`: then `b = 3a - b' = F_{2k+3}`
        have hfb := fib_add_four (2 * k - 1)
        rw [show 2 * k - 1 + 4 = 2 * k + 3 by lia,
          show 2 * k - 1 + 2 = 2 * k + 1 by lia] at hfb
        have hb_eq : b = Nat.fib (2 * k + 3) := by lia
        right
        refine ⟨k + 1, by lia, Or.inl ⟨?_, ?_⟩⟩
        · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by lia]
          exact hae
        · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by lia]
          exact hb_eq
      · -- `b' = F_{2k+1}`, `a = F_{2k-1}` contradicts `b' ≤ a`
        exfalso
        have h1 : Nat.fib (2 * k + 1) = Nat.fib (2 * k - 1) + Nat.fib (2 * k) := by
          have h2 := @Nat.fib_add_two (2 * k - 1)
          rwa [show 2 * k - 1 + 2 = 2 * k + 1 by lia,
            show 2 * k - 1 + 1 = 2 * k by lia] at h2
        have hpos : 0 < Nat.fib (2 * k) := Nat.fib_pos.mpr (by lia)
        lia

/-- The solutions of `a^2 + b^2 + 1 = 3 * a * b` in positive integers are exactly
the pairs `{F_{2k-1}, F_{2k+1}}` (and `(1, 1)`). -/
lemma fib_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 + b ^ 2 + 1 = 3 * a * b) : FibPair a b := by
  have key : ∀ s : ℕ, ∀ a b : ℕ, a + b = s → 0 < a → 0 < b →
      a ^ 2 + b ^ 2 + 1 = 3 * a * b → FibPair a b := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s IH =>
      intro a b hsum ha hb h
      rcases le_or_gt a b with hle | hlt
      · exact fib_pair_aux IH ha hb hsum hle h
      · have h' : b ^ 2 + a ^ 2 + 1 = 3 * b * a := by
          rw [add_comm (b ^ 2) (a ^ 2), h]
          ring
        have h2 := fib_pair_aux IH hb ha (by lia) (le_of_lt hlt) h'
        rcases h2 with h11 | ⟨k, hk1, hcase⟩
        · exact Or.inl ⟨h11.2, h11.1⟩
        · right
          refine ⟨k, hk1, ?_⟩
          rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact Or.inl ⟨h2, h1⟩
  exact key (a + b) a b rfl ha hb h

/-- Every entry of a `FibPair` is a Fibonacci number. -/
lemma fibPair_fib {a b : ℕ} (h : FibPair a b) :
    (∃ m, a = Nat.fib m) ∧ (∃ n, b = Nat.fib n) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨k, _, hcase⟩
  · exact ⟨⟨1, Nat.fib_one.symm⟩, ⟨1, Nat.fib_one.symm⟩⟩
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨2 * k - 1, h1⟩, ⟨2 * k + 1, h2⟩⟩
    · exact ⟨⟨2 * k + 1, h1⟩, ⟨2 * k - 1, h2⟩⟩

/-- Parity helper: a square has the same parity as its root. -/
lemma sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  rw [pow_two, Nat.mul_mod]
  have hx : x % 2 < 2 := Nat.mod_lt x two_pos
  interval_cases h : x % 2 <;> rfl

/-- Odd squares are `1 mod 4`. -/
lemma sq_mod_four_of_odd {x : ℕ} (hx : x % 2 = 1) : x ^ 2 % 4 = 1 := by
  have hx4 : x % 4 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)]
    exact hx
  have hlt : x % 4 < 4 := Nat.mod_lt x (by decide)
  rw [pow_two, Nat.mul_mod]
  interval_cases h : x % 4
  · simp at hx4
  · rfl
  · simp at hx4
  · rfl

/-- Even squares are `0 mod 4`. -/
lemma sq_mod_four_of_even {x : ℕ} (hx : x % 2 = 0) : x ^ 2 % 4 = 0 := by
  have hx4 : x % 4 % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)]
    exact hx
  have hlt : x % 4 < 4 := Nat.mod_lt x (by decide)
  rw [pow_two, Nat.mul_mod]
  interval_cases h : x % 4
  · rfl
  · simp at hx4
  · rfl
  · simp at hx4

end Usa2026P6
