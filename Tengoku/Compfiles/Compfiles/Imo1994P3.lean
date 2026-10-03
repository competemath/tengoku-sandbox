/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
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
# International Mathematical Olympiad 1994, Problem 3

For any positive integer k, let f(k) be the number of elements in the set
{k+1, k+2, ... , 2k} which have exactly three 1s when written in base 2.
Prove that for each positive integer m, there is at least one k with f(k) = m,
and determine all m for which there is exactly one k.
-/

namespace Imo1994P3

/-- The number of `1`s in the binary representation of `n`. -/
def ones (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The function `f` of the problem: the number of elements of `{k+1, ..., 2k}`
whose binary representation has exactly three `1`s. -/
def f (k : ℕ) : ℕ := ((Finset.Icc (k + 1) (2 * k)).filter fun n => ones n = 3).card

abbrev answer : Set ℕ := {m | ∃ n : ℕ, 2 ≤ n ∧ m = Nat.choose n 2 + 1}

/-! ## Basic properties of `ones` -/

lemma ones_zero : ones 0 = 0 := by rw [ones, Nat.digits_zero, List.sum_nil]

lemma ones_two_mul (n : ℕ) : ones (2 * n) = ones n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have h := Nat.digits_add 2 (by norm_num) 0 n (by norm_num) (Or.inr hn.ne')
    rw [zero_add] at h
    simp only [ones]
    rw [h, List.sum_cons, zero_add]

lemma ones_two_mul_add_one (n : ℕ) : ones (2 * n + 1) = ones n + 1 := by
  have h := Nat.digits_add 2 (by norm_num) 1 n (by norm_num) (Or.inl one_ne_zero)
  simp only [ones]
  rw [show 2 * n + 1 = 1 + 2 * n by lia, h, List.sum_cons]
  lia

lemma ones_one : ones 1 = 1 := by
  show ones (2 * 0 + 1) = 1
  rw [ones_two_mul_add_one, ones_zero]

lemma ones_two : ones 2 = 1 := by
  show ones (2 * 1) = 1
  rw [ones_two_mul, ones_one]

lemma ones_two_mul_pow (i : ℕ) (x : ℕ) : ones (2 ^ i * x) = ones x := by
  induction i with
  | zero => rw [pow_zero, one_mul]
  | succ i ih =>
    rw [pow_succ', mul_assoc, ones_two_mul, ih]

lemma ones_two_pow (i : ℕ) : ones (2 ^ i) = 1 := by
  induction i with
  | zero => exact ones_one
  | succ i ih =>
    rw [pow_succ', ones_two_mul, ih]

lemma ones_two_pow_add_one (i : ℕ) : ones (2 ^ (i + 1) + 1) = 2 := by
  rw [pow_succ', ones_two_mul_add_one, ones_two_pow]

lemma ones_two_pow_add_two (i : ℕ) : ones (2 ^ (i + 2) + 2) = 2 := by
  have h : 2 ^ (i + 2) + 2 = 2 * (2 ^ (i + 1) + 1) := by rw [pow_succ']; ring
  rw [h, ones_two_mul, ones_two_pow_add_one]

lemma ones_two_pow_add_three (i : ℕ) : ones (2 ^ (i + 2) + 3) = 3 := by
  have h : 2 ^ (i + 2) + 3 = 2 * (2 ^ (i + 1) + 1) + 1 := by rw [pow_succ']; ring
  rw [h, ones_two_mul_add_one, ones_two_pow_add_one]

lemma ones_two_pow_add_four (i : ℕ) : ones (2 ^ (i + 3) + 4) = 2 := by
  have h : 2 ^ (i + 3) + 4 = 2 * (2 ^ (i + 2) + 2) := by rw [pow_succ']; ring
  rw [h, ones_two_mul, ones_two_pow_add_two]

lemma ones_two_pow_add_five (i : ℕ) : ones (2 ^ (i + 3) + 5) = 3 := by
  have h : 2 ^ (i + 3) + 5 = 2 * (2 ^ (i + 2) + 2) + 1 := by rw [pow_succ']; ring
  rw [h, ones_two_mul_add_one, ones_two_pow_add_two]

/-- Versions of the above with a hypothesis on the exponent. -/
lemma ones_two_pow_add_one' {n : ℕ} (hn : 1 ≤ n) : ones (2 ^ n + 1) = 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by lia⟩
  exact ones_two_pow_add_one i

lemma ones_two_pow_add_two' {n : ℕ} (hn : 2 ≤ n) : ones (2 ^ n + 2) = 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 2 := ⟨n - 2, by lia⟩
  exact ones_two_pow_add_two i

lemma ones_two_pow_add_three' {n : ℕ} (hn : 2 ≤ n) : ones (2 ^ n + 3) = 3 := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 2 := ⟨n - 2, by lia⟩
  exact ones_two_pow_add_three i

lemma ones_two_pow_add_four' {n : ℕ} (hn : 3 ≤ n) : ones (2 ^ n + 4) = 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 3 := ⟨n - 3, by lia⟩
  exact ones_two_pow_add_four i

lemma ones_two_pow_add_five' {n : ℕ} (hn : 3 ≤ n) : ones (2 ^ n + 5) = 3 := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 3 := ⟨n - 3, by lia⟩
  exact ones_two_pow_add_five i

lemma ones_eq_zero {m : ℕ} (h : ones m = 0) : m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    rcases Nat.even_or_odd m with he | ho
    · have h2m : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even he
      have hlt : m / 2 < m := Nat.div_lt_self hm (by norm_num)
      have h0 : ones (m / 2) = 0 := by rw [← ones_two_mul (m / 2), h2m]; exact h
      have h1 := ih (m / 2) hlt h0
      lia
    · have h2m : 2 * (m / 2) + 1 = m := Nat.two_mul_div_two_add_one_of_odd ho
      rw [← h2m, ones_two_mul_add_one] at h
      lia

lemma ones_eq_one {m : ℕ} (h : ones m = 1) : ∃ a, m = 2 ^ a := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [ones_zero] at h; lia
    rcases Nat.even_or_odd m with he | ho
    · have h2m : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even he
      have hlt : m / 2 < m := Nat.div_lt_self hm (by norm_num)
      have h1 : ones (m / 2) = 1 := by rw [← ones_two_mul (m / 2), h2m]; exact h
      obtain ⟨a, ha⟩ := ih (m / 2) hlt h1
      exact ⟨a + 1, by rw [← h2m, ha, pow_succ']⟩
    · have h2m : 2 * (m / 2) + 1 = m := Nat.two_mul_div_two_add_one_of_odd ho
      rw [← h2m, ones_two_mul_add_one] at h
      have h0 : ones (m / 2) = 0 := by lia
      have hm2 : m / 2 = 0 := ones_eq_zero h0
      exact ⟨0, by rw [pow_zero]; lia⟩

lemma ones_eq_two {m : ℕ} (h : ones m = 2) : ∃ a b, b < a ∧ m = 2 ^ a + 2 ^ b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [ones_zero] at h; lia
    rcases Nat.even_or_odd m with he | ho
    · have h2m : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even he
      have hlt : m / 2 < m := Nat.div_lt_self hm (by norm_num)
      have h1 : ones (m / 2) = 2 := by rw [← ones_two_mul (m / 2), h2m]; exact h
      obtain ⟨a, b, hba, hab⟩ := ih (m / 2) hlt h1
      exact ⟨a + 1, b + 1, by lia, by rw [← h2m, hab, pow_succ', pow_succ']; ring⟩
    · have h2m : 2 * (m / 2) + 1 = m := Nat.two_mul_div_two_add_one_of_odd ho
      rw [← h2m, ones_two_mul_add_one] at h
      have h1 : ones (m / 2) = 1 := by lia
      obtain ⟨a, ha⟩ := ones_eq_one h1
      exact ⟨a + 1, 0, by lia, by rw [pow_zero, ← h2m, ha, pow_succ']⟩

lemma add_two_pow_injective (n : ℕ) : Function.Injective fun j => 2 ^ n + 2 ^ j := by
  intro a b hab
  dsimp only at hab
  have h2 : 2 ^ a = 2 ^ b := by lia
  exact Nat.pow_right_injective (le_refl 2) h2

/-! ## The step lemma: `f (k+1) = f k` or `f k + 1` -/

/-- Cumulative count: the number of elements of `{1, ..., n}` with exactly three `1`s. -/
def g (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun m => ones m = 3).card

lemma g_succ (n : ℕ) : g (n + 1) = g n + (if ones (n + 1) = 3 then 1 else 0) := by
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    lia
  simp only [g]
  rw [hIcc, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_filter, Finset.mem_Icc]; lia)]
  · rw [add_zero]

lemma g_mono : Monotone g :=
  monotone_nat_of_le_succ fun n => by rw [g_succ]; exact Nat.le_add_right _ _

lemma f_eq (k : ℕ) : f k = g (2 * k) - g k := by
  have hIcc : Finset.Icc 1 (2 * k) = Finset.Icc 1 k ∪ Finset.Icc (k + 1) (2 * k) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    lia
  have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) (2 * k)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    lia
  have h : g (2 * k) = g k + f k := by
    simp only [g, f]
    rw [hIcc, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  lia

lemma step (k : ℕ) : f (k + 1) = f k + (if ones (2 * k + 1) = 3 then 1 else 0) := by
  have e1 := g_succ (2 * k + 1)
  have e2 := g_succ (2 * k)
  have e3 := g_succ k
  have ho : ones (2 * k + 1 + 1) = ones (k + 1) := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, ones_two_mul]
  have hle1 : g k ≤ g (2 * k) := g_mono (by lia)
  have hle2 : g (k + 1) ≤ g (2 * k + 1 + 1) := g_mono (by lia)
  have hfk := f_eq k
  have hfk1 := f_eq (k + 1)
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at hfk1
  rw [ho] at e1
  by_cases h1 : ones (2 * k + 1) = 3 <;> by_cases h2 : ones (k + 1) = 3 <;>
    simp only [h1, h2, ite_true, ite_false] at e1 e2 e3 ⊢ <;> lia

lemma f_mono : Monotone f :=
  monotone_nat_of_le_succ fun k => by rw [step]; exact Nat.le_add_right _ _

lemma f_zero : f 0 = 0 := by decide

/-! ## Part (a): `f` is surjective -/

lemma f_ge (m : ℕ) (hm : 0 < m) : m ≤ f (2 ^ (m + 1) + 2) := by
  have hsub : (Finset.range m).image (fun i => 2 ^ (m + 1) + 3 * 2 ^ i)
      ⊆ (Finset.Icc (2 ^ (m + 1) + 2 + 1) (2 * (2 ^ (m + 1) + 2))).filter (ones · = 3) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, him, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hpow : (0 : ℕ) < 2 ^ i := pow_pos (by norm_num) _
    have h1 : 2 ^ i ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by lia)
    have h3 : (2 : ℕ) ^ (m + 1) = 4 * 2 ^ (m - 1) := by
      rw [show m + 1 = m - 1 + 2 by lia, pow_add]; ring
    refine ⟨⟨by lia, by lia⟩, ?_⟩
    have h4 : 2 ^ (m + 1) + 3 * 2 ^ i = 2 ^ i * (2 ^ (m + 1 - i) + 3) := by
      rw [Nat.mul_add, pow_mul_pow_sub _ <| Nat.le_succ_of_le him.le, mul_comm]
    rw [h4, ones_two_mul_pow]
    exact ones_two_pow_add_three' (by lia)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (add_two_pow_injective_mul3 m), Finset.card_range] at hcard
  exact hcard
where
  add_two_pow_injective_mul3 (m : ℕ) :
      Function.Injective fun i => 2 ^ (m + 1) + 3 * 2 ^ i := by
    intro a b hab
    dsimp only at hab
    have h1 : 3 * 2 ^ a = 3 * 2 ^ b := by lia
    have h2 : 2 ^ a = 2 ^ b := mul_left_cancel₀ (by norm_num) h1
    exact Nat.pow_right_injective (le_refl 2) h2

/-! ## The counting lemmas -/

lemma card_two_Ico (n : ℕ) :
    ((Finset.Ico (2 ^ n) (2 ^ (n + 1))).filter (ones · = 2)).card = n := by
  have hset : (Finset.Ico (2 ^ n) (2 ^ (n + 1))).filter (ones · = 2)
      = (Finset.range n).image (fun j => 2 ^ n + 2 ^ j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨a, b, hba, rfl⟩ := ones_eq_two h3
      have ha1 : a ≤ n := by
        by_contra hlt
        push Not at hlt
        have h5 : 2 ^ (n + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by lia)
        have h6 : 2 ^ a ≤ 2 ^ a + 2 ^ b := Nat.le_add_right _ _
        lia
      have ha2 : n ≤ a := by
        by_contra hlt
        push Not at hlt
        have hb1 : 2 ^ b ≤ 2 ^ (a - 1) := pow_le_pow_right₀ (by norm_num) (by lia)
        have h7 : (2 : ℕ) ^ a = 2 ^ (a - 1) * 2 := by
          conv_lhs => rw [show a = a - 1 + 1 by lia, pow_succ]
        have h8 : 2 ^ (a + 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by lia)
        have h10 : (2 : ℕ) ^ (a + 1) = 4 * 2 ^ (a - 1) := by
          rw [show a + 1 = a - 1 + 2 by lia, pow_add]; ring
        have hpos : 0 < 2 ^ (a - 1) := pow_pos (by norm_num) _
        lia
      have haeq : a = n := by lia
      exact ⟨b, by lia, by rw [haeq]⟩
    · rintro ⟨j, hj, rfl⟩
      have hj' : j ≤ n - 1 := by lia
      have hpos : 0 < 2 ^ j := pow_pos (by norm_num) _
      refine ⟨⟨by lia, ?_⟩, ?_⟩
      · have h1 : 2 ^ j ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) hj'
        have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ']; ring
        have h3 : (2 : ℕ) ^ (n - 1) < 2 ^ n := by
          conv_rhs => rw [show n = n - 1 + 1 by lia, pow_succ']
          have hpos' : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
          lia
        lia
      · have h4 : 2 ^ n + 2 ^ j = 2 ^ j * (2 ^ (n - j) + 1) := by
          rw [mul_add, ← Nat.pow_add, Nat.add_sub_of_le hj.le, mul_one]
        rw [h4, ones_two_mul_pow]
        exact ones_two_pow_add_one' (by lia)
  rw [hset, Finset.card_image_of_injective _ (add_two_pow_injective n), Finset.card_range]

lemma card_three_Ioc_succ (n : ℕ) :
    ((Finset.Ioc (2 ^ (n + 1)) (2 ^ (n + 2))).filter (ones · = 3)).card
      = ((Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (ones · = 3)).card
        + ((Finset.Ico (2 ^ n) (2 ^ (n + 1))).filter (ones · = 2)).card := by
  have hpow1 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' _ _
  have hpow2 : (2 : ℕ) ^ (n + 2) = 2 * 2 ^ (n + 1) := pow_succ' _ _
  have hset : (Finset.Ioc (2 ^ (n + 1)) (2 ^ (n + 2))).filter (ones · = 3)
      = ((Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (ones · = 3)).image (2 * ·)
        ∪ ((Finset.Ico (2 ^ n) (2 ^ (n + 1))).filter (ones · = 2)).image (2 * · + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_union,
      Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases Nat.even_or_odd x with he | ho
      · have h2m : 2 * (x / 2) = x := Nat.two_mul_div_two_of_even he
        refine Or.inl ⟨x / 2, ⟨⟨by lia, by lia⟩, ?_⟩, h2m⟩
        rw [← ones_two_mul (x / 2), h2m]
        exact h3
      · obtain ⟨j, hj⟩ := ho
        have h2m : 2 * (x / 2) + 1 = x := by lia
        refine Or.inr ⟨x / 2, ⟨⟨by lia, by lia⟩, ?_⟩, h2m⟩
        have h4 := ones_two_mul_add_one (x / 2)
        rw [h2m] at h4
        lia
    · rintro (⟨j, ⟨⟨hj1, hj2⟩, hj3⟩, rfl⟩ | ⟨j, ⟨⟨hj1, hj2⟩, hj3⟩, rfl⟩)
      · exact ⟨⟨by lia, by lia⟩, by rw [ones_two_mul]; exact hj3⟩
      · exact ⟨⟨by lia, by lia⟩, by rw [ones_two_mul_add_one]; lia⟩
  have hdisj : Disjoint (((Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (ones · = 3)).image (2 * ·))
      (((Finset.Ico (2 ^ n) (2 ^ (n + 1))).filter (ones · = 2)).image (2 * · + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨j1, _, h1⟩ := hx1
    obtain ⟨j2, _, h2⟩ := hx2
    lia
  have hinj1 : Function.Injective ((2 * ·) : ℕ → ℕ) := fun a b h => by dsimp only at h; lia
  have hinj2 : Function.Injective ((2 * · + 1) : ℕ → ℕ) := fun a b h => by
    dsimp only at h; lia
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2]

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_two_right, Nat.choose_two_right, Nat.add_sub_cancel,
    show (n + 1) * n = n * (n - 1) + 2 * n by
      cases n with
      | zero => rfl
      | succ n => rw [Nat.add_sub_cancel]; ring]
  lia

lemma card_three (n : ℕ) :
    ((Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (ones · = 3)).card = n.choose 2 := by
  induction n with
  | zero =>
    simp only [pow_zero]
    decide
  | succ n ih =>
    rw [card_three_Ioc_succ n, ih, card_two_Ico, choose_two_succ]

lemma f_two_pow_add_two (n : ℕ) (hn : 2 ≤ n) : f (2 ^ n + 2) = n.choose 2 + 1 := by
  have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' _ _
  have h21 : ones (2 ^ n + 1) = 2 := ones_two_pow_add_one' (by lia)
  have h22 : ones (2 ^ n + 2) = 2 := ones_two_pow_add_two' hn
  have h31 : ones (2 ^ (n + 1) + 1) = 2 := ones_two_pow_add_one' (by lia)
  have h32 : ones (2 ^ (n + 1) + 2) = 2 := by
    have e : 2 ^ (n + 1) + 2 = 2 * (2 ^ n + 1) := by rw [pow_succ']; ring
    rw [e, ones_two_mul]
    exact ones_two_pow_add_one' (by lia)
  have h33 : ones (2 ^ (n + 1) + 3) = 3 := ones_two_pow_add_three' (by lia)
  have h34 : ones (2 ^ (n + 1) + 4) = 2 := ones_two_pow_add_four' (by lia)
  have h1 : (Finset.Icc (2 ^ n + 2 + 1) (2 * (2 ^ n + 2))).filter (ones · = 3)
      = (Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (ones · = 3) ∪ {2 ^ (n + 1) + 3} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, h3⟩
      by_cases hx : x ≤ 2 ^ (n + 1)
      · exact Or.inl ⟨⟨by lia, hx⟩, h3⟩
      · push Not at hx
        have h4 : x = 2 ^ (n + 1) + 3 := by
          rcases (by lia : x = 2 ^ (n + 1) + 1 ∨ x = 2 ^ (n + 1) + 2 ∨ x = 2 ^ (n + 1) + 3
            ∨ x = 2 ^ (n + 1) + 4) with rfl | rfl | rfl | rfl
          · rw [h31] at h3; lia
          · rw [h32] at h3; lia
          · rfl
          · rw [h34] at h3; lia
        exact Or.inr h4
    · rintro (⟨⟨hlo, hhi⟩, h3⟩ | rfl)
      · refine ⟨⟨?_, by lia⟩, h3⟩
        by_contra hlt
        push Not at hlt
        rcases (by lia : x = 2 ^ n + 1 ∨ x = 2 ^ n + 2) with rfl | rfl
        · rw [h21] at h3; lia
        · rw [h22] at h3; lia
      · exact ⟨⟨by lia, by lia⟩, h33⟩
  have hdisj : Disjoint ((Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (ones · = 3))
      {2 ^ (n + 1) + 3} := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    simp only [Finset.mem_singleton]
    lia
  rw [show f (2 ^ n + 2)
      = ((Finset.Icc (2 ^ n + 2 + 1) (2 * (2 ^ n + 2))).filter (ones · = 3)).card from rfl,
    h1, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, card_three]

end Imo1994P3
