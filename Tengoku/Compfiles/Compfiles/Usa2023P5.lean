/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2023, Problem 5

Let n be an integer greater than 2. We will be arranging the numbers
1, 2, ... n² into an n × n grid. Such an arrangement is called *row-valid*
if the numbers in each row can be permuted to make an arithmetic progression.
Similarly, such an arrangement is called *column-valid* if the numbers
in each column can be permuted to make an arithmetic progression.

Determine the values of n for which it possible to transform
any row-valid arrangement into a column-valid arrangement by permuting
the numbers in each row.

-/

namespace Usa2023P5

def PermutedArithSeq {n : ℕ} (hn : 0 < n) (a : Fin n ↪ Fin (n ^ 2)) : Prop :=
    ∃ p : Fin n → Fin n, p.Bijective ∧
      ∃ k : ℕ, ∀ m : Fin n, (a (p m)).val = a (p ⟨0, hn⟩) + m.val * k

def row_valid {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n → Fin (n ^ 2)) (ha : a.Injective2) : Prop :=
    ∀ r : Fin n, PermutedArithSeq hn ⟨(a r ·), Function.Injective2.right ha r⟩

def col_valid {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n → Fin (n ^ 2)) (ha : a.Injective2) : Prop :=
    ∀ c : Fin n, PermutedArithSeq hn ⟨(a · c), Function.Injective2.left ha c⟩

theorem injective_of_permuted_rows {α β γ : Type}
    {f : α → β → γ} (hf : f.Injective2) {p : α → β → β} (hp : ∀ a, (p a).Injective) :
    Function.Injective2 (fun r c ↦ f r (p r c)) := by
  intro a1 a2 b1 b2 hab
  obtain ⟨ha1, hp1⟩ := hf hab
  rw [ha1] at *
  rw [hp a2 hp1]
  simp only [and_self]

abbrev solution_set : Set ℕ := { n | n.Prime }

/-- The Anton Trygub counterexample construction for composite `n` with prime divisor `q`,
at the level of natural number values. Row `0` is `0, …, n-1`; rows `1 ≤ r ≤ q` are
arithmetic progressions with difference `q` filling `n, …, n*q+n-1`; the remaining rows
contain the leftover numbers in reading order. -/
def trygub (n q r c : ℕ) : ℕ :=
  if r = 0 then c else if r ≤ q then n + (r - 1) + q * c else n * q + n + (r - q - 1) * n + c

lemma trygub_row_zero (n q c : ℕ) : trygub n q 0 c = c := rfl

lemma trygub_lt {n q r c : ℕ} (hr : r < n) (hc : c < n) (hq : 2 ≤ q) (hqn : q + 1 ≤ n) :
    trygub n q r c < n ^ 2 := by
  unfold trygub
  split_ifs with h0 hle
  · have hn1 : 1 ≤ n := by lia
    calc c < n := hc
      _ ≤ n ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left n (by lia)
  · have hqc : q * c + q ≤ n * q := by
      calc q * c + q = q * (c + 1) := by rw [← Nat.mul_succ]
        _ ≤ q * n := Nat.mul_le_mul_left q hc
        _ = n * q := Nat.mul_comm q n
    have hkey : n + (r - 1) + q * c < n * (q + 1) := by
      rw [Nat.mul_succ]
      lia
    calc n + (r - 1) + q * c < n * (q + 1) := hkey
      _ ≤ n * n := Nat.mul_le_mul_left n hqn
      _ = n ^ 2 := (pow_two n).symm
  · have hle : q < r := not_le.mp hle
    have hqn2 : q + 2 ≤ n := by lia
    have h3 : (r - q - 1) * n + (n * q + 2 * n) ≤ n * n := by
      have h31 : (r - q - 1) * n ≤ (n - (q + 2)) * n := Nat.mul_le_mul_right n (by lia)
      have h32 : (n - (q + 2)) * n + (n * q + 2 * n) = n * n := by
        rw [Nat.mul_comm n q, ← add_mul, ← Nat.add_mul, Nat.sub_add_cancel hqn2]
      lia
    have hle2 : n * q + 2 * n ≤ n * n := by
      have := Nat.mul_le_mul_right n hqn2
      rw [add_mul, Nat.mul_comm q n] at this
      exact this
    rw [pow_two]
    lia

lemma trygub_eq_zero {n q r c : ℕ} (hn : 2 ≤ n) :
    trygub n q r c = 0 → r = 0 ∧ c = 0 := by
  unfold trygub
  split_ifs with h0 hle
  · exact fun h ↦ ⟨h0, h⟩
  · lia
  · lia

/-- Rows `1 ≤ r ≤ q` contain values in `[n, n*q+n)`. -/
lemma trygub_mid_bounds {n q r c : ℕ} (h0 : r ≠ 0) (hle : r ≤ q) (hc : c < n) :
    n ≤ trygub n q r c ∧ trygub n q r c < n * q + n := by
  unfold trygub
  rw [ite_eq_right h0, ite_eq_left hle]
  have hqc : q * c + q ≤ n * q := by
    calc q * c + q = q * (c + 1) := by rw [← Nat.mul_succ]
      _ ≤ q * n := Nat.mul_le_mul_left q hc
      _ = n * q := Nat.mul_comm q n
  lia

/-- Rows `r > q` contain values in `[n*q+n, n^2)`. -/
lemma trygub_top_bound (n q : ℕ) {r : ℕ} (c : ℕ) (hle : ¬ r ≤ q) :
    n * q + n ≤ trygub n q r c := by
  unfold trygub
  rw [ite_eq_right (by lia : r ≠ 0), ite_eq_right hle]
  lia

lemma trygub_last_ge {n q c : ℕ} (hq : 2 ≤ q) (hqn : q + 2 ≤ n) :
    n ^ 2 - n ≤ trygub n q (n - 1) c := by
  unfold trygub
  split_ifs with h0 hle
  · lia
  · lia
  · have e2 : (n - 1 - q - 1) * n + (q + 2) * n = n * n := by
      have e1 : n - 1 - q - 1 = n - (q + 2) := by lia
      rw [e1, ← Nat.add_mul, Nat.sub_add_cancel hqn]
    have e3 : (q + 2) * n = n * q + 2 * n := by rw [add_mul, Nat.mul_comm q n]
    rw [e3] at e2
    rw [pow_two]
    lia

lemma trygub_inj {n q r₁ r₂ c₁ c₂ : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) (_hqn : q + 1 ≤ n)
    (hr₁ : r₁ < n) (hr₂ : r₂ < n) (hc₁ : c₁ < n) (hc₂ : c₂ < n)
    (h : trygub n q r₁ c₁ = trygub n q r₂ c₂) : r₁ = r₂ ∧ c₁ = c₂ := by
  by_cases h10 : r₁ = 0
  · by_cases h20 : r₂ = 0
    · subst h10; subst h20
      rw [trygub_row_zero, trygub_row_zero] at h
      exact ⟨rfl, h⟩
    · by_cases h2q : r₂ ≤ q
      · rw [h10, trygub_row_zero] at h
        have hb := (trygub_mid_bounds h20 h2q hc₂).1
        lia
      · rw [h10, trygub_row_zero] at h
        have hb := trygub_top_bound n q c₂ h2q
        lia
  · by_cases h20 : r₂ = 0
    · by_cases h1q : r₁ ≤ q
      · rw [h20, trygub_row_zero] at h
        have hb := (trygub_mid_bounds h10 h1q hc₁).1
        lia
      · rw [h20, trygub_row_zero] at h
        have hb := trygub_top_bound n q c₁ h1q
        lia
    · by_cases h1q : r₁ ≤ q
      · by_cases h2q : r₂ ≤ q
        · unfold trygub at h
          rw [ite_eq_right h10, ite_eq_left h1q, ite_eq_right h20, ite_eq_left h2q] at h
          have h' : r₁ - 1 + q * c₁ = r₂ - 1 + q * c₂ := by lia
          have m1 : (r₁ - 1 + q * c₁) % q = r₁ - 1 := by
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by lia)
          have m2 : (r₂ - 1 + q * c₂) % q = r₂ - 1 := by
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by lia)
          have hr1 : r₁ - 1 = r₂ - 1 := by rw [h'] at m1; exact m1.symm.trans m2
          have hr : r₁ = r₂ := by lia
          subst hr
          have hm : q * c₁ = q * c₂ := by lia
          exact ⟨rfl, mul_left_cancel₀ (by lia : q ≠ 0) hm⟩
        · have h1b := (trygub_mid_bounds h10 h1q hc₁).2
          have h2b := trygub_top_bound n q c₂ h2q
          lia
      · by_cases h2q : r₂ ≤ q
        · have h1b := trygub_top_bound n q c₁ h1q
          have h2b := (trygub_mid_bounds h20 h2q hc₂).2
          lia
        · unfold trygub at h
          rw [ite_eq_right h10, ite_eq_right h1q, ite_eq_right h20, ite_eq_right h2q] at h
          have h' : (r₁ - q - 1) * n + c₁ = (r₂ - q - 1) * n + c₂ := by lia
          have hc : c₁ = c₂ := by
            have m1 : ((r₁ - q - 1) * n + c₁) % n = c₁ := by
              rw [Nat.add_comm, Nat.add_mul_mod_self_right]
              exact Nat.mod_eq_of_lt hc₁
            have m2 : ((r₂ - q - 1) * n + c₂) % n = c₂ := by
              rw [Nat.add_comm, Nat.add_mul_mod_self_right]
              exact Nat.mod_eq_of_lt hc₂
            rw [h'] at m1
            exact m1.symm.trans m2
          subst hc
          have hr : r₁ - q - 1 = r₂ - q - 1 := by
            have m1 : ((r₁ - q - 1) * n + c₁) / n = r₁ - q - 1 := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by lia : 0 < n)]
              rw [Nat.div_eq_of_lt hc₁]
              lia
            have m2 : ((r₂ - q - 1) * n + c₁) / n = r₂ - q - 1 := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by lia : 0 < n)]
              rw [Nat.div_eq_of_lt hc₁]
              lia
            rw [h'] at m1
            exact m1.symm.trans m2
          have : r₁ = r₂ := by lia
          exact ⟨this, rfl⟩

lemma trygub_eq_add_one {n q r c : ℕ} (_hn : 4 ≤ n) (hq : 2 ≤ q)
    (_hr : r < n) (hc : c < n) (h : trygub n q r c = n + 1) : r = 2 := by
  unfold trygub at h
  split_ifs at h with h0 hle
  · lia
  · by_cases hc0 : c = 0
    · subst hc0
      rw [Nat.mul_zero, Nat.add_zero] at h
      lia
    · have hqc : q ≤ q * c := Nat.le_mul_of_pos_right q (by lia)
      lia
  · have hnq : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    lia

lemma trygub_eq_two_mul_add_one {n q r c : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) (hdvd : q ∣ n)
    (_hr : r < n) (hc : c < n) (h : trygub n q r c = 2 * n + 1) : r = 2 := by
  unfold trygub at h
  split_ifs at h with h0 hle
  · lia
  · have h1 : r - 1 + q * c = n + 1 := by lia
    have h2 : (r - 1 + q * c) % q = r - 1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by lia)
    have h3 : (n + 1) % q = 1 := by
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, Nat.add_comm (q * t) 1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hq
    rw [h1] at h2
    have h4 : r - 1 = 1 := h2.symm.trans h3
    lia
  · have hnq : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    lia

lemma trygub_mid (n q r c : ℕ) (h0 : r ≠ 0) (hle : r ≤ q) :
    trygub n q r c = n + (r - 1) + q * c := by
  unfold trygub
  rw [ite_eq_right h0, ite_eq_left hle]

lemma trygub_top (n q r c : ℕ) (hle : ¬ r ≤ q) :
    trygub n q r c = n * q + n + (r - q - 1) * n + c := by
  unfold trygub
  rw [ite_eq_right (by lia : r ≠ 0), ite_eq_right hle]

/-- Two naturals with the same quotient and remainder mod `m` are equal. -/
lemma eq_of_div_mod_eq {v₁ v₂ m : ℕ} (hdiv : v₁ / m = v₂ / m) (hmod : v₁ % m = v₂ % m) :
    v₁ = v₂ := by
  rw [← Nat.div_add_mod v₁ m, ← Nat.div_add_mod v₂ m, hdiv, hmod]

/-- The quotient of an element of `Fin (n^2)` by `n` is again in `Fin n`. -/
lemma div_lt_of_mem {n : ℕ} (v : Fin (n ^ 2)) : v.val / n < n :=
  Nat.div_lt_of_lt_mul (by rw [← pow_two]; exact v.isLt)

/-- The common difference of a permuted arithmetic progression of length at least 2
of elements of `Fin (n^2)` is positive. -/
lemma ap_k_pos {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n) {f : Fin n → Fin (n ^ 2)} (hf : f.Injective)
    {p : Fin n → Fin n} (hp : p.Injective) {k : ℕ}
    (hk : ∀ m : Fin n, (f (p m)).val = (f (p ⟨0, hn⟩)).val + m.val * k) : 1 ≤ k := by
  by_contra h0
  have h0 : k = 0 := by lia
  subst h0
  have heq : f (p ⟨1, by lia⟩) = f (p ⟨0, hn⟩) := by
    apply Fin.ext
    rw [hk ⟨1, by lia⟩, Nat.mul_zero, Nat.add_zero]
  have h10 := hp (hf heq)
  have h13 : (1 : ℕ) = 0 := congrArg Fin.val h10
  lia

/-- For prime `n`, an arithmetic progression of length `n` whose common difference is not
divisible by `n` hits every residue class mod `n` at most once. -/
lemma ap_res_inj {n : ℕ} (hp : n.Prime) {k : ℕ} (hk : ¬ n ∣ k) (b : ℕ) {m₁ m₂ : Fin n}
    (h : (b + m₁.val * k) % n = (b + m₂.val * k) % n) : m₁ = m₂ := by
  have : Fact n.Prime := ⟨hp⟩
  have h' : ((b + m₁.val * k : ℕ) : ZMod n) = ((b + m₂.val * k : ℕ) : ZMod n) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  push_cast at h'
  have hk0 : (k : ZMod n) ≠ 0 := by
    intro hkc
    rw [ZMod.natCast_eq_zero_iff] at hkc
    exact hk hkc
  have hmk : (m₁.val : ZMod n) * (k : ZMod n) = (m₂.val : ZMod n) * (k : ZMod n) :=
    add_left_cancel h'
  have hm : (m₁.val : ZMod n) = (m₂.val : ZMod n) := mul_right_cancel₀ hk0 hmk
  rw [ZMod.natCast_eq_natCast_iff] at hm
  have hval : m₁.val = m₂.val := by
    rw [← Nat.mod_eq_of_lt m₁.isLt, ← Nat.mod_eq_of_lt m₂.isLt]
    exact hm
  exact Fin.ext hval

/-- The Trygub arrangement, packaged as a grid of elements of `Fin (n^2)`. -/
def trygubArr (n q : ℕ) (hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2) :
    Fin n → Fin n → Fin (n ^ 2) :=
  fun r c ↦ ⟨trygub n q r.val c.val, hbound r c⟩

lemma trygubArr_injective2 {n q : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) (hqn : q + 1 ≤ n)
    (hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2) :
    (trygubArr n q hbound).Injective2 := by
  intro r₁ r₂ c₁ c₂ h
  have hv : trygub n q r₁.val c₁.val = trygub n q r₂.val c₂.val := congrArg Fin.val h
  obtain ⟨hr, hc⟩ := trygub_inj hn hq hqn r₁.isLt r₂.isLt c₁.isLt c₂.isLt hv
  exact ⟨Fin.ext hr, Fin.ext hc⟩

lemma trygubArr_row_valid {n q : ℕ} (hn0 : 0 < n) (_hq : 2 ≤ q)
    (hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2)
    (ha : (trygubArr n q hbound).Injective2) :
    row_valid hn0 (trygubArr n q hbound) ha := by
  intro r
  by_cases h0 : r.val = 0
  · refine ⟨id, Function.bijective_id, 1, fun m ↦ ?_⟩
    show (trygubArr n q hbound r m).val = (trygubArr n q hbound r ⟨0, hn0⟩).val + m.val * 1
    show trygub n q r.val m.val = trygub n q r.val 0 + m.val * 1
    rw [h0, trygub_row_zero, trygub_row_zero]
    lia
  · by_cases hq_le : r.val ≤ q
    · refine ⟨id, Function.bijective_id, q, fun m ↦ ?_⟩
      show (trygubArr n q hbound r m).val = (trygubArr n q hbound r ⟨0, hn0⟩).val + m.val * q
      show trygub n q r.val m.val = trygub n q r.val 0 + m.val * q
      rw [trygub_mid n q r.val m.val h0 hq_le, trygub_mid n q r.val 0 h0 hq_le,
        Nat.mul_comm q m.val]
      lia
    · refine ⟨id, Function.bijective_id, 1, fun m ↦ ?_⟩
      show (trygubArr n q hbound r m).val = (trygubArr n q hbound r ⟨0, hn0⟩).val + m.val * 1
      show trygub n q r.val m.val = trygub n q r.val 0 + m.val * 1
      rw [trygub_top n q r.val m.val hq_le, trygub_top n q r.val 0 hq_le]
      lia

end Usa2023P5
