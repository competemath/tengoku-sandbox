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
# USA Mathematical Olympiad 1997, Problem 6

Suppose the sequence of nonnegative integers a₁, a₂, ..., a₁₉₉₇ satisfies

  aᵢ + aⱼ ≤ aᵢ₊ⱼ ≤ aᵢ + aⱼ + 1

for all i, j ≥ 1 with i + j ≤ 1997.
Prove that there exists a real number x such that
aₙ = ⌊nx⌋ for all 1 ≤ n ≤ 1997.
-/

namespace Usa1997P6

/-!
The key inequality: for all indices `1 ≤ m, n ≤ 1997` we have
`n * a m + 1 ≤ m * a n + m`, i.e. `a m / m < (a n + 1) / n`.
It is proved by strong induction on `m + n`.  If `m < n`, write `n = m + s`
and combine superadditivity `a m + a s ≤ a n` with the induction hypothesis
for the pair `(m, s)`; if `m > n`, write `m = n + r` and combine
`a m ≤ a n + a r + 1` with the induction hypothesis for the pair `(r, n)`.
-/

lemma key_ineq (a : ℕ → ℕ)
    (hlo : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i + j ≤ 1997 → a i + a j ≤ a (i + j))
    (hhi : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i + j ≤ 1997 → a (i + j) ≤ a i + a j + 1) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m ≤ 1997 → n ≤ 1997 →
      n * a m + 1 ≤ m * a n + m := by
  suffices H : ∀ k m n : ℕ, m + n = k → 1 ≤ m → 1 ≤ n → m ≤ 1997 → n ≤ 1997 →
      n * a m + 1 ≤ m * a n + m by
    intro m n hm hn hmN hnN
    exact H (m + n) m n rfl hm hn hmN hnN
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro m n hsum hm hn hmN hnN
    rcases lt_trichotomy m n with hmn | rfl | hmn
    · -- Case `m < n`: write `n = m + s` and apply the IH to the pair `(m, s)`.
      obtain ⟨s, rfl⟩ : ∃ s, n = m + s := ⟨n - m, by lia⟩
      have hs : 1 ≤ s := by lia
      have hsN : s ≤ 1997 := by lia
      have h1 : a m + a s ≤ a (m + s) := hlo m s hm hs hnN
      have ih' : s * a m + 1 ≤ m * a s + m := ih (m + s) (by lia) m s rfl hm hs hmN hsN
      calc (m + s) * a m + 1 = m * a m + (s * a m + 1) := by ring
        _ ≤ m * a m + (m * a s + m) := Nat.add_le_add_left ih' _
        _ = m * (a m + a s) + m := by ring
        _ ≤ m * a (m + s) + m := Nat.add_le_add_right (Nat.mul_le_mul_left m h1) m
    · -- Case `m = n`: trivial since `n ≥ 1`.
      exact Nat.add_le_add_left (by assumption) _
    · -- Case `m > n`: write `m = n + r` and apply the IH to the pair `(r, n)`.
      obtain ⟨r, rfl⟩ : ∃ r, m = n + r := ⟨m - n, by lia⟩
      have hr : 1 ≤ r := by lia
      have hrN : r ≤ 1997 := by lia
      have h2 : a (n + r) ≤ a n + a r + 1 := hhi n r hn hr hmN
      have ih' : n * a r + 1 ≤ r * a n + r := ih (n + r) (by lia) r n (by lia) hr hn hrN hnN
      calc n * a (n + r) + 1 ≤ n * (a n + a r + 1) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left n h2) 1
        _ = n * a n + (n * a r + 1) + n := by ring
        _ ≤ n * a n + (r * a n + r) + n :=
            Nat.add_le_add_right (Nat.add_le_add_left ih' _) _
        _ = (n + r) * a n + (n + r) := by ring

end Usa1997P6
