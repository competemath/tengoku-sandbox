/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# IMO 2020 A4 (P2)

Let $a, b, c, d ∈ ℝ$ with $a ≥ b ≥ c ≥ d > 0$ and $a + b + c + d = 1$.
Prove that $$ (a + 2b + 3c + 4d) a^a b^b c^c d^d < 1. $$

### Solution

We follow both Solution 1 and Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2020SL.pdf).
We start with $a + 2b + 3c + 4d ≤ a + 3(b + c + d) = 3 - 2a$.
Then we use the bound $a^a b^b c^c d^d ≤ a$ when $a < 1/2$ and the weighted AM-GM
  $a^a b^b c^c d^d ≤ a^2 + b^2 + c^2 + d^2$ when $1/2 ≤ a < 1$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2020A4

open Finset Real

section

variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-- If `a, b > 0` then` a^2 + b^2 < (a + b)^2`. -/
theorem sq_add_lt_add_sq {a b : R} (ha : a > 0) (hb : b > 0) :
    a ^ 2 + b ^ 2 < (a + b) ^ 2 := by
  rw [add_sq', lt_add_iff_pos_right]
  exact mul_pos (mul_pos two_pos ha) hb

/-- If `n ≥ 2` and `x_1, x_2, …, x_n > 0`, then `∑_i x_i^2 < (∑_i x_i)^2`. -/
theorem sum_sq_lt_sq_sum_of_pos [DecidableEq ι] {f : ι → R} {I : Finset ι}
    (hI : #I ≥ 2) (hf : ∀ i ∈ I, 0 < f i) :
    ∑ i ∈ I, f i ^ 2 < (∑ i ∈ I, f i) ^ 2 := by
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := card_pos.mp (Nat.zero_lt_of_lt hI)
  replace hI : (I.erase i₀).Nonempty :=
    card_pos.mp ((Nat.sub_le_sub_right hI 1).trans pred_card_le_card_erase)
  have hf' (i) (hi : i ∈ I.erase i₀) : 0 < f i := hf i (mem_of_mem_erase hi)
  calc ∑ i ∈ I, f i ^ 2
    _ = f i₀ ^ 2 + ∑ i ∈ I.erase i₀, f i ^ 2 := (add_sum_erase _ _ hi₀).symm
    _ ≤ f i₀ ^ 2 + (∑ i ∈ I.erase i₀, f i) ^ 2 :=
      add_le_add_right (sum_sq_le_sq_sum_of_nonneg λ i hi ↦ (hf' i hi).le) _
    _ < (f i₀ + ∑ i ∈ I.erase i₀, f i) ^ 2 :=
      sq_add_lt_add_sq (hf i₀ hi₀) (sum_pos hf' hI)
    _ = (∑ i ∈ I, f i) ^ 2 := by rw [add_sum_erase _ _ hi₀]

end
