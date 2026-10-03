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
# USA Mathematical Olympiad 2005, Problem 4

Legs L₁, L₂, L₃, L₄ of a square table each have length n, where n is a positive
integer. For how many ordered 4-tuples (k₁, k₂, k₃, k₄) of nonnegative integers
can we cut a piece of length kᵢ from the end of leg Lᵢ (i = 1, 2, 3, 4) and
still have a stable table? (The table is stable if it can be placed so that
all four of the leg ends touch the floor. Note that a cut leg of length 0 is
permitted.)
-/

namespace Usa2005P4

abbrev solution (n : ℕ) : ℕ := (n + 1) * (2 * n ^ 2 + 4 * n + 3) / 3

/-!
### Reduction to a counting problem

Put the table upside down, so that the tabletop rests on the floor and the
truncated legs point vertically upwards from the corners of a square, with
lengths `n - kᵢ`. The table is stable iff the four leg endpoints are coplanar.
Four points directly above the corners of a square are coplanar iff they form
a parallelogram, i.e. iff `(n - k₁) + (n - k₃) = (n - k₂) + (n - k₄)`, or
equivalently `k₁ + k₃ = k₂ + k₄`. Hence the answer is the number of 4-tuples
`(k₁, k₂, k₃, k₄)` of natural numbers with `kᵢ ≤ n` and `k₁ + k₃ = k₂ + k₄`.
We count them below for every `n : ℕ`; the formula also gives the correct
value `1` for `n = 0`.
-/

/-- The admissible 4-tuples, as a `Finset`. -/
def tuples (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
    Finset.range (n + 1)).filter fun k => k.1 + k.2.2.1 = k.2.1 + k.2.2.2

/-- `pairCount n r` counts pairs `(a, b)` of natural numbers with `a, b ≤ n`
and `a + b = r`. -/
def pairCount (n r : ℕ) : ℕ :=
  (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun p => p.1 + p.2 = r).card

/-- The symmetry `(a, b) ↦ (n - a, n - b)` shows `pairCount n r = pairCount n (2 * n - r)`. -/
lemma pairCount_symm {n r : ℕ} (hr : r ≤ 2 * n) : pairCount n r = pairCount n (2 * n - r) := by
  unfold pairCount
  apply Finset.card_bij' (fun p _ => (n - p.1, n - p.2)) (fun p _ => (n - p.1, n - p.2))
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    lia
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    lia
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    show (n - (n - a), n - (n - b)) = (a, b)
    rw [Prod.mk.injEq]
    exact ⟨by lia, by lia⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    show (n - (n - a), n - (n - b)) = (a, b)
    rw [Prod.mk.injEq]
    exact ⟨by lia, by lia⟩

/-- The number of admissible 4-tuples is `∑ r, (pairCount n r)^2`: group the
4-tuples according to the common value `r` of `k₁ + k₃ = k₂ + k₄`. -/
lemma tuples_card_eq_sum (n : ℕ) :
    (tuples n).card = ∑ r ∈ Finset.range (2 * n + 1), (pairCount n r) ^ 2 := by
  have h1 : (tuples n).card =
      ((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ
          ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)))).filter
        fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2).card := by
    apply Finset.card_bij' (fun k _ => ((k.1, k.2.2.1), (k.2.1, k.2.2.2)))
      (fun x _ => (x.1.1, x.2.1, x.1.2, x.2.2))
    case hi =>
      rintro ⟨a, b, c, d⟩ h
      simp only [tuples, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      tauto
    case hj =>
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
      simp only [tuples, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      tauto
    case left_inv =>
      rintro ⟨a, b, c, d⟩ _
      rfl
    case right_inv =>
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
      rfl
  rw [h1]
  set F := ((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ
      ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)))).filter
    fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2) with hF
  have hmaps : (F : Set ((ℕ × ℕ) × (ℕ × ℕ))).MapsTo
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 + x.1.2)
      (↑(Finset.range (2 * n + 1)) : Set ℕ) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at h
    simp only [Finset.coe_range, Set.mem_Iio]
    lia
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hfib : F.filter (fun x => x.1.1 + x.1.2 = r) =
      (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
        fun p => p.1 + p.2 = r) ×ˢ
      (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
        fun p => p.1 + p.2 = r) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    lia
  rw [hfib, Finset.card_product, pow_two]
  rfl

/-- Three times the count equals `(n + 1) * (2 * n ^ 2 + 4 * n + 3)`. -/
lemma key_arith (n : ℕ) :
    3 * (2 * (∑ i ∈ Finset.range (n + 1), i ^ 2) + (n + 1) ^ 2) =
      (n + 1) * (2 * n ^ 2 + 4 * n + 3) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h : 3 * (2 * ((∑ i ∈ Finset.range (k + 1), i ^ 2) + (k + 1) ^ 2) + (k + 1 + 1) ^ 2) =
        3 * (2 * (∑ i ∈ Finset.range (k + 1), i ^ 2) + (k + 1) ^ 2) +
          3 * ((k + 1) ^ 2 + (k + 1 + 1) ^ 2) := by ring
    rw [h, ih]
    ring

end Usa2005P4
