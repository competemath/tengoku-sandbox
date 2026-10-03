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
# USA Mathematical Olympiad 1999, Problem 4

Let a₁, a₂, ..., aₙ be a sequence of n > 3 real numbers such that

  a₁ + a₂ + ⋯ + aₙ ≥ n

and

  a₁² + a₂² + ⋯ + aₙ² ≥ n².

Prove that max(a₁, a₂, ..., aₙ) ≥ 2.
-/

namespace Usa1999P4

/-!
We follow the proof from Evan Chen's
[USAMO 1999 Solution Notes](https://web.evanchen.cc/exams/USAMO-1999-notes.pdf),
reformulated so that no iterative "smoothing" is needed.

Assume `aᵢ < 2` for all `i`. If every `aᵢ` is nonnegative, then
`∑ aᵢ² < 4n ≤ n²`, a contradiction. Otherwise, writing `S` for the sum of the
nonnegative entries and `-M` for the sum of the negative entries, one checks
`∑ aᵢ² ≤ 2S + M²` and `M ≤ S - n`, hence `n² ≤ 2S + (S - n)²`, which forces
`S ≥ 2n - 2`. But `S < 2·#P ≤ 2(n - 1)`, contradiction.
-/

/-- If every value of `f` on `s` is nonpositive, then the sum of the squares is
at most the square of the sum: the cross terms are nonnegative. -/
theorem sum_sq_le_sq_sum_of_nonpos {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ≤ 0) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have h1 : ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, (-f i) ^ 2 :=
    Finset.sum_congr rfl fun i _ ↦ by rw [neg_sq]
  have h2 : (∑ i ∈ s, f i) ^ 2 = (∑ i ∈ s, -f i) ^ 2 := by
    rw [Finset.sum_neg_distrib, neg_sq]
  rw [h1, h2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i hi ↦ neg_nonneg.mpr (hf i hi)

end Usa1999P4
