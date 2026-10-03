/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256, Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 2010, Problem 5
Let $q = \dfrac{3p-5}{2}$ where $p$ is an odd prime, and let

\[S_q = \frac{1}{2\cdot 3 \cdot 4} + \frac{1}{5\cdot 6 \cdot 7} + \cdots + \frac{1}{q\cdot (q+1) \cdot (q+2)}.\]

Prove that if $\dfrac{1}{p}-2S_q = \dfrac{m}{n}$ for integers $m$ and $n$, then $m-n$ is divisible by $p$.

-/

namespace Usa2010P5

open Finset

/-- Summation of three consecutive terms in blocks of three:
the sum of `f (3i+2) + f (3i+3) + f (3i+4)` over `i ∈ range t`
equals the sum of `f j` over `j ∈ Icc 2 (3t+1)`. -/
lemma sum_range_triple (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ Finset.range t, (f (3*i+2) + f (3*i+3) + f (3*i+4)) =
    ∑ j ∈ Finset.Icc 2 (3*t+1), f j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp_rw [← add_assoc]
    repeat rw [← sum_Icc_succ_top ?_ f]
    · congr 2
    all_goals lia

/-- A sum of reciprocals as a single fraction with the product
of all denominators as denominator. -/
lemma sum_one_div_eq_div_prod {s : Finset ℕ} {c : ℕ → ℚ} (hc : ∀ i ∈ s, c i ≠ 0) :
    ∑ i ∈ s, 1 / c i = (∑ i ∈ s, ∏ j ∈ s.erase i, c j) / ∏ i ∈ s, c i := by
  have h : (∏ j ∈ s, c j) * ∑ i ∈ s, 1 / c i = ∑ i ∈ s, ∏ j ∈ s.erase i, c j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.mul_prod_erase s c hi, mul_right_comm, mul_one_div_cancel (hc i hi),
      one_mul]
  have hprod : ∏ i ∈ s, c i ≠ 0 := Finset.prod_ne_zero_iff.2 hc
  rw [eq_div_iff hprod, mul_comm (∑ i ∈ s, 1 / c i) (∏ i ∈ s, c i)]
  exact h

end Usa2010P5
