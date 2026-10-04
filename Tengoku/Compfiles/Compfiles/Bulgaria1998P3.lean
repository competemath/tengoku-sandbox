/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 3

Let ℝ⁺ be the set of positive real numbers. Prove that there does not exist a function
f: ℝ⁺ → ℝ⁺ such that

                (f(x))² ≥ f(x + y) * (f(x) + y)

for every x,y ∈ ℝ⁺.

-/

namespace Bulgaria1998P3

lemma geom_sum_bound (n : ℕ) : ∑ i ∈ Finset.range n, (1:ℝ) / (2^i) < 3 :=
  calc ∑ i ∈ Finset.range n, (1:ℝ) / ((2:ℝ)^i)
          = ∑ i ∈ Finset.range n, ((1:ℝ) / 2)^i := by {congr; simp [div_eq_mul_inv]}
        _ ≤ 2 := sum_geometric_two_le n
        _ < 3 := by norm_num

end Bulgaria1998P3
