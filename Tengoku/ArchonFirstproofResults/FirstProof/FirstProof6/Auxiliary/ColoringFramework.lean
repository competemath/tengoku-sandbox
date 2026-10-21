/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# Problem 6: Large epsilon-light vertex subsets -- Coloring Framework

`PartialColoring` structure, pigeonhole bound,
`coloring_step_exists`, `coloring_iterate`,
and `barrier_parameter_bound`.

## Main definitions

- `Problem6.PartialColoring`: partial vertex coloring

## Main theorems

- `Problem6.largest_color_class_bound`: pigeonhole bound
- `Problem6.coloring_step_exists`: one-step coloring extension
- `Problem6.coloring_iterate`: k-step coloring iteration
- `Problem6.barrier_parameter_bound`: final parameter bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Coloring process -/

/-- A coloring of a subset `T ⊆ V` with `r` colors. -/
structure PartialColoring (V : Type*) [Fintype V] (r : ℕ) where
  /-- The set of colored vertices -/
  colored : Finset V
  /-- The color assignment function -/
  color : V → Fin r

omit [DecidableEq V] in
/-- The largest color class in a coloring has size at least |T|/r (pigeonhole).
@isnad1 id=ex.1h3v.s6.5eeb7a5cf471 from=translated src=- shape=b74cf9de vocab=10fdc908
-/
lemma largest_color_class_bound
    (pc : PartialColoring V r) (hr : 0 < r) :
    ∃ γ : Fin r,
      (pc.colored.filter (fun v => pc.color v = γ)).card * r ≥
        pc.colored.card := by
  classical
  -- Pigeonhole: color classes partition pc.colored; sum of sizes = |T|;
  -- max size ≥ average = |T|/r.
  by_contra hall
  push_neg at hall
  -- Color classes partition pc.colored
  have hsum : pc.colored.card =
      ∑ γ : Fin r, (pc.colored.filter (fun v => pc.color v = γ)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext v; simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro i _ j _ hij
      exact Finset.disjoint_filter.mpr fun _ _ h1 h2 => hij (h1 ▸ h2)
  -- Each color class * r < |T|, so sum * r < r * |T|
  have hlt : ∑ γ : Fin r, (pc.colored.filter (fun v => pc.color v = γ)).card * r <
      ∑ _ : Fin r, pc.colored.card :=
    Finset.sum_lt_sum (fun γ _ => le_of_lt (hall γ))
      ⟨⟨0, hr⟩, Finset.mem_univ _, hall ⟨0, hr⟩⟩
  -- LHS = |T| * r, RHS = r * |T|, contradiction
  rw [← Finset.sum_mul] at hlt
  rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin] at hlt
  rw [hsum, Nat.mul_comm] at hlt
  exact lt_irrefl _ hlt

/-! ### The inductive coloring step -/

/-- **Parameter bound (Step 3)**: The final barrier parameter u_k = eps/2 + k*(eps/n)
    satisfies u_k <= 3*eps/4 < eps when k = n/4 and n >= 4.
    Proof: u_k = eps/2 + (n/4)*(eps/n). Since n/4 <= n/4 (integer division),
    (n/4)*(eps/n) <= (n/4)*(eps/n) = eps/4. So u_k <= eps/2 + eps/4 = 3*eps/4 < eps.
@isnad1 id=other.2h2v.s7.3442ccb12c4f from=translated src=- shape=701ada8f vocab=3a4e774d
-/
lemma barrier_parameter_bound
    (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (hn : 4 ≤ n) :
    let k := n / 4
    let u₀ := ε / 2
    let δ := ε / (n : ℝ)
    let u_k := u₀ + (k : ℝ) * δ
    u_k ≤ 3 * ε / 4 ∧ 3 * ε / 4 < ε := by
  constructor
  · -- u_k = eps/2 + (n/4) * (eps/n) <= eps/2 + (n/4)/n * eps <= eps/2 + eps/4
    show ε / 2 + ↑(n / 4) * (ε / ↑n) ≤ 3 * ε / 4
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    -- Key: 4 * (n/4 : ℕ) ≤ n, so (n/4 : ℕ) ≤ n/4 as reals
    have h4_div : 4 * (↑(n / 4) : ℝ) ≤ (n : ℝ) := by
      have := Nat.div_mul_le_self n 4
      have : (n / 4) * 4 ≤ n := this
      exact_mod_cast show 4 * (n / 4) ≤ n by omega
    -- (n/4) * (eps/n) ≤ eps/4
    have key : (↑(n / 4) : ℝ) * (ε / ↑n) ≤ ε / 4 := by
      rw [mul_div_assoc']
      rw [div_le_div_iff₀ hn_pos (by norm_num : (0:ℝ) < 4)]
      nlinarith
    linarith
  · -- 3*eps/4 < eps when eps > 0
    linarith
end Problem6

end
