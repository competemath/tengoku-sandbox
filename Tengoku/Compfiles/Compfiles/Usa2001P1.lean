/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 2001, Problem 1

Each of eight boxes contains six balls.
Each ball has been colored with one of n colors, such that no two balls
in the same box are the same color, and no two colors occur together in
more than one box. Determine, with justification, the smallest integer n
for which this is possible.
-/

namespace Usa2001P1

def possible_num_colors : Set ℕ :=
{ n : ℕ | ∃ f : Fin 8 → Finset (Fin n),
    (∀ i, (f i).card = 6) ∧
    (∀ x y : Fin n, ∀ i j : Fin 8,
      i ≠ j → x ∈ f i → y ∈ f i → x ≠ y →
        (¬ (x ∈ f j ∧ y ∈ f j))) }

abbrev min_colors : ℕ := 23

/--
  if
    a₁, ... a₆ is positive, ∑ (i=1 to 6), aᵢ ≤ 13
  then
    ∑ (i=1 to 6) (1 / aᵢ) ≥ 36/13
-/
lemma usa2001_p1_lemma {α} (s : Finset α) (sz : s.card = 6) (gen : α -> ℕ)
    (gt : ∀ i ∈ s, gen i > 0) (sum : (∑ i ∈ s, gen i) ≤ 13) :
    (36:ℝ)/(13:ℝ) ≤ (∑ i ∈ s, 1 / (gen i:ℝ)) := by
  let f := fun (i : α) ↦ √(gen i : ℝ)
  let g := fun (i : α) ↦ (1 : ℝ) / √(gen i : ℝ)
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  unfold f g at h
  have : ∑ x ∈ s, √(gen x : ℝ) * (1 / √(gen x : ℝ)) = ∑ x ∈ s, 1 := by
    apply Finset.sum_congr rfl
    intro x hx
    have := gt x hx
    field_simp
  rw [this] at h
  simp only [Finset.sum_const, sz, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.cast_nonneg,
    Real.sq_sqrt, one_div, inv_pow] at h
  have : (∑ x ∈ s, (gen x:ℝ)⁻¹) = (∑ x ∈ s, 1 / (gen x : ℝ)) := by congr; simp
  rw [this] at h
  set aa := (∑ x ∈ s, (gen x : ℝ)) with haa
  set bb := (∑ x ∈ s, (1 / (gen x : ℝ))) with hbb
  rify at sum
  rw [← haa] at sum
  norm_num1 at h
  have : aa ≥ 0 := by positivity
  have : bb ≥ 0 := by positivity
  field_simp
  trans aa * bb
  · exact h
  · gcongr

end Usa2001P1
