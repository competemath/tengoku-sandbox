/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1988, Problem 3

Let X be the set {1, 2, ... , 20} and let P be the set of all 9-element
subsets of X. Show that for any map f : P → X we can find a 10-element
subset Y of X, such that f(Y - {k}) ≠ k for any k in Y.
-/

namespace Usa1988P3

open Finset

/--
For any finite set `X`, the number of pairs `(Y, k)` where `Y` is a
10-element subset of `X`, `k ∈ Y`, and `f (Y.erase k) = k` is at most the
number of 9-element subsets of `X`: the map `(Y, k) ↦ Y.erase k` is
injective on such pairs, because `k = f (Y.erase k)` is determined by the
image, and then `Y = insert k (Y.erase k)` is determined as well.
-/
lemma card_bad_pairs_le (X : Finset ℕ) (f : Finset ℕ → ℕ) :
    ((X.powersetCard 10).sigma
        (fun Y ↦ Y.filter (fun k ↦ f (Y.erase k) = k))).card
      ≤ (X.powersetCard 9).card := by
  apply card_le_card_of_injOn (fun p : Σ _Y : Finset ℕ, ℕ ↦ p.1.erase p.2)
  · rintro ⟨Y, k⟩ hp
    simp only [mem_coe, mem_sigma, mem_powersetCard, mem_filter] at hp
    obtain ⟨⟨hYX, hYcard⟩, hkY, -⟩ := hp
    show Y.erase k ∈ X.powersetCard 9
    rw [mem_powersetCard]
    exact ⟨(erase_subset _ _).trans hYX, by rw [card_erase_of_mem hkY, hYcard]⟩
  · rintro ⟨Y₁, k₁⟩ hp₁ ⟨Y₂, k₂⟩ hp₂ h
    simp only [mem_coe, mem_sigma, mem_powersetCard, mem_filter] at hp₁ hp₂
    dsimp only at h
    have hk : k₁ = k₂ := by
      have e1 : f (Y₁.erase k₁) = k₁ := hp₁.2.2
      have e2 : f (Y₂.erase k₂) = k₂ := hp₂.2.2
      rw [h] at e1
      exact e1.symm.trans e2
    have hY : Y₁ = Y₂ := by
      rw [← insert_erase hp₁.2.1, ← insert_erase hp₂.2.1, h, hk]
    exact Sigma.ext hY (heq_of_eq hk)

end Usa1988P3
