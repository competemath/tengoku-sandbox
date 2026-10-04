/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku.Automatatheory.AutomataTheory.Sequences.Basic

/-!
This file contains some definitions and theorems about
infinite occurrences in an infinite sequence.
-/

open Function Set Prod Option Filter Stream'
open Classical

section InfOcc

/-- `InfOcc xs` is the set of elements that appears infinitely many times in `xs`.
-/
def InfOcc {X : Type*} (xs : Stream' X) : Set X :=
  { x | ∃ᶠ k in atTop, xs k = x }

/-- Removing any finite prefix of `xs` does not change `InfOcc xs`.
-/
theorem inf_occ_suffix {X : Type*} (xs : Stream' X) (k : ℕ) :
    InfOcc (xs.drop k) = InfOcc xs := by
  ext x ; simp [InfOcc, frequently_atTop] ; constructor
  · intro h_inf n ; obtain ⟨m, h_m, rfl⟩ := h_inf n
    use (k + m) ; simp [get_drop'] ; omega
  · intro h_inf n ; obtain ⟨m, h_m, rfl⟩ := h_inf (n + k)
    use (m - k) ; simp [get_drop', (show n ≤ m - k by omega), (show k + (m - k) = m by omega)]

/-- Over a finite type, `xs k` is in `InfOcc xs` for all sufficiently large `k`.
-/
theorem inf_occ_eventually {X : Type*} [Finite X] (xs : Stream' X) :
    ∀ᶠ k in atTop, xs k ∈ InfOcc xs := by
  have h_compl : ∀ x ∈ (InfOcc xs)ᶜ, ∃ n, ∀ k ≥ n, xs k ≠ x := by simp [InfOcc]
  choose lb h_lb using h_compl
  let fs_compl := Finite.toFinset <| toFinite (InfOcc xs)ᶜ
  let glb := fs_compl.sup (fun x ↦ if h : x ∈ (InfOcc xs)ᶜ then lb x h else 0)
  have h_glb : ∀ x, (h : x ∈ (InfOcc xs)ᶜ) → lb x h ≤ glb := by
    intro x h ; refine Finset.le_sup_of_le (b := x) (by simpa [fs_compl]) (by simp [h])
  apply eventually_atTop.mpr
  use glb ; intro k h_k ; by_contra h_contra
  have := h_glb (xs k) h_contra
  have := h_lb (xs k) h_contra k (by omega)
  contradiction

/- The following two proofs are due to Aaron Liu.
The ⊆ direction of the first proof doesn't need injectivity assumption.
-/
-- The following proof is due to Kyle Miller

end InfOcc
