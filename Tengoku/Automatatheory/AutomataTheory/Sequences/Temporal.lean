/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku.Automatatheory.AutomataTheory.Sequences.Basic

/-!
This file contains some definitions and theorems for doing
"temporal reasoning" over infinite sequences.  They are used to
prove that omega-regular languages are closed under intersection.
-/

open Function Set Filter Stream'

section Temporal

/-- Whenever `p` holds at an element in `xs`, `q` holds at the next element in `xs`.
-/
def Step {X : Type*} (xs : Stream' X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → xs (k + 1) ∈ q

/-- Whenever `p` holds at an element in `xs`, `q` holds eventually at a later element in `xs`.
-/
def LeadsTo {X : Type*} (xs : Stream' X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q

variable {X : Type*} {xs : Stream' X}

theorem leads_to_step {p q : Set X}
    (h : Step xs p q) : LeadsTo xs p q := by
  intro k h_p
  use (k + 1) ; constructor
  · omega
  · exact h k h_p

theorem leads_to_trans {p q r : Set X}
    (h1 : LeadsTo xs p q) (h2 : LeadsTo xs q r) : LeadsTo xs p r := by
  intro k h_p
  obtain ⟨k', h_k', h_q⟩ := h1 k h_p
  obtain ⟨k'', h_k'', h_r⟩ := h2 k' h_q
  use k'' ; constructor
  · omega
  · assumption

theorem frequently_leads_to_frequently {p q : Set X}
    (h1 : ∃ᶠ k in atTop, xs k ∈ p) (h2 : LeadsTo xs p q) : ∃ᶠ k in atTop, xs k ∈ q := by
  rw [frequently_atTop] at h1 ⊢
  intro k0
  obtain ⟨k1, h_k1, h_k1_p⟩ := h1 k0
  obtain ⟨k2, h_k2, h_k2_q⟩ := h2 k1 h_k1_p
  use k2 ; constructor
  · omega
  · assumption

end Temporal
