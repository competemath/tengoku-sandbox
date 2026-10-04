/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku

/-!
This file proves a Ramsey theorem on infinite graphs.
This result really should be in Mathlib, but it is not.
-/

open Function Set

section InfGraphRamsey

open Classical

/-- The infinitary pigeonhole principle.
-/
lemma pigeonhole_principle {X Y : Type*} [Finite Y] (f : X → Y) {s : Set X} (h_inf : s.Infinite) :
    ∃ y, ∃ t, t.Infinite ∧ t ⊆ s ∧ ∀ x ∈ t, f x = y := by
  have := h_inf.to_subtype
  obtain ⟨y, h_inf'⟩ := Finite.exists_infinite_fiber (s.domRestrict f)
  have h_inf_iff := Equiv.infinite_iff <| Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (fun x ↦ f x = y)
  simp [coe_eq_subtype, h_inf_iff] at h_inf'
  have h_inf'' := (infinite_coe_iff (s := { x | x ∈ s ∧ f x = y })).mp h_inf'
  use y, {x | x ∈ s ∧ f x = y}
  simpa

variable {Color Vertex : Type*} [Finite Color]
abbrev Edge := Finset Vertex
variable (color : (e : Edge) → Color)

structure InfVSet (Vertex : Type*) where
  set : Set Vertex
  inf : set.Infinite

structure Selection (Color Vertex : Type*) where
  vs : InfVSet Vertex
  v : Vertex
  c : Color

def selection_prop (ivs : InfVSet Vertex) (S : Selection Color Vertex) : Prop :=
  S.vs.set ⊆ ivs.set ∧ S.v ∈ ivs.set \ S.vs.set ∧ ∀ u ∈ S.vs.set, color {S.v, u} = S.c

lemma selection_exists (ivs : InfVSet Vertex) :
    ∃ S : Selection Color Vertex, selection_prop color ivs S := by
  obtain ⟨v, h_v⟩ := Set.Infinite.nonempty ivs.inf
  let f u := color {v, u}
  obtain ⟨c, vs, h_inf, h_vs, h_col⟩ := pigeonhole_principle f <| Set.Infinite.sdiff ivs.inf (finite_singleton v)
  simp [subset_sdiff] at h_vs
  obtain ⟨h_vs, h_v'⟩ := h_vs
  let ivs' := InfVSet.mk vs h_inf
  use {vs := ivs', v := v, c := c}
  simp [selection_prop, ivs', h_vs, h_v, h_v']
  exact h_col

variable [Infinite Vertex]

noncomputable def selection_seq : ℕ → Selection Color Vertex
  | 0 => choose (selection_exists color (InfVSet.mk univ infinite_univ))
  | n + 1 => choose (selection_exists color (selection_seq n).vs)

end InfGraphRamsey
