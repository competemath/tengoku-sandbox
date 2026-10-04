/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Finset.Defs
public import Tengoku.Seed.Data.Multiset.ZeroCons
public import Tengoku.Seed.Order.Directed

/-!
# Finsets of ordered types
-/

public section


universe u v w

variable {α : Type u}

theorem Directed.finset_le {r : α → α → Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι → α}
    (D : Directed r f) (s : Finset ι) : ∃ z, ∀ i ∈ s, r (f i) (f z) :=
  show ∃ z, ∀ i ∈ s.1, r (f i) (f z) from
    Multiset.induction_on s.1 (let ⟨z⟩ := hι; ⟨z, fun _ ↦ by simp⟩)
      fun i _ ⟨j, H⟩ ↦
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun _ h ↦ (Multiset.mem_cons.1 h).casesOn (fun h ↦ h.symm ▸ h₁)
        fun h ↦ _root_.trans (H _ h) h₂⟩

theorem Finset.exists_le [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset α) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finset_le _
