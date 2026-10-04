/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.AddChar
public import Tengoku.Seed.Topology.DenseEmbedding

/-!
# Additive characters of topological monoids
-/

public section

lemma DenseRange.addChar_eq_of_eval_one_eq {A M : Type*} [TopologicalSpace A] [AddMonoidWithOne A]
    [Monoid M] [TopologicalSpace M] [T2Space M] (hdr : DenseRange ((↑) : ℕ → A))
    {κ₁ κ₂ : AddChar A M} (hκ₁ : Continuous κ₁) (hκ₂ : Continuous κ₂) (h : κ₁ 1 = κ₂ 1) :
    κ₁ = κ₂ := by
  refine DFunLike.coe_injective <| hdr.equalizer hκ₁ hκ₂ (funext fun n ↦ ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]
