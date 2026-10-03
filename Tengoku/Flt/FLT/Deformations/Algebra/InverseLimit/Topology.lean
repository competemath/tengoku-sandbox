/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import Tengoku.Flt.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import Tengoku.Flt.FLT.Deformations.Algebra.InverseLimit.Basic
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Topology on inverse limits

The inverse limit of a system of topological algebraic structures inherits
a natural topological structure as a subspace of the product. We record
basic continuity properties of the canonical maps.
-/

@[expose] public section

open TopologicalSpace

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G j) (G i)]
variable [∀ i : ι, TopologicalSpace (G i)]
  {cont : ∀ {i j}, (h : i ≤ j) → Continuous (f i j h)}

namespace InverseLimit

variable {W : Type*} {M : ι → Type*} (maps : ∀ i, M i) [∀ i, FunLike (M i) W (G i)]
variable (inverseSystemHom : InverseSystemHom G f maps)
variable [TopologicalSpace W]
variable (maps_cont : (i : ι) → Continuous (maps i))

instance : TopologicalSpace (InverseLimit G f) :=
  inferInstanceAs (TopologicalSpace {x : (i : ι) → G i // ∀ i j h, f i j h (x j) = x i})

@[fun_prop, continuity]
lemma val_continuous : Continuous (fun (x : InverseLimit G f) ↦ x.val) := by
  continuity

section ToComponent

@[fun_prop, continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent G f i) := by
  rw [toComponent_def]
  have : (fun (z : InverseLimit G f) ↦ z.val i) = (fun y ↦ y i) ∘ (fun z ↦ z.val) := rfl
  rw [this]
  exact Continuous.comp (by fun_prop) (val_continuous ..)

end ToComponent

section Maps

@[fun_prop, continuity]
lemma lift_continuous (maps_cont : ∀ i, Continuous (maps i)) :
    Continuous (lift G f maps inverseSystemHom) := by
  rw [lift_def]
  fun_prop

end Maps

section TopologicalStructures

end TopologicalStructures

end InverseLimit
