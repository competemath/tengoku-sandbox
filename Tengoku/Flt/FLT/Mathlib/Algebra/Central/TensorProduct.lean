/-
Copyright (c) 2026 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import Tengoku

/-!
# Tensor Product

Material destined for Mathlib.
-/

@[expose] public section

open scoped TensorProduct

@[simp]
lemma Subalgebra.sup_includeLeft_includeRight_eq_top
    {k A B : Type*} [CommSemiring k]
    [Semiring A] [Algebra k A] [Semiring B] [Algebra k B] :
    Algebra.TensorProduct.includeLeft.range ⊔ Algebra.TensorProduct.includeRight.range
    = (⊤ : Subalgebra k (A ⊗[k] B)) := by
  ext x
  simp only [Algebra.mem_top, iff_true]
  refine TensorProduct.induction_on x (by simp) (fun a b ↦ ?_) (fun _ _ ↦ AddMemClass.add_mem)
  have : a ⊗ₜ[k] b = a ⊗ₜ[k] 1 * 1 ⊗ₜ[k] b := by simp
  rw [this]
  exact Subalgebra.mul_mem _
    (Algebra.mem_sup_left <| Set.mem_range_self _)
    (Algebra.mem_sup_right <| Set.mem_range_self _)

lemma Submodule.tensorProduct_inf_eq_range_map
    {k : Type*} [Field k]
    {A B : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (S : Submodule k A) (T : Submodule k B) :
    LinearMap.range (TensorProduct.map S.subtype LinearMap.id) ⊓
    LinearMap.range (TensorProduct.map LinearMap.id T.subtype) =
    LinearMap.range (TensorProduct.map S.subtype T.subtype) := by
  refine le_antisymm ?_
    (le_inf (TensorProduct.range_map_mono le_rfl (by simp))
      (TensorProduct.range_map_mono (by simp) le_rfl))
  rintro x ⟨⟨u, hux⟩, ⟨v, hvx⟩⟩
  let qS := S.projectionOnto S.exists_isCompl.choose S.exists_isCompl.choose_spec
  let qT := T.projectionOnto T.exists_isCompl.choose T.exists_isCompl.choose_spec
  have hxS : TensorProduct.map (S.subtype.comp qS) LinearMap.id x = x := by
    rw [← hux]
    exact TensorProduct.induction_on u (by simp)
      (fun _ _ ↦ by simp_all [qS]) (fun _ _ ↦ by simp_all)
  have hxT : TensorProduct.map LinearMap.id (T.subtype.comp qT) x = x := by
    rw [← hvx]
    exact TensorProduct.induction_on v (by simp)
      (fun _ _ ↦ by simp_all [qT]) (fun _ _ ↦ by simp_all)
  have hxST : TensorProduct.map (S.subtype.comp qS) (T.subtype.comp qT) x = x := by
    conv_rhs => rw [← hxS, ← hxT]
    simp [← TensorProduct.map_comp, ← LinearMap.comp_apply]
  use TensorProduct.map qS qT x;
  simpa [← TensorProduct.map_comp, ← LinearMap.comp_apply] using hxST
