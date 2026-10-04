/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
module

public import Tengoku
/-!

# Tensor product commutes with direct product when tensoring with a finite free module

If `M` is a finite free module and `Nᵢ` is an indexed collection of modules of a commutative ring
`R` then there is an `R`-module isomorphism between `M ⊗ ∏ᵢ Nᵢ` and `∏ᵢ (M ⊗ Nᵢ)`.

## Main definition

* `tensorPiEquivPiTensor` : `M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i)` for finite free modules
* `tensorPiEquivPiTensor'` : the same but for finitely-presented modules.

## TODO

Switch the names around because the primed version is more general hence better.

-/

@[expose] public section
open DirectSum Function

section

theorem Module.FinitePresentation.exists_fin_exact (R : Type*) (M : Type*)
  [Ring R] [AddCommGroup M] [Module R M] [fp : Module.FinitePresentation R M] :
  ∃ (n m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] M),
    Exact f g ∧ Surjective g := by
  obtain ⟨n, K, iso, S, hS⟩ := Module.FinitePresentation.exists_fin R M
  let m := S.card
  let gens : Fin m → (Fin n → R) := Subtype.val ∘ (Finset.equivFin S).symm
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R gens
  let g : (Fin n → R) →ₗ[R] M := iso.symm.toLinearMap.comp (Submodule.mkQ K)
  have h₁ : LinearMap.range f = K := by
    simp only [← hS, f, Fintype.range_linearCombination, gens, (Surjective.range_comp
      (Finset.equivFin S).symm.surjective Subtype.val), Subtype.range_val_subtype,
      Finset.setOfPred_mem]
  have h₂ : LinearMap.ker g = K := by
    simp only [g, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  have exact_fg : Exact f g := LinearMap.exact_iff.mpr (h₂.trans h₁.symm)
  have : Surjective g := by
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
      Submodule.mkQ_surjective]
  exact ⟨n, m, f, g, exact_fg, this⟩
end

section

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {R ι : Type*} [Semiring R]
  {M N : ι → ι' → Type*} [∀ i i', AddCommMonoid (M i i')] [∀ i i', AddCommMonoid (N i i')]
  [∀ i i', Module R (M i i')] [∀ i i', Module R (N i i')]

end

section

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

open TensorProduct

/-- The isomorphism `M ⊗ ∏ᵢ Nᵢ ≅ (B →₀ R) ⊗ ∏ᵢ Nᵢ`, where `M` is assumed free and
`B` is the basis of `M` given by Lean's global axiom-of-choice operator. This is an
auxiliary definition. -/
noncomputable def freeModuleTensorPiEquiv :
    M ⊗[R] (∀ i, N i) ≃ₗ[R] (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀ i, N i) :=
  TensorProduct.congr (Module.Free.chooseBasis R M).repr (LinearEquiv.refl R ((i : ι) → N i))

/-- The isomorphism `Πᵢ ((B →₀ R) ⊗ Nᵢ) ≅ Πᵢ (M ⊗ Nᵢ)` where `M` is assumed free and
`B` is the basis of `M` given by Lean's global axiom-of-choice operator. This is an
auxiliary definition. -/
noncomputable def tensorPiEquivFinitefreeModule :
    (Π i, (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) ≃ₗ[R] Π i, (M ⊗[R] N i) :=
  LinearEquiv.piCongrRight
    (fun i ↦ (LinearEquiv.rTensor (N i) (Module.Free.chooseBasis R M).repr.symm))

end

section

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [h : Module.FinitePresentation R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

end
