/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Tengoku
import Tengoku.Flt.FLT.Mathlib.RingTheory.TensorProduct.Pi

/-!
# Constructions

Material destined for Mathlib.
-/

@[expose] public section

open scoped TensorProduct

/-- Choice of an `R`-linear isomorphism `M ≃ R^(finrank R M)` for a finite free module `M` over a
ring `R` with the strong rank condition. -/
noncomputable def Module.Finite.equivPi (R M : Type*) [Ring R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    M ≃ₗ[R] Fin (Module.finrank R M) → R :=
  LinearEquiv.ofFinrankEq _ _ <| by rw [Module.finrank_pi, Fintype.card_fin]

/-- Base change of `Module.Finite.equivPi` to an `R`-algebra `N`: the equivalence
`N ⊗[R] M ≃ₗ[N] Fin (finrank R M) → N`. -/
noncomputable abbrev TensorProduct.AlgebraTensorModule.finiteEquivPi (R M N : Type*) [CommRing R]
    [CommSemiring N] [Ring M] [Algebra R N] [Module R M] [Module.Free R M] [Module.Finite R M]
    [StrongRankCondition R] :
    N ⊗[R] M ≃ₗ[N] Fin (Module.finrank R M) → N :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl N N) (Module.Finite.equivPi _ _)).trans
    (TensorProduct.piScalarRight _ _ _ _)
