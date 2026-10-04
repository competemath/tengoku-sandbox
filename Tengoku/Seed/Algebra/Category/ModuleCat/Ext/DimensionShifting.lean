/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Ext.HasExt
public import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
public import Tengoku.Seed.Data.Nat.Totient
public import Tengoku.Seed.Data.Rat.Floor
public import Tengoku.Seed.Tactic.Continuity

/-!

# Dimension Shifting

-/

public section

universe v u

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory Abelian

/-- The standard short complex `0 → N → P → M → 0` with `P= R^{⊕M}` free. -/
noncomputable abbrev ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr ℕ id).shortComplexKer

theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projectiveShortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

instance [Small.{v} R] (M : ModuleCat.{v} R) : Module.Free R M.projectiveShortComplex.X₂ :=
  Module.Free.finsupp R _ _

/-- The connection maps in the contravariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is projective. -/
theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) :=
  fun x ↦ Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

/-- The connection maps in the covariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is injective. -/
theorem postcomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : ℕ)
    [Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) :=
  fun x ↦ Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl
