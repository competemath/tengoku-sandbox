module

public import Tengoku.Apap.APAP.Mathlib.LinearAlgebra.Dimension.Finrank
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

public section

open scoped Finset

variable {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Finset ι} {f : ι → V →ₗ[K] K}

namespace Module

lemma codim_iInf_ker_le_fintypeCard [Fintype ι] :
    finrank K V - (⨅ i, (f i).ker).finrank ≤ Fintype.card ι := by
  let F : V →ₗ[K] (ι → K) := {
    toFun x i := f i x
    map_add' x y := by ext i; simp
    map_smul' c x := by ext i; simp
  }
  have hker : F.ker = ⨅ i, (f i).ker := by ext x; simp [F, funext_iff]
  grw [← hker, ← F.finrank_range_add_finrank_ker, Submodule.finrank_le]
  simp [Submodule.finrank]

lemma codim_biInf_ker_le_finsetCard : finrank K V - (⨅ i ∈ s, (f i).ker).finrank ≤ #s := by
  simpa [iInf_subtype] using codim_iInf_ker_le_fintypeCard (ι := s) (f := fun i ↦ f i)

end Module
