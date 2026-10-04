--import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Tengoku

/- !

# Index of modules over PIDs

For a finite and free module over a PID, we define the index of a submodule and prove
some of its properties.

## Main Definitions:
- `Submodule.indexPID`: The index of a submodule.

## Main Results:
- `Submodule.eq_top_of_index_isUnit` : if the index is a unit, then the submodule is maximal.
- `prod_moduleSmithCoeffs_associated_index` : The index is associated to the product of the Smith
  coefficients corresponding to the inclusion map.
- `Submodule.prime_dvd_index` : a consequence of a prime dividing the index of a submodule.
- `indexPID_eq_index_int` : in the case of `ℤ`-modules, the absolute value of the index is equal to
  the cardinality of the quotient.

## Notes
- For some of the results, we closely followed an approach
  adapted from the proofs involving quotients by ideals such as
  `Ideal.quotientEquivPiZMod`.  -/

open scoped BigOperators

open scoped Classical

open Module

/- Here we prove that the quotient of free `ℤ`-modules of the same rank is finite· The proof
is essentially the same as that of `Ideal.quotientEquivDirectSum`, which was written by Anne Baanen.
-/
variable {ι ι' R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

variable [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι] [Fintype ι']

/-- For `N` a submodule of a free and finite module `M` of the same rank,
  we extract a basis for `N` of cardinality the rank of `M`-/
noncomputable def Submodule.basisOfPID_of_eq_rank  (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
    (heq : Module.rank R M = Module.rank R N) : Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex R M))) R N := by
  let B := Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))
  obtain ⟨n,b⟩ :=  Submodule.basisOfPid B N
  rw [rank_eq_card_basis (Module.Free.chooseBasis R M), rank_eq_card_basis b, Nat.cast_inj, Fintype.card_fin] at heq
  rw [← heq] at b
  exact b

noncomputable def Submodule.indexPID_aux (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
    (heq : Module.rank R M = Module.rank R N) : R := by
  let B := Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))
  exact ((LinearMap.toMatrix (Submodule.basisOfPID_of_eq_rank N heq) B (Submodule.subtype N)).det)

/-- Auxiliary definition: for `N` a submodule of `M` of the same rank,
  the determinant of the matrix representing the inclusion map `N → M` with
  respect to some choice of bases.  -/
lemma Submodule.indexPID_aux_def (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
    (heq : Module.rank R M = Module.rank R N) : Submodule.indexPID_aux N heq =
  (LinearMap.toMatrix (Submodule.basisOfPID_of_eq_rank N heq)
  (Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin (Module.Free.ChooseBasisIndex R M)))
  (Submodule.subtype N)).det := rfl

/-- The index `[M : N]` of `N` in `M` as an element in `R`. -/
noncomputable def Submodule.indexPID (N : Submodule R M) [Module.Free R M][Module.Finite R M] : R :=
 if heq : Module.rank R M = Module.rank R N then (Submodule.indexPID_aux N heq) else 0

lemma Submodule.eq_top_of_index_isUnit  (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
   (hu : IsUnit (Submodule.indexPID N)) : N = ⊤ := by
  have heq : Module.rank R M = Module.rank R N := by
    by_contra hc
    have : Submodule.indexPID N = 0 := by
      unfold Submodule.indexPID
      simp only [dite_false, hc]
    rw [this] at hu
    simp only [isUnit_zero_iff, zero_ne_one] at hu
  unfold Submodule.indexPID at hu
  simp only [heq, dite_true, Submodule.indexPID_aux_def] at hu
  rw [Submodule.eq_top_iff']
  intro x
  have aux : (LinearEquiv.ofIsUnitDet hu) ((LinearEquiv.ofIsUnitDet hu).symm x) =
    ((LinearEquiv.ofIsUnitDet hu).symm x).1 := by
    simp only [LinearEquiv.ofIsUnitDet_symm_apply, LinearEquiv.ofIsUnitDet_apply, coe_subtype]
  rw [← LinearEquiv.apply_symm_apply (LinearEquiv.ofIsUnitDet hu) x, aux]
  simp only [LinearEquiv.ofIsUnitDet_symm_apply, SetLike.coe_mem]

omit [IsDomain R] [IsPrincipalIdealRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]

/- Version of `Submodule.smithNormalFormTopBasis` which takes two bases as input instead of a
  proof of equalities of ranks. -/
noncomputable def smithBasisModule (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    Basis ι R M := by
    refine Submodule.smithNormalFormTopBasis b (N := N) ?_
    rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b2]

    --(module_exists_smith_normal_form N b b2).choose

/-- Version of `Submodule.smithNormalFormCoeffs` which takes two bases as input instead of a
  proof of equalities of ranks.  -/
noncomputable def moduleSmithCoeffs (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    ι → R := by
  refine Submodule.smithNormalFormCoeffs b (N := N) ?_
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b2]

noncomputable def moduleSmithSubmodule (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    Basis ι R N := by
  refine Submodule.smithNormalFormBotBasis b (N := N) ?_
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b2]

@[simp]
theorem smith_coeffs_property (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    ∀ i,  (moduleSmithSubmodule N b b2 i : M) =
    moduleSmithCoeffs N b b2 i • smithBasisModule N b b2 i := Submodule.smithNormalFormBotBasis_def b _

theorem moduleSmithCoeffs_ne_zero (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    ∀ i, moduleSmithCoeffs N b b2 i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b _

/-- If `N` is a proper submodule of `M`, then at least one of the smith coefficients is not a unit. -/
lemma moduleSmithCoeff_ne_unit (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N)
    (hneq : N ≠ ⊤) : ∃ i, ¬ (IsUnit (moduleSmithCoeffs N b b2 i)) := by
  by_contra h
  push Not at h
  have : ⊤ ≤ N := by
    intro x _
    set c := λ i => (IsUnit.exists_right_inv (h i)).choose with hc
    have aux : ∀ i, c i • (moduleSmithSubmodule N b b2 i : M) = smithBasisModule N b b2 i := by
      intro i
      rw [smith_coeffs_property, ← mul_smul, mul_comm, hc,
        ((IsUnit.exists_right_inv (h i)).choose_spec), one_smul]
    have := Basis.sum_repr (smithBasisModule N b b2) x
    simp_rw [← aux] at this
    set y : N := ∑ i : ι , (((smithBasisModule N b b2).repr x) i) •
      (c i • (moduleSmithSubmodule N b b2 i)) with hy
    have : y.1 = x := by
      rw [← this, hy]
      norm_cast
    rw [← this]
    exact y.2
  exact hneq (top_le_iff.1 this)
