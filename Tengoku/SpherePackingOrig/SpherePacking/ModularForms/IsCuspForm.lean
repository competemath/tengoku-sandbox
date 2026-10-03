module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq
public import Tengoku.SpherePackingOrig.SpherePacking.ForMathlib.Cusps

/-!
# Cusp Forms

The predicate `IsCuspForm` and its basic properties.
-/

@[expose] public section

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups Manifold

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat CongruenceSubgroup Manifold

noncomputable section Definitions

variable {α ι : Type*}

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

def ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_cusps' := fun hc ↦ bdd_at_cusps f hc

lemma ModForm_mk_inj (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) (hf : f ≠ 0) :
  ModForm_mk _ _ f ≠ 0 := by
  rw [@DFunLike.ne_iff] at *
  obtain ⟨x, hx⟩ := hf
  use x
  simp only [zero_apply, ne_eq, ModForm_mk, zero_apply] at *
  exact hx

def CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k
  where
  toFun f := ModForm_mk Γ k f
  map_add' := by
    intro f g
    simp only [ModForm_mk, FunLike.coe_add]
    rfl
  map_smul' := by
    intro m f
    simp only [ModForm_mk, RingHom.id_apply]
    rfl

def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm_to_ModularForm Γ k)

def CuspForm_iso_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    CuspForm Γ k ≃ₗ[ℂ] CuspFormSubmodule Γ k := by
  apply LinearEquiv.ofInjective
  rw [@injective_iff_map_eq_zero]
  intro f hf
  rw [CuspForm_to_ModularForm] at hf
  simp only [ModForm_mk, LinearMap.coe_mk, AddHom.coe_mk] at hf
  ext z
  have := congr_fun (congr_arg (fun x => x.toFun) hf) z
  simpa using this

lemma mem_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : f ∈ CuspFormSubmodule Γ k) :
    ∃ g : CuspForm Γ k, f = CuspForm_to_ModularForm Γ k g := by
  rw [CuspFormSubmodule, LinearMap.mem_range] at hf
  aesop

instance (priority := 100) CuspFormSubmodule.funLike :
    FunLike (CuspFormSubmodule Γ k) ℍ ℂ where
  coe f := f.1.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f ∈ CuspFormSubmodule Γ k

/-- Build a `CuspForm` from a `SlashInvariantForm` that is holomorphic and tends to 0. -/
noncomputable def cuspFormOfSIFTendstoZero {k : ℤ}
    (f_SIF : SlashInvariantForm Γ(1) k)
    (h_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f_SIF.toFun)
    (h_zero : Tendsto f_SIF.toFun atImInfty (𝓝 0)) : CuspForm Γ(1) k where
  toSlashInvariantForm := f_SIF
  holo' := h_mdiff
  zero_at_cusps' hc := by
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    rw [f_SIF.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩]
    exact h_zero

private lemma isZeroAtImInfty_of_coeffZero {k : ℤ}
    (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) :
    IsZeroAtImInfty f := by
  rw [qExpansion_coeff] at h
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
  change Function.Periodic.cuspFunction (1 : ℝ) (⇑f ∘ ↑ofComplex) 0 = 0
    at h
  have ht := Function.Periodic.tendsto_nhds_zero
    (h := (1 : ℝ))
    (f := ⇑f ∘ ↑ofComplex)
    (ModularFormClass.analyticAt_cuspFunction_zero f Real.zero_lt_one (by simp)).continuousAt
  have ht0 : Tendsto
      (fun x ↦ (⇑f ∘ ↑ofComplex) (Function.Periodic.invQParam (1 : ℝ) x))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa [h] using ht
  have := (ht0.comp (Function.Periodic.qParam_tendsto (h := 1) Real.zero_lt_one)).comp
    tendsto_coe_atImInfty
  rw [IsZeroAtImInfty, ZeroAtFilter]
  apply this.congr'
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨⊤, univ_mem, fun y _ => ?_⟩
  simp only [comp_apply]
  obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period (h := 1)
    (Ne.symm (zero_ne_one' ℝ)) y
  have := (periodic_comp_ofComplex (h := 1) f (by simp)).int_mul m y
  simp only [comp_apply, ofReal_one, mul_one, ofComplex_apply] at *
  rwa [hm]

/-- Build a `CuspForm` from a modular form whose q-expansion has vanishing constant term. -/
noncomputable def cuspFormOfCoeffZero {k : ℤ}
    (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm Γ(1) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' hc := by
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    rw [f.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩]
    exact isZeroAtImInfty_of_coeffZero f h
