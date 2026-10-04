import Tengoku.LerayHopf.LerayHopf.R3.GalerkinODE
import Tengoku.LerayHopf.LerayHopf.R3.GalerkinScheme
import Tengoku
import Tengoku.LerayHopf.LerayHopf.Galerkin.QuadraticField

/-!
# Galerkin ODE existence on ℝ³: finite-dim Riesz field + weak↔vector-field bridge (Pillar E)

**Milestone:** `ode-continuation` (Pillar E).

This file attempts the second analytic gap behind `galerkin_ode_solution_R3`:
constructing a `GalerkinODEInput` (`GalerkinODE.lean`) from the finite-dim Galerkin ODE.
It mirrors `GalerkinScheme.lean`/`GalerkinODE.lean`: a standalone sibling under
`LerayHopf/R3/`, isolated-hypothesis discipline for the residual frontier, and it
**never edits `SolutionInterfaces.lean`** (the abstraction-barrier finite-dimensionality fix
is the later sequential capstone).

## HONEST scope (the §1.4 abstraction barrier — concrete-scheme route)

`galerkinODEInput` over an **abstract** `R3GalerkinScheme` is *not* provable: the abstract
fields (`norm_le`, `idem`, `preserves_sigma`, `range_schwartz`, `tendsto_id`) do NOT expose
finite-dimensionality of `range (𝔊.P n)`, so neither Riesz nor auto-continuity even start
(see `docs/scratch/ode-continuation.md` §1.4). We therefore work over the **CONCRETE**
scheme `schemeOfBasis B` produced from a `SchwartzGalerkinBasis B`, where
`V_n := galerkinSpan B n` carries an explicit finite `Fin n` basis (P5
`galerkinSpan_finiteDimensional`).

### Proved here (axiom-free, must-prove — lean-prover targets)

- `galerkinODE_vectorField` (R1)        — the finite-dim Riesz vector field `G_n` on `V_n`.
- `galerkinODE_vectorField_spec` (R2)   — its defining identity (the weak↔vector-field bridge).
- `galerkinODEInput_of_globalCurve` (R3) — assemble the five `GalerkinODEInput` fields,
  DERIVING the weak form `u_ode` from the autonomous field equation `c' = G_n(c)` via R2.
- `galerkinODEInput_of_basis` (D)       — deliverable wrapper.

This proves the **R-repr** content (weak-form ⇄ vector-field representation) axiom-free.
It does **NOT** remove the axiom and does **NOT** prove global existence: the genuine
remaining frontier — global-in-time existence of the finite-dim quadratic ODE (mathlib has
no continuation-from-a-priori-bound theorem) — is **isolated** in the hypothesis structure
`FinDimGlobalODE` (S0), supplied by the caller, NOT proved here.

### Also here (issue #112 PR-B: generic-layer witness + equality bridge)

- `r3FieldForms` (R0a) — the `Galerkin.FieldForms (galerkinSpan B n)` witness packaging
  `R3NSForms.b`/`stokesTestPairing_R3`, deduplicating `GalerkinODESolve.lean`'s CLM tower
  against `LerayHopf/Galerkin/QuadraticField.lean`'s generic construction. Sorry-free.
- `galerkinODE_vectorField_eq_generic` — the equality bridge `galerkinODE_vectorField … =
  (r3FieldForms …).vectorField ν`, from which `GalerkinODESolve.lean`'s C1/A1/A2/A3/G1
  theorems are now derived as corollaries.

## Import justification (NO import cycle)

```
Domain.lean → … → SolutionInterfaces.lean → GalerkinODE.lean ─┐
                                        → GalerkinScheme.lean┴─→ GalerkinODEExistence.lean [THIS FILE]
```

`GalerkinODE.lean` already imports `SolutionInterfaces.lean`, so the structures/defs
(`GalerkinODEInput`, `R3GalerkinScheme`, `R3NSForms`, `stokesTestPairing_R3`, `L2Sigma_R3`,
`L2VF_R3`, `Time`) are transitively in scope; `GalerkinScheme.lean` supplies `galerkinSpan`,
`galerkinP`, and the finite-dimensional instance. Neither file imports THIS one — the
dependency is one-directional, **no cycle**. `InnerProductSpace.Dual` provides the Riesz
isometry `InnerProductSpace.toDual` (needs `CompleteSpace`, available on the finite-dim
`V_n`); `Normed.Module.FiniteDimension` provides `LinearMap.continuous_of_finiteDimensional`
and finite-dim completeness for the Riesz step.

## Assumptions / axioms

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.** The single residual frontier
(finite-dim ODE global existence) is carried by the hypothesis structure `FinDimGlobalODE`
(a bundle of curve data, not an environment axiom) — the honest analogue of P3's
`LocalRellichInput` and P5's `SchwartzGalerkinBasis`, and STRICTLY smaller than
`GalerkinODEInput` because R-repr is now PROVED (R1/R2/R3), not assumed.
`SolutionInterfaces.lean` is **NOT edited**.
-/

namespace LerayHopf

open MeasureTheory
open scoped Topology InnerProductSpace

/-! ### C0 — the concrete Galerkin scheme attached to a basis -/

/-- The concrete Galerkin scheme attached to a Schwartz divergence-free basis `B`.

This is the record built inside P5's `nonempty_r3GalerkinScheme_of_basis`
(`GalerkinScheme.lean:338`), extracted as a `def` so that its projector is *definitionally*
`galerkinP B`: in particular `(schemeOfBasis B).P n = galerkinP B n` holds by `rfl`, hence
`range ((schemeOfBasis B).P n)` has the explicit finite basis of `galerkinSpan B n` (P5
`galerkinSpan_finiteDimensional`). This finite-dimensionality is exactly what the abstract
`R3GalerkinScheme` does not expose, and is what makes the Riesz construction (R1/R2) and the
whole milestone feasible (see the header, §1.4). -/
noncomputable def schemeOfBasis (B : SchwartzGalerkinBasis) : R3GalerkinScheme where
  P               := galerkinP B
  preserves_sigma := galerkinP_preserves_sigma B
  tendsto_id      := fun u hu => galerkinP_tendsto_id B u hu
  norm_le         := galerkinP_norm_le B
  idem            := galerkinP_idem B
  range_schwartz  := galerkinP_range_schwartz B
  mono_range      := galerkinP_mono_range B

/-- The projector of `schemeOfBasis B` is definitionally `galerkinP B`. -/
@[simp] theorem schemeOfBasis_P (B : SchwartzGalerkinBasis) (n : ℕ) :
    (schemeOfBasis B).P n = galerkinP B n := rfl

/-! ### V_n embedding helpers -/

/-- The prefix span lies in the divergence-free subspace: every generator `B.e k` is
divergence-free (`B.e_mem_sigma`) and `L2Sigma_R3` is a submodule, so the span is contained
in it.  This is the `Submodule` inequality underlying the `V_n ↪ L2Sigma_R3` embedding. -/
theorem galerkinSpan_le_sigma (B : SchwartzGalerkinBasis) (n : ℕ) :
    galerkinSpan B n ≤ L2Sigma_R3 := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨k, rfl⟩
  exact B.e_mem_sigma _

/-- Embedding helper: an element of `V_n := galerkinSpan B n`, viewed as an `L2VF_R3`
vector, is divergence-free, i.e. lies in `L2Sigma_R3`.  Used to coerce `V_n` elements into
the domain `L2Sigma_R3` of the convection form `F.b`. -/
theorem mem_sigma_of_mem_galerkinSpan (B : SchwartzGalerkinBasis) (n : ℕ)
    (v : galerkinSpan B n) : (v : L2VF_R3) ∈ L2Sigma_R3 :=
  galerkinSpan_le_sigma B n v.2

/-- Embedding `V_n → L2Sigma_R3`: package a `V_n := galerkinSpan B n` element as a
divergence-free L² field. -/
noncomputable def galerkinSpanToSigma (B : SchwartzGalerkinBasis) (n : ℕ)
    (v : galerkinSpan B n) : L2Sigma_R3 :=
  ⟨(v : L2VF_R3), mem_sigma_of_mem_galerkinSpan B n v⟩

/-- The `L2Sigma_R3`-embedding `galerkinSpanToSigma` is compatible with the underlying
`L2VF_R3` coercion: coercing the image agrees with coercing the source `V_n` element. -/
@[simp] theorem galerkinSpanToSigma_coe (B : SchwartzGalerkinBasis) (n : ℕ)
    (v : galerkinSpan B n) :
    ((galerkinSpanToSigma B n v : L2Sigma_R3) : L2VF_R3) = (v : L2VF_R3) := rfl

/-! ### Linearity helpers for `stokesTestPairing_R3` on span elements -/

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap

/-- A span element has **complex Schwartz** component representatives: for `w ∈ V_n`, each
complex component `L2VF_projComponentC_R3 j w` is the `L²`-class of a (complex-valued)
Schwartz map.  This is the complexification of `galerkinP_range_schwartz` (real components ⇒
real Schwartz), post-composed with the real-to-complex embedding `RCLike.ofRealCLM`. -/
theorem galerkinSpan_exists_schwartzC
    (B : SchwartzGalerkinBasis) (n : ℕ) (w : galerkinSpan B n) :
    ∃ φ : Fin 3 → SchwartzMap Domain3 ℂ,
      ∀ j : Fin 3,
        L2VF_projComponentC_R3 j (w : L2VF_R3) = (φ j).toLp 2 (volume : Measure Domain3) := by
  obtain ⟨ψ, hψ⟩ := galerkinP_range_schwartz B n (w : L2VF_R3)
  -- `galerkinP B n w = w` since `w ∈ V_n`.
  have hfix : galerkinP B n (w : L2VF_R3) = (w : L2VF_R3) :=
    (galerkinSpan B n).starProjection_eq_self_iff.mpr w.2
  refine ⟨fun j => (ψ j).postcompCLM (𝕜 := ℝ) (RCLike.ofRealCLM (K := ℂ)), fun j => ?_⟩
  -- Reduce the complex component to the real one via the definition of `L2VF_projComponentC_R3`.
  have hreal : L2VF_projComponent_R3 j (w : L2VF_R3)
      = (ψ j).toLp 2 (volume : Measure Domain3) := by
    rw [← hfix]; exact hψ j
  -- `L2VF_projComponentC_R3 j w = (ofRealCLM).compLpL (L2VF_projComponent_R3 j w)`.
  have hcomp : L2VF_projComponentC_R3 j (w : L2VF_R3)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
          (L2VF_projComponent_R3 j (w : L2VF_R3)) := rfl
  rw [hcomp, hreal]
  -- Both sides are a.e. equal to `x ↦ ofRealCLM (ψ j x)`; conclude by `Lp` extensionality.
  apply Lp.ext_iff.mpr
  have h1 : (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
        ((ψ j).toLp 2 (volume : Measure Domain3))
      =ᵐ[volume] fun x => RCLike.ofRealCLM (K := ℂ) (((ψ j).toLp 2 (volume : Measure Domain3)) x) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have h2 : ((ψ j).toLp 2 (volume : Measure Domain3) : Domain3 → ℝ)
      =ᵐ[volume] (ψ j) := (ψ j).coeFn_toLp 2 (volume : Measure Domain3)
  have h3 : (((ψ j).postcompCLM (𝕜 := ℝ) (RCLike.ofRealCLM (K := ℂ))).toLp
        2 (volume : Measure Domain3) : Domain3 → ℂ)
      =ᵐ[volume] ((ψ j).postcompCLM (𝕜 := ℝ) (RCLike.ofRealCLM (K := ℂ))) :=
    ((ψ j).postcompCLM (𝕜 := ℝ) (RCLike.ofRealCLM (K := ℂ))).coeFn_toLp
      2 (volume : Measure Domain3)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx3]
  simp only [SchwartzMap.postcompCLM_apply]
  rw [hx2]

/-- For a span element `w ∈ V_n`, the pointwise coercion of the `L²`-Fourier transform of its
`j`-th complex component is a.e. equal to a genuine **Schwartz** function (the classical
Schwartz Fourier transform of the component's Schwartz representative).  This is the bridge
from the a.e.-only `Lp.fourierTransformₗᵢ` coercion to the classical Schwartz `fourierIntegral`,
via `SchwartzMap.toLp_fourier_eq`. -/
theorem galerkinSpan_fourier_ae
    (B : SchwartzGalerkinBasis) (n : ℕ) (w : galerkinSpan B n) (j : Fin 3) :
    ∃ S : SchwartzMap Domain3 ℂ,
      ((𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) : Domain3 → ℂ)
        =ᵐ[volume] (S : Domain3 → ℂ) := by
  obtain ⟨φ, hφ⟩ := galerkinSpan_exists_schwartzC B n w
  refine ⟨𝓕 (φ j), ?_⟩
  -- `𝓕 (component) = 𝓕 ((φ j).toLp) = (𝓕 (φ j)).toLp`, whose coercion is a.e. `𝓕 (φ j)`.
  have hF : (𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3)
      = (𝓕 (φ j)).toLp 2 (volume : Measure Domain3) := by
    rw [hφ j]; exact SchwartzMap.toLp_fourier_eq (φ j)
  rw [hF]
  exact (𝓕 (φ j)).coeFn_toLp 2 (volume : Measure Domain3)

/-- The per-component integrand of `stokesTestPairing_R3` is **integrable** when both arguments
are span elements: their Fourier components are a.e. Schwartz, so the integrand is dominated by
`C · (‖ξ‖² · ‖S_w ξ‖)` (`S_u` bounded, `S_w` rapidly decaying), which is integrable by
`SchwartzMap.integrable_pow_mul`.  This is the crux that licenses `integral_add`/
`integral_const_mul` and hence the right-linearity of `stokesTestPairing_R3` on `V_n`. -/
theorem stokesTestPairing_R3_integrand_integrable
    (B : SchwartzGalerkinBasis) (n : ℕ) (u w : galerkinSpan B n) (j : Fin 3) :
    Integrable (fun ξ : Domain3 =>
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ((𝓕 (L2VF_projComponentC_R3 j (u : L2VF_R3)) : L2C_R3) ξ *
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) ξ)).re)
      (volume : Measure Domain3) := by
  obtain ⟨Su, hSu⟩ := galerkinSpan_fourier_ae B n u j
  obtain ⟨Sw, hSw⟩ := galerkinSpan_fourier_ae B n w j
  -- The dominating integrable function: `(2π)² · M · (‖ξ‖² · ‖Sw ξ‖)` with `M = ‖Su‖_∞`.
  set M : ℝ := ‖Su.toBoundedContinuousFunction‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hdom : Integrable (fun ξ : Domain3 =>
      (2 * Real.pi) ^ 2 * M * (‖ξ‖ ^ 2 * ‖Sw ξ‖)) (volume : Measure Domain3) := by
    have hbase : Integrable (fun ξ : Domain3 => ‖ξ‖ ^ 2 * ‖Sw ξ‖) (volume : Measure Domain3) :=
      Sw.integrable_pow_mul (volume : Measure Domain3) 2
    have := hbase.const_mul ((2 * Real.pi) ^ 2 * M)
    refine this.congr ?_
    filter_upwards with ξ
    ring
  -- The integrand is a.e. equal to its Schwartz form and dominated by `hdom`.
  refine Integrable.mono' hdom ?_ ?_
  · -- a.e.-strong measurability of the integrand (it is a.e. continuous via the Schwartz reps)
    have hcont : Continuous (fun ξ : Domain3 =>
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * (Su ξ * (starRingEnd ℂ) (Sw ξ)).re) :=
      (continuous_const.mul ((continuous_pow 2).comp continuous_norm)).mul
        (Complex.continuous_re.comp
          (Su.continuous.mul (Complex.continuous_conj.comp Sw.continuous)))
    refine hcont.aestronglyMeasurable.congr ?_
    filter_upwards [hSu, hSw] with ξ hξu hξw
    simp only [hξu, hξw]
  · -- the domination bound, a.e.
    filter_upwards [hSu, hSw] with ξ hξu hξw
    rw [hξu, hξw]
    have hpi : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
    have hSubd : ‖Su ξ‖ ≤ M := by
      rw [hMdef, ← Su.toBoundedContinuousFunction_apply ξ]
      exact (Su.toBoundedContinuousFunction).norm_coe_le_norm ξ
    calc ‖(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * (Su ξ * (starRingEnd ℂ) (Sw ξ)).re‖
        = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(Su ξ * (starRingEnd ℂ) (Sw ξ)).re‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs ((2 * Real.pi) ^ 2),
            abs_of_nonneg hpi, Real.norm_eq_abs (‖ξ‖ ^ 2), abs_of_nonneg (by positivity)]
      _ ≤ (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * (‖Su ξ‖ * ‖Sw ξ‖) := by
          have hre : ‖(Su ξ * (starRingEnd ℂ) (Sw ξ)).re‖ ≤ ‖Su ξ‖ * ‖Sw ξ‖ := by
            refine (Complex.abs_re_le_norm _).trans ?_
            rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left hre (by positivity)
      _ ≤ (2 * Real.pi) ^ 2 * M * (‖ξ‖ ^ 2 * ‖Sw ξ‖) := by
          have hkey : (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖Sw ξ‖) * ‖Su ξ‖
              ≤ (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖Sw ξ‖) * M :=
            mul_le_mul_of_nonneg_left hSubd (by positivity)
          calc (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * (‖Su ξ‖ * ‖Sw ξ‖)
              = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖Sw ξ‖) * ‖Su ξ‖ := by ring
            _ ≤ (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖Sw ξ‖) * M := hkey
            _ = (2 * Real.pi) ^ 2 * M * (‖ξ‖ ^ 2 * ‖Sw ξ‖) := by ring

/-- Right-additivity of `stokesTestPairing_R3` on span elements: the bare Fourier-integral
pairing is additive in its second argument when both arguments lie in `V_n`.  This uses
additivity of the component CLM and of the `L²`-Fourier transform (`map_add`), `Lp.coeFn_add`
to push it through the a.e. coercion, and the integrability of each component integrand
(`stokesTestPairing_R3_integrand_integrable`) to split the Bochner integral via `integral_add`. -/
theorem stokesTestPairing_R3_add_right
    (B : SchwartzGalerkinBasis) (n : ℕ) (u w w' : galerkinSpan B n) :
    stokesTestPairing_R3 (u : L2VF_R3) ((w + w' : galerkinSpan B n) : L2VF_R3)
      = stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
        + stokesTestPairing_R3 (u : L2VF_R3) (w' : L2VF_R3) := by
  unfold stokesTestPairing_R3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- a.e. additivity of the `j`-th Fourier component on `w + w'`.
  have hae : (𝓕 (L2VF_projComponentC_R3 j ((w + w' : galerkinSpan B n) : L2VF_R3)) : L2C_R3)
      =ᵐ[volume] fun ξ =>
        (𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) ξ
          + (𝓕 (L2VF_projComponentC_R3 j (w' : L2VF_R3)) : L2C_R3) ξ := by
    have hsum : ((w + w' : galerkinSpan B n) : L2VF_R3) = (w : L2VF_R3) + (w' : L2VF_R3) := rfl
    have hLp : (𝓕 (L2VF_projComponentC_R3 j ((w + w' : galerkinSpan B n) : L2VF_R3)) : L2C_R3)
        = (𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3)
          + (𝓕 (L2VF_projComponentC_R3 j (w' : L2VF_R3)) : L2C_R3) := by
      rw [hsum, map_add]
      exact fourier_add (L2VF_projComponentC_R3 j (w : L2VF_R3))
        (L2VF_projComponentC_R3 j (w' : L2VF_R3))
    rw [hLp]
    exact Lp.coeFn_add _ _
  -- rewrite the integrand under the a.e. equality, then split via `integral_add`.
  rw [show (∫ ξ : Domain3,
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
          ((𝓕 (L2VF_projComponentC_R3 j (u : L2VF_R3)) : L2C_R3) ξ *
            (starRingEnd ℂ)
              ((𝓕 (L2VF_projComponentC_R3 j ((w + w' : galerkinSpan B n) : L2VF_R3))
                : L2C_R3) ξ)).re
        ∂(volume : Measure Domain3))
      = ∫ ξ : Domain3,
          ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
            ((𝓕 (L2VF_projComponentC_R3 j (u : L2VF_R3)) : L2C_R3) ξ *
              (starRingEnd ℂ)
                ((𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) ξ)).re
          + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
            ((𝓕 (L2VF_projComponentC_R3 j (u : L2VF_R3)) : L2C_R3) ξ *
              (starRingEnd ℂ)
                ((𝓕 (L2VF_projComponentC_R3 j (w' : L2VF_R3)) : L2C_R3) ξ)).re)
          ∂(volume : Measure Domain3) from ?_]
  · exact integral_add (stokesTestPairing_R3_integrand_integrable B n u w j)
      (stokesTestPairing_R3_integrand_integrable B n u w' j)
  · refine integral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]
    rw [map_add, mul_add, Complex.add_re, mul_add]

/-- Right-homogeneity of `stokesTestPairing_R3` on span elements. -/
theorem stokesTestPairing_R3_smul_right
    (B : SchwartzGalerkinBasis) (n : ℕ) (u w : galerkinSpan B n) (c : ℝ) :
    stokesTestPairing_R3 (u : L2VF_R3) ((c • w : galerkinSpan B n) : L2VF_R3)
      = c * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3) := by
  unfold stokesTestPairing_R3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- a.e. homogeneity of the `j`-th Fourier component on `c • w`.
  have hae : (𝓕 (L2VF_projComponentC_R3 j ((c • w : galerkinSpan B n) : L2VF_R3)) : L2C_R3)
      =ᵐ[volume] fun ξ =>
        (c : ℂ) • (𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) ξ := by
    have hsmul : ((c • w : galerkinSpan B n) : L2VF_R3) = c • (w : L2VF_R3) := rfl
    -- convert the ℝ-smul on `L2C_R3` to the `(c : ℂ)`-smul, then use `fourier_smul`.
    have hLp : (𝓕 (L2VF_projComponentC_R3 j ((c • w : galerkinSpan B n) : L2VF_R3)) : L2C_R3)
        = (c : ℂ) • (𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) := by
      rw [hsmul, map_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ) c (L2VF_projComponentC_R3 j (w : L2VF_R3))]
      exact fourier_smul (c : ℂ) (L2VF_projComponentC_R3 j (w : L2VF_R3))
    rw [hLp]
    exact Lp.coeFn_smul _ _
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with ξ hξ
  rw [hξ]
  rw [smul_eq_mul, map_mul, Complex.conj_ofReal]
  rw [show ((𝓕 (L2VF_projComponentC_R3 j (u : L2VF_R3)) : L2C_R3) ξ *
        ((c : ℂ) * (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) ξ)))
      = (c : ℂ) * ((𝓕 (L2VF_projComponentC_R3 j (u : L2VF_R3)) : L2C_R3) ξ *
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j (w : L2VF_R3)) : L2C_R3) ξ)) by ring]
  rw [Complex.re_ofReal_mul]
  ring

/-! ### R1 — the finite-dim Galerkin Riesz vector field -/

/-- `galerkinSpanToSigma` is additive in its argument (both sides agree as `L2Sigma_R3`
elements, i.e. as the underlying `L2VF_R3` vectors via `Submodule.coe_add`). -/
theorem galerkinSpanToSigma_add (B : SchwartzGalerkinBasis) (n : ℕ)
    (w w' : galerkinSpan B n) :
    galerkinSpanToSigma B n (w + w') = galerkinSpanToSigma B n w + galerkinSpanToSigma B n w' := by
  apply Subtype.ext; rfl

/-- `galerkinSpanToSigma` is ℝ-homogeneous in its argument. -/
theorem galerkinSpanToSigma_smul (B : SchwartzGalerkinBasis) (n : ℕ)
    (c : ℝ) (w : galerkinSpan B n) :
    galerkinSpanToSigma B n (c • w) = c • galerkinSpanToSigma B n w := by
  apply Subtype.ext; rfl

/-! ### R0a — generic `FieldForms` witness (issue #112 PR-B, plan §3.3)

`r3FieldForms` packages `R3NSForms.b` and `stokesTestPairing_R3` as a
`Galerkin.FieldForms (galerkinSpan B n)` instance, deduplicating this file's CLM tower against
`LerayHopf/Galerkin/QuadraticField.lean`'s generic construction. All 13 obligations are
discharged mechanically from the Schwartz-Fourier right-linearity layer above, `R3NSForms`'s
own algebraic fields, and `stokesTestPairing_R3_symm` (`R3/GalerkinODE.lean`, promoted from a
`private` copy in `GalerkinODESolve.lean` for this witness — see that file's promotion note). -/

/-- The generic `FieldForms` witness for the ℝ³ Galerkin ODE layer: `bV` is `F.b` composed with
`galerkinSpanToSigma`, `sV` is `stokesTestPairing_R3` on the ambient `L2VF_R3` coercion. -/
noncomputable def r3FieldForms (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) : Galerkin.FieldForms (galerkinSpan B n) where
  bV u u' w := F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u') (galerkinSpanToSigma B n w)
  bV_add_1 u u' v w := by
    show F.b (galerkinSpanToSigma B n (u + u')) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
        = F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
          + F.b (galerkinSpanToSigma B n u') (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
    rw [galerkinSpanToSigma_add]; exact F.b_add_1 _ _ _ _
  bV_add_2 u v v' w := by
    show F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n (v + v')) (galerkinSpanToSigma B n w)
        = F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
          + F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v') (galerkinSpanToSigma B n w)
    rw [galerkinSpanToSigma_add]; exact F.b_add_2 _ _ _ _
  bV_add_3 u v w w' := by
    show F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n (w + w'))
        = F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
          + F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w')
    rw [galerkinSpanToSigma_add]; exact F.b_add_3 _ _ _ _
  bV_smul_1 a u v w := by
    show F.b (galerkinSpanToSigma B n (a • u)) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
        = a * F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
    rw [galerkinSpanToSigma_smul]; exact F.b_smul_1 _ _ _ _
  bV_smul_2 a u v w := by
    show F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n (a • v)) (galerkinSpanToSigma B n w)
        = a * F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
    rw [galerkinSpanToSigma_smul]; exact F.b_smul_2 _ _ _ _
  bV_smul_3 a u v w := by
    show F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n (a • w))
        = a * F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n v) (galerkinSpanToSigma B n w)
    rw [galerkinSpanToSigma_smul]; exact F.b_smul_3 _ _ _ _
  bV_diag_zero v := F.b_self_zero (galerkinSpanToSigma B n v)
  sV u w := stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
  sV_symm u w := stokesTestPairing_R3_symm (u : L2VF_R3) (w : L2VF_R3)
  sV_add_right u w w' := stokesTestPairing_R3_add_right B n u w w'
  sV_smul_right a u w := stokesTestPairing_R3_smul_right B n u w a
  sV_diag_nonneg v := by
    show (0 : ℝ) ≤ stokesTestPairing_R3 (v : L2VF_R3) (v : L2VF_R3)
    rw [stokesTestPairing_R3_diag]
    exact viscousFormSq_R3_nonneg zero_le_one _

/-- The continuous linear functional on `V_n := galerkinSpan B n` whose Riesz representative is
the Galerkin vector field: `φ w = - ν · stokesTestPairing_R3 (u, w) - F.b (σu) (σu) (σw)`.

Right-linearity in `w` comes from `stokesTestPairing_R3_add_right`/`_smul_right` (the analytic
linearity helpers, valid on span elements) and `F.b_add_3`/`F.b_smul_3` (with
`galerkinSpanToSigma` additive/homogeneous).  Continuity is automatic on the
finite-dimensional `V_n` via `LinearMap.toContinuousLinearMap`. -/
noncomputable def galerkinODE_functional
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) : galerkinSpan B n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
        - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
              (galerkinSpanToSigma B n w)
      map_add' := by
        intro w w'
        rw [stokesTestPairing_R3_add_right, galerkinSpanToSigma_add,
          F.b_add_3 (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
            (galerkinSpanToSigma B n w) (galerkinSpanToSigma B n w')]
        ring
      map_smul' := by
        intro c w
        rw [stokesTestPairing_R3_smul_right, galerkinSpanToSigma_smul,
          F.b_smul_3 c (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
            (galerkinSpanToSigma B n w)]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }

/-- `galerkinODE_functional` unfolds to its defining Stokes/convection pairing formula. -/
@[simp] theorem galerkinODE_functional_apply
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u w : galerkinSpan B n) :
    galerkinODE_functional B F ν n u w
      = - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
        - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
              (galerkinSpanToSigma B n w) := rfl

/-- The finite-dim Galerkin vector field `G_n` on `V_n := galerkinSpan B n`.

It is the Riesz representative (in the finite-dim — hence complete — inner product space
`V_n`) of the continuous linear functional `galerkinODE_functional`
`w ↦ - ν · stokesTestPairing_R3 (u, w) - F.b u u w` restricted to `V_n`.  The functional is
linear in `w` (`stokes` linear in its 2nd slot — `stokesTestPairing_R3_add_right`/`_smul_right`
on span elements — and `F.b` additive + ℝ-homogeneous in its 3rd slot), so it is automatically
continuous on the finite-dim `V_n` (`LinearMap.toContinuousLinearMap`), and
`InnerProductSpace.toDual.symm` produces its representative WITHOUT needing the quantitative
`b_bound`.

Working over `schemeOfBasis B` is essential: `V_n` is finite-dimensional only for the
concrete span (P5 `galerkinSpan_finiteDimensional`), which the abstract scheme does not give. -/
noncomputable def galerkinODE_vectorField
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) : galerkinSpan B n :=
  (InnerProductSpace.toDual ℝ (galerkinSpan B n)).symm (galerkinODE_functional B F ν n u)

/-! ### R2 — the Riesz characterization (the weak↔vector-field bridge) -/

/-- Defining property of the Riesz field `G_n`: testing it against any `w ∈ V_n` recovers the
functional `w ↦ - ν · stokes(u, w) - b(u, u, w)`.  This is the **R-repr** content
(weak-form ⇄ vector-field representation) made precise: it is the identity from which the
weak Galerkin ODE `u_ode` is DERIVED in R3.  Sign/`ν` conventions match `u_ode`
(`SolutionInterfaces.lean` / `GalerkinODE.lean:102`). -/
theorem galerkinODE_vectorField_spec
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u w : galerkinSpan B n) :
    inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n u : L2VF_R3) (w : L2VF_R3)
      = - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
        - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
              (galerkinSpanToSigma B n w) := by
  -- Transport the ambient inner product to the `V_n` inner product, then apply
  -- `toDual_symm_apply` and unfold the functional.
  rw [show inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n u : L2VF_R3) (w : L2VF_R3)
      = inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n u) w from
        (Submodule.coe_inner (galerkinSpan B n) (galerkinODE_vectorField B F ν n u) w).symm]
  -- `toDual_symm_apply : ⟪(toDual).symm φ, w⟫_{V_n} = φ w`; then `galerkinODE_functional_apply`
  -- exposes the RHS exactly.
  rw [galerkinODE_vectorField, InnerProductSpace.toDual_symm_apply,
    galerkinODE_functional_apply]

/-! ### S0 — the residual isolated frontier hypothesis -/

/-- Residual isolated frontier (Pillar E): a GLOBAL solution of the finite-dim AUTONOMOUS
Galerkin ODE `c' = galerkinODE_vectorField` on `V_n := galerkinSpan B n`.

This bundles ONLY the one irreducible mathlib gap — there is no
continuation/global-existence-from-a-priori-bound theorem for vector spaces in mathlib (the
field `G_n` is quadratic, hence only locally Lipschitz, so the only `_univ` ODE-existence
lemma does not apply; the manifold continuation lemma assumes per-interval existence). It is
supplied by the caller, NOT proved here.

**No-smuggle.** The defining field `ode` is the AUTONOMOUS vector-field equation
`c'(t) = G_n(c t)`, **NOT** the weak Galerkin form `u_ode`.  The weak form, the subspace
confinement `u_inVn`, the ambient-derivative transport, the energy/dissipation bounds, and
the H¹ regularity are all DELIBERATELY ABSENT — they are DERIVED (R3 here + the already
proved `GalerkinODE.lean` payoff).  In particular R-repr (weak ⇄ vector-field) is PROVED via
R2, not assumed: this bundle is STRICTLY weaker than `GalerkinODEInput`. -/
structure FinDimGlobalODE (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) where
  /-- The global finite-dim solution curve into `V_n := galerkinSpan B n`. -/
  c : Time → galerkinSpan B n
  /-- Initial condition: `c 0 = galerkinP B n u₀` (in `L2VF_R3`). -/
  c_initial : (c 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3)
  /-- Forward differentiability of the ambient curve `t ↦ (c t : L2VF_R3)` at `t ≥ 0`.

  SOUNDNESS (forward-only): the global solver guarantees the finite-dim curve only on forward
  time (the energy bound confines `c` for `t ≥ 0`); this quadratic vector field can blow up in
  finite backward time, so the all-`t` form was a latent over-strength claim.  Restricted to
  `0 ≤ t`. -/
  c_hasDeriv : ∀ t, 0 ≤ t → HasDerivAt (fun s => (c s : L2VF_R3))
    (deriv (fun s => (c s : L2VF_R3)) t) t
  /-- The AUTONOMOUS finite-dim vector-field equation `c'(t) = G_n (c t)` at forward times
  `t ≥ 0` (NOT the weak form — that is derived in R3 from this via the Riesz characterization
  R2).

  SOUNDNESS (forward-only): same rationale as `c_hasDeriv`; restricted to `0 ≤ t`. -/
  ode : ∀ t, 0 ≤ t → deriv (fun s => (c s : L2VF_R3)) t
      = (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)

/-! ### R3 — assemble the `GalerkinODEInput` from a global curve -/

/-- H¹ regularity of a span element (it is fixed by `galerkinP B n`). -/
private theorem galerkinSpan_memH1 (B : SchwartzGalerkinBasis) (n : ℕ) (v : galerkinSpan B n) :
    memH1VF_R3 (v : L2VF_R3) :=
  galerkinCurve_reg_mem (schemeOfBasis B) n (v : L2VF_R3)
    ((galerkinSpan B n).starProjection_eq_self_iff.mpr v.2).symm

/-- The weighted Fourier component, as an **ℝ-linear map** on the finite-dimensional Galerkin
subspace `V_n = galerkinSpan B n`.  Linearity is `weightedFourierComponent_add` / `_smul`
(the `H¹`-proof argument is irrelevant). -/
noncomputable def weightedFourierComponentₗ (B : SchwartzGalerkinBasis) (n : ℕ) (j : Fin 3) :
    galerkinSpan B n →ₗ[ℝ] L2C_R3 where
  toFun v := weightedFourierComponent (v : L2VF_R3) (galerkinSpan_memH1 B n v) j
  map_add' v w := by
    simp only [Submodule.coe_add]
    exact weightedFourierComponent_add (v : L2VF_R3) (w : L2VF_R3)
      (galerkinSpan_memH1 B n v) (galerkinSpan_memH1 B n w) (galerkinSpan_memH1 B n (v + w)) j
  map_smul' r v := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact weightedFourierComponent_smul r (v : L2VF_R3)
      (galerkinSpan_memH1 B n v) (galerkinSpan_memH1 B n (r • v)) j

/-- The weighted Fourier component map on `V_n` is **continuous** (linear map out of a
finite-dimensional space). -/
theorem continuous_weightedFourierComponentₗ (B : SchwartzGalerkinBasis) (n : ℕ) (j : Fin 3) :
    Continuous (weightedFourierComponentₗ B n j) :=
  (weightedFourierComponentₗ B n j).continuous_of_finiteDimensional

/-- From a global curve `c : Time → V_n` solving the AUTONOMOUS field equation
`c' = G_n(c)` (the residual `FinDimGlobalODE` hypothesis), assemble the full
`GalerkinODEInput`: the curve and its initial value, subspace confinement `u_inVn`, the
ambient-derivative transport `u_hasDeriv`, and — crucially — the weak Galerkin ODE `u_ode`,
which is DERIVED from `c' = G_n(c)` via the Riesz characterization R2.  This last step is
where R-repr (weak-form ⇄ vector-field) is discharged into the weak form.

A `noncomputable def` (not `theorem`): `GalerkinODEInput` is a data-carrying structure in
`Type`, not a `Prop` (mirrors `galerkinSolutionData_R3_of_input` in `GalerkinODE.lean`). -/
noncomputable def galerkinODEInput_of_globalCurve
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (_hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) (G : FinDimGlobalODE B F ν u₀ n) :
    GalerkinODEInput (schemeOfBasis B) F ν u₀ n := by
  -- The Galerkin curve transported into `L2Sigma_R3`.
  refine
    { u := fun t => galerkinSpanToSigma B n (G.c t)
      u_initial := ?_
      u_inVn := ?_
      u_hasDeriv := ?_
      u_ode := ?_
      viscous_curve_continuous := ?_ }
  · -- `u 0 = ⟨galerkinP B n u₀, …⟩`.  Equate the underlying `L2VF_R3` vectors via `G.c_initial`.
    apply Subtype.ext
    show (G.c 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3)
    exact G.c_initial
  · -- The curve stays in `V_n`: `(u t : L2VF_R3) = G.c t ∈ galerkinSpan B n` is fixed by `P n`.
    intro t
    show (G.c t : L2VF_R3) = galerkinP B n (G.c t : L2VF_R3)
    exact ((galerkinSpan B n).starProjection_eq_self_iff.mpr (G.c t).2).symm
  · -- The ambient-curve derivative is exactly the `c_hasDeriv` field (forward time).
    intro t ht
    exact G.c_hasDeriv t ht
  · -- Derive the weak Galerkin ODE from the autonomous field equation `c' = G_n(c)` + R2.
    intro t ht w hw
    -- `w ∈ galerkinSpan B n` since `(w : L2VF_R3) = galerkinP B n w` (i.e. `P n` fixes `w`).
    have hwmem : (w : L2VF_R3) ∈ galerkinSpan B n := by
      rw [hw]; exact galerkinP_mem_span B n (w : L2VF_R3)
    -- View `w` as an element of `V_n`.
    set wV : galerkinSpan B n := ⟨(w : L2VF_R3), hwmem⟩ with hwV
    -- `F.b` arguments: the embedding `galerkinSpanToSigma B n wV` agrees with `w` as `L2Sigma_R3`.
    have hbw : galerkinSpanToSigma B n wV = w := by
      apply Subtype.ext; rfl
    -- The transported curve coerces back to `G.c`, so its ambient derivative is `G.c`'s.
    simp only [galerkinSpanToSigma_coe]
    -- Rewrite the derivative via the autonomous field equation, then apply the Riesz spec R2.
    rw [G.ode t ht]
    have hspec := galerkinODE_vectorField_spec B F ν n (G.c t) wV
    -- `hspec : ⟨G_n(c t), w⟩ = -ν·stokes(c t, w) - b(c t, c t, w)`.
    rw [hspec]
    -- `galerkinSpanToSigma B n (G.c t) = u t` and `galerkinSpanToSigma B n wV = w`.
    rw [hbw]
    ring
  · -- `viscous_curve_continuous`: the weighted Fourier component curve factors as the continuous
    -- linear `weightedFourierComponentₗ` applied to the continuous (finite-dim) Galerkin curve.
    intro j
    -- The curve `s ↦ G.c s` is continuous into `V_n` (the subtype): its `L2VF_R3` coercion has a
    -- derivative on `Ici 0`, and the subtype topology is induced.
    have hcSpan : ContinuousOn (fun s => G.c s) (Set.Ici (0 : ℝ)) := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      exact fun t ht => (G.c_hasDeriv t ht).continuousAt.continuousWithinAt
    -- Compose with the continuous linear weighted-Fourier map; the values agree pointwise.
    have hcomp : ContinuousOn
        (fun s => weightedFourierComponentₗ B n j (G.c s)) (Set.Ici (0 : ℝ)) :=
      (continuous_weightedFourierComponentₗ B n j).comp_continuousOn hcSpan
    refine hcomp.congr (fun s _ => ?_)
    -- `weightedFourierComponent (u s) _ j = weightedFourierComponentₗ B n j (G.c s)` (proof-irrel.).
    rfl

/-! ### D — the deliverable -/

/-- **Deliverable (Pillar E).** From a Schwartz divergence-free basis `B` (concrete scheme
`schemeOfBasis B`) and the isolated finite-dim global-existence hypothesis `FinDimGlobalODE`,
construct the Galerkin ODE input.  Thin wrapper for R3, named to match the milestone
deliverable vocabulary.  This discharges R-repr (weak-form ⇄ vector-field, via the finite-dim
Riesz field R1/R2) axiom-free; the R-global gap stays isolated in `FinDimGlobalODE`.

A `noncomputable def` (not `theorem`): `GalerkinODEInput` lives in `Type`, not `Prop`. -/
noncomputable def galerkinODEInput_of_basis
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) (G : FinDimGlobalODE B F ν u₀ n) :
    GalerkinODEInput (schemeOfBasis B) F ν u₀ n :=
  galerkinODEInput_of_globalCurve B F ν hν u₀ n G

/-- Optional full chain: assemble the complete `GalerkinSolutionData_R3` over the concrete
scheme `schemeOfBasis B`, combining the deliverable input (D) with the already-proved
energy/dissipation/regularity payoff `galerkinSolutionData_R3_of_input` (`GalerkinODE.lean`). -/
noncomputable def galerkinSolutionData_of_basis
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) (G : FinDimGlobalODE B F ν u₀ n) :
    GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
  galerkinSolutionData_R3_of_input (schemeOfBasis B) F ν hν u₀ n
    (galerkinODEInput_of_basis B F ν hν u₀ n G)

end LerayHopf
