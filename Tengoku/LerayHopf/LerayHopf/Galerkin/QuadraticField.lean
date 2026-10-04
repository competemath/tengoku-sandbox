import Tengoku
import Tengoku.LerayHopf.LerayHopf.Galerkin.DissipativeODE

/-!
# Generic quadratic-plus-linear Galerkin vector field (issue #112)

**Campaign:** `docs/scratch/galerkin-domain-plan.md` §3.2 (PR-A). `FieldForms` packages the
raw trilinear convection form and viscous form data on a finite-dimensional real
inner-product space `V`, deduplicating the two lane CLM towers
(`LerayHopf/R3/GalerkinODESolve.lean`'s `rieszSymmCLM`/`bInner`/`bMid`/`bOut`/`stokesInner`/
`stokesOut` and `LerayHopf/Torus/GalerkinODESolve.lean`'s byte-parallel copy) into a single
construction proved ONCE. `FieldForms.vectorField` is the Riesz representative of the
functional `w ↦ -ν * D.sV u w - D.bV u u w`, matching each lane's
`galerkinODE_functional`/`galerkinODE_vectorField` sign/`ν` convention.

Linearity is stated raw (no `ContinuousLinearMap` data in the structure fields): on the
finite-dimensional `V` every linear map is automatically continuous
(`LinearMap.toContinuousLinearMap`), so continuity does not need to be threaded through the
structure — it is recovered where needed (`vectorField_contDiff`) from finite-dimensionality
alone. PR-B (issue #112 lane rewiring) supplies the two lane witnesses `torusFieldForms` /
`r3FieldForms` and bridges each lane's existing `galerkinODE_vectorField` to
`(FieldForms).vectorField` by `ext_inner_right` + both specs (plan §3.3).

Generic-layer only: mathlib plus `LerayHopf.Galerkin.DissipativeODE` (itself mathlib-only) —
no NS/domain/Galerkin-scheme content. The `DissipativeODE` import is needed for
`forwardGlobalSolution_exists`'s frozen proof route (plan §3.2): it is derived from
`DissipativeODE.forwardGlobalSolution_exists` applied to `vectorField_contDiff` and
`inner_self_vectorField_nonpos`. Pdelib-grade is a property of the `LerayHopf/Galerkin/`
generic layer as a whole (flagged in `docs/pdelib-staging.md`) and is preserved by this
intra-layer dependency; this file is consumed by nothing in `LerayHopf` yet (PR-A has no
consumers by design; wiring happens in PR-B).

## Scaffold status

`FieldForms.vectorField` is a REAL definition (PR-A, coder pass): it is a mechanical
transcription of the lane `galerkinODE_functional`/`galerkinODE_vectorField` pair (via the
private helper `vectorFieldFunctional`, mirroring `rieszSymmCLM ∘ galerkinODE_functional`),
substituting the abstract `D.bV`/`D.sV` for each lane's concrete `F.b`/`stokesTestPairing`.
Every THEOREM body below is filled (PR-A, prover pass): direct ports of the lane proof
route (plan §3.2), with `vectorField_contDiff` supplied by the local CLM tower
`rieszSymm`/`bInner`/`bMid`/`bOut`/`bilinearPart` + `stokesInner`/`stokesOut`/`linearPart`
(finite-dim auto-continuity at each level, `vectorField_eq_parts` splitting the field into a
continuous-bilinear-plus-linear map of `u`). Statements are FROZEN by the architect
(plan §3.2) and were not altered.
-/

namespace LerayHopf.Galerkin

/-- Raw trilinear + viscous form data restricted to a finite-dimensional real
inner-product space, sufficient to build the Galerkin vector field.  Linearity is stated
raw (no CLM data): on the finite-dimensional `V` continuity is automatic. -/
structure FieldForms (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  bV : V → V → V → ℝ
  bV_add_1 : ∀ u u' v w, bV (u + u') v w = bV u v w + bV u' v w
  bV_add_2 : ∀ u v v' w, bV u (v + v') w = bV u v w + bV u v' w
  bV_add_3 : ∀ u v w w', bV u v (w + w') = bV u v w + bV u v w'
  bV_smul_1 : ∀ (a : ℝ) u v w, bV (a • u) v w = a * bV u v w
  bV_smul_2 : ∀ (a : ℝ) u v w, bV u (a • v) w = a * bV u v w
  bV_smul_3 : ∀ (a : ℝ) u v w, bV u v (a • w) = a * bV u v w
  bV_diag_zero : ∀ v, bV v v v = 0
  sV : V → V → ℝ
  sV_symm : ∀ u w, sV u w = sV w u
  sV_add_right : ∀ u w w', sV u (w + w') = sV u w + sV u w'
  sV_smul_right : ∀ (a : ℝ) u w, sV u (a • w) = a * sV u w
  sV_diag_nonneg : ∀ v, 0 ≤ sV v v

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The continuous linear functional on `V` whose Riesz representative is the Galerkin
vector field at `u`: `w ↦ -ν * D.sV u w - D.bV u u w`. Right-linearity in `w` is
`D.sV_add_right`/`D.sV_smul_right` (slot 2) and `D.bV_add_3`/`D.bV_smul_3` (slot 3);
continuity is automatic on the finite-dim `V`. Mirrors each lane's
`galerkinODE_functional`. -/
private noncomputable def vectorFieldFunctional (D : FieldForms V) (ν : ℝ) (u : V) :
    V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => -ν * D.sV u w - D.bV u u w
      map_add' := by
        intro w w'
        rw [D.sV_add_right, D.bV_add_3]; ring
      map_smul' := by
        intro a w
        rw [D.sV_smul_right, D.bV_smul_3]
        simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem vectorFieldFunctional_apply (D : FieldForms V) (ν : ℝ) (u w : V) :
    vectorFieldFunctional D ν u w = -ν * D.sV u w - D.bV u u w := rfl

/-- Riesz representative of `w ↦ -ν * D.sV u w - D.bV u u w`. -/
noncomputable def FieldForms.vectorField (D : FieldForms V) (ν : ℝ) : V → V :=
  fun u => (InnerProductSpace.toDual ℝ V).symm (vectorFieldFunctional D ν u)

/-- `vectorField` is the Riesz representative of the functional it was built from: pairing
against any `w` recovers `-ν * D.sV u w - D.bV u u w`. -/
theorem FieldForms.vectorField_spec (D : FieldForms V) (ν : ℝ) (u w : V) :
    inner (𝕜 := ℝ) (D.vectorField ν u) w = -ν * D.sV u w - D.bV u u w := by
  show inner (𝕜 := ℝ) ((InnerProductSpace.toDual ℝ V).symm (vectorFieldFunctional D ν u)) w
      = -ν * D.sV u w - D.bV u u w
  rw [InnerProductSpace.toDual_symm_apply, vectorFieldFunctional_apply]

/-! ### CLM tower for `vectorField_contDiff`

Mirrors `LerayHopf/R3/GalerkinODESolve.lean`'s `rieszSymmCLM`/`bInner`/`bMid`/`bOut`/
`stokesInner`/`stokesOut` tower, specialized to the abstract `FieldForms` data (no submodule
coercions): the field splits as `u ↦ Bil(u,u) + Lin u`, a continuous-bilinear-plus-linear map
of `u`, hence `C¹` on the finite-dimensional `V` by finite-dim auto-continuity at each level. -/

/-- Riesz inverse `(V →L[ℝ] ℝ) →L[ℝ] V` as a `ContinuousLinearMap`. -/
private noncomputable def rieszSymm : (V →L[ℝ] ℝ) →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearMap

@[simp] private theorem rieszSymm_apply (φ : V →L[ℝ] ℝ) :
    rieszSymm φ = (InnerProductSpace.toDual ℝ V).symm φ := rfl

/-- Inner functional (slot 3): `w ↦ -D.bV u u' w`, linear in `w` by `bV_add_3`/`bV_smul_3`. -/
private noncomputable def bInner (D : FieldForms V) (u u' : V) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - D.bV u u' w
      map_add' := by intro w w'; rw [D.bV_add_3]; ring
      map_smul' := by
        intro c w
        rw [D.bV_smul_3]; simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem bInner_apply (D : FieldForms V) (u u' w : V) :
    bInner D u u' w = - D.bV u u' w := rfl

/-- Middle map (slot 2): `u' ↦ bInner D u u'`, linear in `u'` by `bV_add_2`/`bV_smul_2`. -/
private noncomputable def bMid (D : FieldForms V) (u : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u' => bInner D u u'
      map_add' := by
        intro u' u''
        ext w
        simp only [add_apply, bInner_apply, D.bV_add_2]; ring
      map_smul' := by
        intro c u'
        ext w
        simp only [RingHom.id_apply, smul_apply, bInner_apply,
          D.bV_smul_2, smul_eq_mul]; ring }

@[simp] private theorem bMid_apply (D : FieldForms V) (u u' : V) :
    bMid D u u' = bInner D u u' := rfl

/-- Outer map (slot 1): `u ↦ bMid D u`, linear in `u` by `bV_add_1`/`bV_smul_1`. -/
private noncomputable def bOut (D : FieldForms V) : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => bMid D u
      map_add' := by
        intro u u''
        ext u' w
        simp only [add_apply, bMid_apply, bInner_apply, D.bV_add_1]; ring
      map_smul' := by
        intro c u
        ext u' w
        simp only [RingHom.id_apply, smul_apply, bMid_apply, bInner_apply,
          D.bV_smul_1, smul_eq_mul]; ring }

@[simp] private theorem bOut_apply (D : FieldForms V) (u : V) :
    bOut D u = bMid D u := rfl

/-- Bilinear `bV`-part `V × V → V`: `(u, u') ↦ rieszSymm (w ↦ -bV u u' w)`, the Riesz inverse
of the `bOut`-functional, post-composed with `rieszSymm`. -/
private noncomputable def bilinearPart (D : FieldForms V) : V →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V (V →L[ℝ] ℝ) V rieszSymm).comp (bOut D)

@[simp] private theorem bilinearPart_apply (D : FieldForms V) (u u' : V) :
    bilinearPart D u u' = rieszSymm (bInner D u u') := rfl

omit [FiniteDimensional ℝ V] in
/-- Left-additivity of `sV`, via right-additivity + symmetry (`sV_symm`). -/
private theorem sV_add_left (D : FieldForms V) (u u' w : V) :
    D.sV (u + u') w = D.sV u w + D.sV u' w := by
  rw [D.sV_symm (u + u') w, D.sV_add_right, D.sV_symm w u, D.sV_symm w u']

omit [FiniteDimensional ℝ V] in
/-- Left-homogeneity of `sV`, via right-homogeneity + symmetry (`sV_symm`). -/
private theorem sV_smul_left (D : FieldForms V) (a : ℝ) (u w : V) :
    D.sV (a • u) w = a * D.sV u w := by
  rw [D.sV_symm (a • u) w, D.sV_smul_right, D.sV_symm w u]

/-- Inner functional: `w ↦ -ν * D.sV u w`, linear in `w` by `sV_add_right`/`sV_smul_right`. -/
private noncomputable def stokesInner (D : FieldForms V) (ν : ℝ) (u : V) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - ν * D.sV u w
      map_add' := by intro w w'; rw [D.sV_add_right]; ring
      map_smul' := by
        intro c w
        rw [D.sV_smul_right]; simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem stokesInner_apply (D : FieldForms V) (ν : ℝ) (u w : V) :
    stokesInner D ν u w = - ν * D.sV u w := rfl

/-- Outer map: `u ↦ stokesInner D ν u`, linear in `u` by `sV_add_left`/`sV_smul_left`. -/
private noncomputable def stokesOut (D : FieldForms V) (ν : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => stokesInner D ν u
      map_add' := by
        intro u u'
        ext w
        simp only [add_apply, stokesInner_apply]
        rw [sV_add_left D u u' w]; ring
      map_smul' := by
        intro c u
        ext w
        simp only [RingHom.id_apply, smul_apply, stokesInner_apply,
          smul_eq_mul]
        rw [sV_smul_left D c u w]; ring }

@[simp] private theorem stokesOut_apply (D : FieldForms V) (ν : ℝ) (u : V) :
    stokesOut D ν u = stokesInner D ν u := rfl

/-- Linear `-ν·sV`-part `V → V`: `u ↦ rieszSymm (w ↦ -ν * sV u w)`, the Riesz inverse of the
`stokesOut`-functional. -/
private noncomputable def linearPart (D : FieldForms V) (ν : ℝ) : V →L[ℝ] V :=
  rieszSymm.comp (stokesOut D ν)

@[simp] private theorem linearPart_apply (D : FieldForms V) (ν : ℝ) (u : V) :
    linearPart D ν u = rieszSymm (stokesInner D ν u) := rfl

/-- The field equals `Bil(u,u) + Lin u`, by Riesz injectivity (test against every `w`). -/
private theorem vectorField_eq_parts (D : FieldForms V) (ν : ℝ) (u : V) :
    D.vectorField ν u = bilinearPart D u u + linearPart D ν u := by
  refine ext_inner_right ℝ (fun w => ?_)
  have hbil : inner (𝕜 := ℝ) (bilinearPart D u u) w = - D.bV u u w := by
    rw [bilinearPart_apply, rieszSymm_apply, InnerProductSpace.toDual_symm_apply, bInner_apply]
  have hlin : inner (𝕜 := ℝ) (linearPart D ν u) w = - ν * D.sV u w := by
    rw [linearPart_apply, rieszSymm_apply, InnerProductSpace.toDual_symm_apply, stokesInner_apply]
  rw [D.vectorField_spec, inner_add_left, hbil, hlin]; ring

/-- `vectorField ν` is `C¹` in its argument: as the sum of the bilinear part `bilinearPart D u u`
(quadratic, hence `C¹`) and the linear part `linearPart D ν` (continuous linear, hence smooth). -/
theorem FieldForms.vectorField_contDiff (D : FieldForms V) (ν : ℝ) :
    ContDiff ℝ 1 (D.vectorField ν) := by
  have hfun : D.vectorField ν
      = fun u => bilinearPart D u u + linearPart D ν u := by
    funext u; exact vectorField_eq_parts D ν u
  rw [hfun]
  have hbil : ContDiff ℝ 1 (fun u => bilinearPart D u u) :=
    (bilinearPart D).contDiff.clm_apply contDiff_id
  have hlin : ContDiff ℝ 1 (fun u => linearPart D ν u) :=
    (linearPart D ν).contDiff
  exact hbil.add hlin

/-- The diagonal pairing `⟨v, vectorField ν v⟩` collapses to `-(ν * D.sV v v)`: the bilinear
part `D.bV v v v` vanishes by the antisymmetry-driven diagonal identity `bV_diag_zero`, leaving
only the dissipative (linear-part) contribution. -/
theorem FieldForms.inner_self_vectorField (D : FieldForms V) (ν : ℝ) (v : V) :
    inner (𝕜 := ℝ) v (D.vectorField ν v) = -(ν * D.sV v v) := by
  rw [real_inner_comm, D.vectorField_spec, D.bV_diag_zero, sub_zero, neg_mul]

/-- For `ν > 0`, the diagonal pairing `⟨v, vectorField ν v⟩` is nonpositive — the dissipativity
condition that drives the energy inequality for solutions of `c' = vectorField ν c`. -/
theorem FieldForms.inner_self_vectorField_nonpos (D : FieldForms V) {ν : ℝ}
    (hν : 0 < ν) (v : V) : inner (𝕜 := ℝ) v (D.vectorField ν v) ≤ 0 := by
  rw [D.inner_self_vectorField ν v]
  exact neg_nonpos.mpr (mul_nonneg hν.le (D.sV_diag_nonneg v))

/-- Along a solution `c` of `c' = vectorField ν c`, the kinetic energy `½‖c‖²` has derivative
`-(ν * D.sV (c t) (c t))` — the abstract energy identity for the quadratic-field ODE. -/
theorem FieldForms.energy_hasDerivAt (D : FieldForms V) (ν : ℝ) (c : ℝ → V) (t : ℝ)
    (hc : HasDerivAt c (D.vectorField ν (c t)) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2) (-(ν * D.sV (c t) (c t))) t := by
  have h := energy_hasDerivAt_of_solution (D.vectorField ν) c t hc
  rwa [D.inner_self_vectorField ν (c t)] at h

/-- For `ν > 0`, the ODE `c' = vectorField ν c` has a global forward-in-time solution from any
initial data `x₀` — assembled from `C¹`-regularity (`vectorField_contDiff`) and dissipativity
(`inner_self_vectorField_nonpos`) via the abstract global-existence lemma
`forwardGlobalSolution_exists`. -/
theorem FieldForms.forwardGlobalSolution_exists (D : FieldForms V) {ν : ℝ}
    (hν : 0 < ν) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (D.vectorField ν (c t)) t :=
  _root_.LerayHopf.Galerkin.forwardGlobalSolution_exists (D.vectorField ν)
    (D.vectorField_contDiff ν) (fun v => D.inner_self_vectorField_nonpos hν v) x₀

end LerayHopf.Galerkin
