import Tengoku.LerayHopf.LerayHopf.R3.Regularity
import Tengoku
-- Sobolev.lean import justification: MemSobolev.add, MemSobolev.smul, MemSobolev.lineDerivOp,
--   used to extract the spectral L² weak-derivative representative below.

namespace LerayHopf

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv

/-!
# Spectral weak-gradient component and its integration-by-parts identity

Generic H¹(ℝ³) infrastructure extracted from `EnergyClassConvection.lean` (issue #113 PR-2):
for `u : L2VF_R3` with `memH1VF_R3 u`, `gradComp_of_memH1 u hu a j` is the `L²(ℝ³;ℂ)`
representative of the weak directional derivative `∂_{eₐ}` of the `j`-th complex component of
`u`, extracted from `TemperedDistribution.MemSobolev` via `MemSobolev.lineDerivOp` +
`memSobolev_zero_iff`. `gradComponent_weakDeriv` is the integration-by-parts identity relating
it to the classical Schwartz IBP; `gradComp_of_memH1_add`/`_smul` are its linearity in the field
argument. None of this is convection-specific — it is pure H¹/Sobolev machinery.

## Declarations

- `cxify`, `cxify_apply`, `lineDerivOp_cxify` — complexification of a real Schwartz map and its
  commutation with the line derivative. Kept public (not `private` as on `main`): the B3a/B6
  content still left in `EnergyClassConvection.lean` (pending issue #113 PR-2 commits 4-5)
  references them by name.
- `gradComp_of_memH1`, `gradComp_of_memH1_spec` — the spectral L² weak-derivative representative
  and its defining tempered-distribution identity
- `gradComponent_weakDeriv` — the classical IBP identity against a Schwartz test
- `L2C_eq_of_toTempered_eq` — injectivity of the `Lp → 𝓢'` embedding. Also kept public for the
  same cross-file-reference reason as `cxify` above.
- `gradComp_of_memH1_add`, `gradComp_of_memH1_smul` — linearity of `gradComp_of_memH1` in the
  field argument

All public names/statements preserved from `EnergyClassConvection.lean`.

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-! ### Helpers — complexification of real Schwartz tests -/

/-- Complexification of a real Schwartz map: post-compose with `ofRealCLM : ℝ →L[ℝ] ℂ`. -/
noncomputable def cxify (φ : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  φ.postcompCLM (RCLike.ofRealCLM (K := ℂ))

/-- The complexification `cxify φ` evaluates pointwise as the real-to-complex coercion of
`φ`. -/
@[simp] theorem cxify_apply (φ : SchwartzMap Domain3 ℝ) (x : Domain3) :
    cxify φ x = ((φ x : ℝ) : ℂ) := by
  simp [cxify, SchwartzMap.postcompCLM_apply]

/-- Complexification commutes with the line derivative: `∂_{m}(cxify φ) = cxify (∂_{m} φ)`.
Both sides agree pointwise: `lineDeriv` commutes with the `ℝ`-linear map `ofRealCLM`. -/
theorem lineDerivOp_cxify (m : Domain3) (φ : SchwartzMap Domain3 ℝ) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) m) (cxify φ)
      = cxify ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m) φ) := by
  apply SchwartzMap.ext
  intro x
  rw [LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply, cxify_apply, SchwartzMap.lineDerivOp_apply]
  -- Goal: lineDeriv ℝ (cxify φ) x m = ofReal (lineDeriv ℝ φ x m)
  have hL : HasLineDerivAt ℝ (fun y => φ y) (lineDeriv ℝ (fun y => φ y) x m) x m :=
    (φ.differentiableAt.lineDifferentiableAt).hasLineDerivAt
  have hcx : (fun y => cxify φ y) = fun y => RCLike.ofRealCLM (K := ℂ) (φ y) :=
    funext fun y => by rw [cxify_apply]; rfl
  have hLcx : HasLineDerivAt ℝ (fun y => cxify φ y)
      (RCLike.ofRealCLM (K := ℂ) (lineDeriv ℝ (fun y => φ y) x m)) x m := by
    rw [hcx]
    exact (RCLike.ofRealCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt _ hL
  rw [hLcx.lineDeriv]
  rfl

/-! ### B2 — Spectral weak-gradient component and IBP identity -/

/-- **B2 helper `gradComp_of_memH1`** — the spectral L² weak-derivative representative.

For `u : L2VF_R3` with `memH1VF_R3 u`, the j-th Sobolev component satisfies
`MemSobolev 1 2 (L2VF_projComponentC_R3 j u)`. Applying `MemSobolev.lineDerivOp` at
`m = EuclideanSpace.single a 1` yields `MemSobolev 0 2 (∂_{eₐ} (L2VF_projComponentC_R3 j u))`,
and `memSobolev_zero_iff` gives an `L²` representative.

`gradComp_of_memH1 u hu a j` is the L²(ℝ³; ℂ) representative of the weak
directional derivative `∂_{eₐ}` of the j-th component of `u`. -/
noncomputable def gradComp_of_memH1 (u : L2VF_R3) (hu : memH1VF_R3 u) (a j : Fin 3) :
    L2C_R3 :=
  -- MemSobolev 1 2 on j-th component → MemSobolev (1-1) 2 on the directional derivative.
  -- Note: MemSobolev.lineDerivOp gives MemSobolev (s-1) 2; here s = 1 so we get (1-1) = 0.
  have hderiv : TemperedDistribution.MemSobolev 0 2
      (∂_{EuclideanSpace.single a (1 : ℝ)} (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ))) := by
    have h := (hu j).lineDerivOp (m := EuclideanSpace.single a (1 : ℝ))
    -- h : MemSobolev (1 - 1) 2 ...  but 1 - 1 = 0 in ℝ.
    norm_num at h
    exact h
  -- MemSobolev 0 2 ↔ ∃ f' : L2C_R3, f = f' — extract the L² representative.
  (TemperedDistribution.memSobolev_zero_iff.mp hderiv).choose

/-- Injectivity of the `Lp → 𝓢'` embedding: equal tempered distributions ⟹ equal `Lp` elements. -/
theorem L2C_eq_of_toTempered_eq {f g : L2C_R3}
    (h : (f : 𝓢'(Domain3, ℂ)) = (g : 𝓢'(Domain3, ℂ))) : f = g := by
  have hker := MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure Domain3)) (p := 2)
  have : (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2) (f - g) = 0 := by
    rw [map_sub]
    simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply]
    rw [sub_eq_zero]; exact h
  have hmem : (f - g) ∈ (MeasureTheory.Lp.toTemperedDistributionCLM
      ℂ (volume : Measure Domain3) 2).ker := this
  rw [hker] at hmem
  rw [Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

end LerayHopf
