import Tengoku.LerayHopf.LerayHopf.R3.FourierL2

namespace LerayHopf

open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped Topology RealInnerProductSpace FourierTransform

/-!
# Fourier–Parseval bridge lemmas and the du Bois-Reymond Hermitian/anti-Hermitian machinery

Generic infrastructure extracted from `CurlDensity.lean` (issue #113 PR-2): the
complexification-of-a-real-Schwartz-map utility (`schwartzC`), the vector Parseval bridge
between the real `L2VF_R3` inner product and the Fourier-side component pairing
(`inner_L2VF_eq_integral_sum_fourier` and its supporting lemmas), the Hermitian-reality facts
(`fourier_hermitian_real`, `fourier_schwartzC_hermitian`), and the companion du Bois-Reymond
block characterizing which Fourier symbols are attained by real Schwartz test functions
(`testSymbol` and its (anti-)Hermitian preimage-extraction theory). None of this is specific to
curl or divergence-freeness — it is generic real/complex-Fourier-analysis infrastructure that
`CurlDensity.lean`'s curl-density argument builds on top of, and `CurlDensityH1.lean` also
consumes directly.

## Declarations

- `schwartzC`, `schwartzC_apply` — complexification of a real Schwartz map (public on `main`)
- `toLp_schwartzC_eq` — the complex L²-class of a complexified real Schwartz map (public)
- `lineDerivOp_schwartzC`, `fourier_schwartzC_lineDeriv_apply` — line-derivative-commutes and
  its Fourier symbol. NOT in the extraction contract's named list, but discovered via the
  build: `CurlDensity.lean`'s own remaining Schwartz-Fourier lemmas and `StokesFourier.lean`
  both need them, and they are purely generic (`schwartzC` + line derivatives, no curl
  coupling). Kept public (were `private` on `main`).
- `fourier_schwartzC_hermitian` — Fourier of a complexified real Schwartz function is Hermitian
  (public)
- `complexInner_compLpL_ofReal` — complex inner product of real-to-complex embeddings (public)
- `inner_L2VF_eq_sum_component` — the real `L2VF_R3` inner product as a sum over components
  (public; not individually named in the extraction contract, but is the sole dependency of
  `inner_L2VF_eq_integral_sum_fourier` immediately below, so it moves with it)
- `inner_L2VF_eq_integral_sum_fourier` — the vector Parseval bridge (public)
- `testSymbol`, `testSymbol_antiHermitian` — the Fourier test symbol and its anti-Hermitian
  symmetry. `testSymbol` kept public (not `private` as on `main`): `CurlDensity.lean`'s
  `antiHermitianTest_integral_zero` (see note below) references it by name.
- `reflect_fourier_schwartzC_eq_conj`, `fourier_ofReal_reflect_eq_conj` — the (P1) Lp-level
  Hermitian reflection identity (`private`)
- `fourier_hermitian_real` — reality of the Fourier transform of a Hermitian Schwartz function
  (public)
- `schwartz_antiHermitian_has_testSymbol_preimage` — the (P2) Schwartz surjectivity theorem.
  Kept public (not `private` as on `main`), same reason as `testSymbol` above.
- `ae_zero_of_hermitianTest`, `schwartz_hermitian_has_fourier_preimage` — the du Bois-Reymond
  even/odd reduction and its Hermitian-preimage consequence. Kept public (not `private` as on
  `main`): `CurlDensity.lean`'s remaining `mem_sigma_iff_fourier_transverse`/
  `orthogonalCurl_longitudinal_ae` content references them by name.

**Not moved despite being named in the original extraction scope:**
`antiHermitianTest_integral_zero`'s STATEMENT (not just its proof) mentions `transverseDefect`,
a `private` divergence/curl-specific definition that legitimately stays in `CurlDensity.lean` —
so despite living textually inside the "du Bois-Reymond block" on `main`, it is not itself
generic Fourier-analysis infrastructure and was left in `CurlDensity.lean`. Caught by the build
(`Function expected at transverseDefect` / `Unknown identifier`), not the tracing pass.

All public names/statements preserved from `CurlDensity.lean`.

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-- Complexification of a real Schwartz map by post-composing with `ℝ →L[ℝ] ℂ`. -/
noncomputable def schwartzC (f : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  f.postcompCLM (RCLike.ofRealCLM (K := ℂ))

/-- The complexification `schwartzC f` evaluates pointwise as the real-to-complex coercion of
`f`. -/
theorem schwartzC_apply (f : SchwartzMap Domain3 ℝ) (x : Domain3) :
    schwartzC f x = (f x : ℂ) := rfl

/-- The complex L²-class of a complexified real Schwartz map is the `compLpL`-embedding of the
real class — i.e. exactly `potentialComponentC`-shaped. -/
theorem toLp_schwartzC_eq (f : SchwartzMap Domain3 ℝ) :
    (schwartzC f).toLp 2 (volume : Measure Domain3)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
          (f.toLp 2 (volume : Measure Domain3)) := by
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  refine Lp.ext ?_
  filter_upwards [(schwartzC f).coeFn_toLp 2 (volume : Measure Domain3),
    (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (f.toLp 2 (volume : Measure Domain3)),
    f.coeFn_toLp 2 (volume : Measure Domain3)] with x hx hc hf
  rw [hx, hc, hf, schwartzC_apply, RCLike.ofRealCLM_apply]
  rfl

/-- Line derivative commutes with complexification: `∂_m (schwartzC f) = schwartzC (∂_m f)`.

Moved here from `CurlDensity.lean` (issue #113 PR-2), kept public (not `private` as on `main`):
`CurlDensity.lean`'s own remaining Schwartz-Fourier machinery and `StokesFourier.lean` both
reference it and `fourier_schwartzC_lineDeriv_apply` by name. -/
theorem lineDerivOp_schwartzC (f : SchwartzMap Domain3 ℝ) (m : Domain3) :
    (∂_{m} (schwartzC f)) = schwartzC (∂_{m} f) := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, schwartzC_apply, lineDerivOp_apply_eq_fderiv]
  -- `schwartzC f = ofRealCLM ∘ f`; push fderiv through the CLM
  have hcomp : ((schwartzC f : Domain3 → ℂ))
      = (RCLike.ofRealCLM (K := ℂ)) ∘ (f : Domain3 → ℝ) := by
    funext y; rw [schwartzC_apply]; rfl
  rw [hcomp]
  rw [fderiv_comp x (RCLike.ofRealCLM (K := ℂ)).differentiableAt
    (f.smooth 1).differentiable_one.differentiableAt]
  rw [(RCLike.ofRealCLM (K := ℂ)).fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- Pointwise Fourier symbol of the complexified line derivative: for a real Schwartz `f` and
direction `m`, the Schwartz Fourier transform of `schwartzC (∂_m f)` at `ξ` is
`(2π i)(inner ℝ ξ m)·𝓕(schwartzC f)(ξ)`.

This is `fourier_lineDerivOp_eq` applied to the complexified map `schwartzC f`, using
`lineDerivOp_schwartzC` to identify `schwartzC (∂_m f) = ∂_m (schwartzC f)`. -/
theorem fourier_schwartzC_lineDeriv_apply
    (f : SchwartzMap Domain3 ℝ) (m : Domain3) (ξ : Domain3) :
    (𝓕 (schwartzC (∂_{m} f)) : SchwartzMap Domain3 ℂ) ξ
      = (2 * Real.pi * Complex.I) * ((inner ℝ ξ m : ℝ) : ℂ)
          * ((𝓕 (schwartzC f) : SchwartzMap Domain3 ℂ) ξ) := by
  have hC : schwartzC (∂_{m} f) = ∂_{m} (schwartzC f) := (lineDerivOp_schwartzC f m).symm
  rw [hC]
  have hg : (inner ℝ · m : Domain3 → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hkey := SchwartzMap.fourier_lineDerivOp_eq (schwartzC f) m
  rw [hkey]
  -- evaluate the RHS SchwartzMap at `ξ`
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [smul_eq_mul, Complex.real_smul]
  ring

/-- **Fourier of a real function is Hermitian.**  For a real Schwartz `φ`, the Fourier
transform of its complexification satisfies `𝓕(schwartzC φ)(-ξ) = conj (𝓕(schwartzC φ)(ξ))`.

This is the conjugate symmetry of the Fourier transform of a (complexified) real function:
pushing `conj` through the integral defining `𝓕`, the unit-modulus character contributes
`conj(𝐞(-⟪v,ξ⟫)) = 𝐞(⟪v,ξ⟫) = 𝐞(-⟪v,-ξ⟫)`, while `conj` acts trivially on the real-valued
integrand `schwartzC φ`. -/
theorem fourier_schwartzC_hermitian (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) :
    (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) (-ξ)
      = (starRingEnd ℂ) ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) := by
  -- Move to the underlying function `𝓕 (schwartzC φ : Domain3 → ℂ)`.
  have hcoe : ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) : Domain3 → ℂ)
        = 𝓕 ((schwartzC φ : Domain3 → ℂ)) := SchwartzMap.fourier_coe (schwartzC φ)
  rw [show (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) (-ξ)
        = 𝓕 ((schwartzC φ : Domain3 → ℂ)) (-ξ) from congrFun hcoe (-ξ),
    show (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ
        = 𝓕 ((schwartzC φ : Domain3 → ℂ)) ξ from congrFun hcoe ξ]
  -- RHS: push `conj` into the integral defining `𝓕 _ ξ`.
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards with v
  -- Convert both `Circle` actions to complex multiplication.
  simp only [Circle.smul_def, smul_eq_mul, inner_neg_right, map_mul, schwartzC_apply,
    Complex.conj_ofReal, neg_neg]
  -- character: `(𝐞 (⟪v,ξ⟫) : ℂ) = conj ((𝐞 (-⟪v,ξ⟫) : ℂ))`
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-- The complex L²-inner product of the complexifications of two real Lp components equals the
cast of their real L²-inner product.  Both sides are the integral of the pointwise product. -/
theorem complexInner_compLpL_ofReal
    (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    (inner ℂ ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a)
        ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) b) : ℂ)
      = ((inner ℝ a b : ℝ) : ℂ) := by
  -- real inner as an integral of the pointwise product
  have hreal : (inner ℝ a b : ℝ)
      = ∫ x, (a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x ∂(volume : Measure Domain3) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [RCLike.inner_apply, conj_trivial]
    ring
  -- complex inner as the integral of the cast of the pointwise product
  rw [MeasureTheory.L2.inner_def, hreal]
  calc (∫ x, (inner ℂ
        (((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a : Domain3 → ℂ) x)
        (((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) b : Domain3 → ℂ) x) : ℂ)
          ∂(volume : Measure Domain3))
      = ∫ x, (((a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x : ℝ) : ℂ)
          ∂(volume : Measure Domain3) := by
        refine integral_congr_ae ?_
        filter_upwards [(RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL a,
          (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL b] with x hax hbx
        rw [hax, hbx]
        simp only [RCLike.ofRealCLM_apply, RCLike.inner_apply, RCLike.conj_ofReal]
        rw [mul_comm]
        norm_cast
    _ = ((∫ x, (a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x ∂(volume : Measure Domain3) : ℝ) : ℂ) :=
        integral_ofReal

/-- **Component decomposition of the `L2VF_R3` inner product.**  The real inner product on
`L2VF_R3 = L²(ℝ³; ℝ³)` is the sum over the three coordinates of the component inner products. -/
theorem inner_L2VF_eq_sum_component (a b : L2VF_R3) :
    (inner ℝ a b : ℝ)
      = ∑ j : Fin 3, (inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ) := by
  -- each component inner as an integral of the pointwise product
  have hcomp : ∀ j : Fin 3,
      (inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ)
        = ∫ x, (L2VF_projComponent_R3 j a : Domain3 → ℝ) x
            * (L2VF_projComponent_R3 j b : Domain3 → ℝ) x ∂(volume : Measure Domain3) := by
    intro j
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]; ring
  have hint : ∀ j : Fin 3, Integrable (fun x => (L2VF_projComponent_R3 j a : Domain3 → ℝ) x
      * (L2VF_projComponent_R3 j b : Domain3 → ℝ) x) (volume : Measure Domain3) := by
    intro j
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
      (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b)
    refine hI.congr ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]; ring
  simp_rw [hcomp]
  rw [← integral_finsetSum _ (fun j _ => hint j), MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  -- a.e. each component coercion is the coordinate projection of `a x`, `b x`
  have hcoe : ∀ᵐ x ∂(volume : Measure Domain3), ∀ j : Fin 3,
      (L2VF_projComponent_R3 j a : Domain3 → ℝ) x = (a : Domain3 → EuclideanSpace ℝ (Fin 3)) x j
        ∧ (L2VF_projComponent_R3 j b : Domain3 → ℝ) x = (b : Domain3 → EuclideanSpace ℝ (Fin 3)) x j := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL a,
      (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL b] with x hax hbx
    exact ⟨hax, hbx⟩
  filter_upwards [hcoe] with x hx
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [RCLike.inner_apply, conj_trivial, (hx j).1, (hx j).2]
  ring

/-- **Vector Parseval bridge.**  The (complexified) real inner product of two velocity fields
equals the integral of the three-component sum of Hermitian products of their complex component
Fourier transforms:
`⟪u, w⟫ = ∫ ∑_j conj(û_j(ξ)) · ŵ_j(ξ) dξ`, where `û_j = 𝓕 (L2VF_projComponentC_R3 j u)`.

Assembles `inner_L2VF_eq_sum_component` (vector → component inners), `complexInner_compLpL_ofReal`
(real → complex component inner), `Lp.inner_fourier_eq` (Plancherel per component), and the
finite-sum/integral swap. -/
theorem inner_L2VF_eq_integral_sum_fourier (a b : L2VF_R3) :
    ((inner ℝ a b : ℝ) : ℂ)
      = ∫ ξ : Domain3, ∑ j : Fin 3,
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
            * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ
        ∂(volume : Measure Domain3) := by
  -- component inner products, complexified and Planchereled
  have hcomp : ∀ j : Fin 3,
      ((inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ) : ℂ)
        = ∫ ξ : Domain3,
            (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
              * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ ∂(volume : Measure Domain3) := by
    intro j
    rw [← complexInner_compLpL_ofReal (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b)]
    -- the complexified component is `L2VF_projComponentC_R3 j`
    rw [show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
            (L2VF_projComponent_R3 j a) = L2VF_projComponentC_R3 j a from
          (ContinuousLinearMap.comp_apply _ _ _).symm,
      show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
            (L2VF_projComponent_R3 j b) = L2VF_projComponentC_R3 j b from
          (ContinuousLinearMap.comp_apply _ _ _).symm]
    rw [← MeasureTheory.Lp.inner_fourier_eq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with ξ
    simp only [RCLike.inner_apply]; ring
  -- integrability of each Fourier-side component integrand
  have hint : ∀ j : Fin 3, Integrable
      (fun ξ : Domain3 => (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
        * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ) (volume : Measure Domain3) := by
    intro j
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (𝓕 (L2VF_projComponentC_R3 j a)) (𝓕 (L2VF_projComponentC_R3 j b))
    refine hI.congr ?_
    filter_upwards with ξ
    simp only [RCLike.inner_apply]; ring
  rw [show ((inner ℝ a b : ℝ) : ℂ)
        = ((∑ j : Fin 3, (inner ℝ (L2VF_projComponent_R3 j a)
            (L2VF_projComponent_R3 j b) : ℝ) : ℝ) : ℂ) from by rw [inner_L2VF_eq_sum_component]]
  push_cast
  rw [Finset.sum_congr rfl (fun j _ => hcomp j)]
  rw [integral_finsetSum _ (fun j _ => hint j)]

/-- The Fourier test symbol attached to a real Schwartz `φ` in the weak-divergence pairing:
`testSymbol φ ξ = conj((2π i)·𝓕(schwartzC φ)(ξ))`.  As `φ` ranges over all real Schwartz
functions this is exactly the available family of test symbols paired against the transverse
defect in `divTestFunctional_eq_fourier_integral` / `mem_sigma_iff_fourier_integral_zero`. -/
noncomputable def testSymbol (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) : ℂ :=
  (starRingEnd ℂ)
    ((2 * Real.pi * Complex.I) * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)

/-! #### (P1) Lp-level Hermitian reflection of the Fourier transform of a real component

The a.e. Hermitian symmetry of the L²-Fourier transform of a *complexified real* `Lp`
function: `(𝓕 (ofReal ∘ a))(-ξ) =ᵐ conj((𝓕 (ofReal ∘ a)) ξ)`.  This is the `(-·)` analogue
of `FourierL2.fourier_translate_eq`, proved by the same `DenseRange.induction_on` template over
the real Schwartz functions, with base case the already-proved Schwartz-level
`fourier_schwartzC_hermitian`.  The two sides are realised as honest `Lp` operations:
reflection `g ↦ g ∘ (-·)` (`Lp.compMeasurePreserving Neg.neg`, the measure-preserving negation
involution on `volume`) and conjugation `g ↦ conj ∘ g` (`Complex.conjCLE.compLpL`).

This discharges what was, in the forward direction below, the first of two named analytic
blockers (the `(P1)` reflection identity).  It is genuine analysis, axiom-free, no `sorry`. -/

/-- **Reality of the Fourier transform of a Hermitian Schwartz function.**  If
`g : 𝓢(ℝ³, ℂ)` is Hermitian (`g(-v) = conj(g(v))` for all `v`), then `𝓕 g` is real-valued:
`conj(𝓕 g ξ) = 𝓕 g ξ`.

Pointwise integral argument (mirrors `fourier_schwartzC_hermitian`): pushing `conj` into the
integral defining `𝓕 g ξ = ∫ 𝐞(-⟪v,ξ⟫) g v` turns the unit-modulus character into its
inverse `𝐞(⟪v,ξ⟫)` and conjugates the integrand to `g(-v)` (Hermitian); the substitution
`v ↦ -v` (negation is measure preserving) restores `∫ 𝐞(-⟪v,ξ⟫) g v = 𝓕 g ξ`. -/
theorem fourier_hermitian_real
    (g : SchwartzMap Domain3 ℂ)
    (hg : ∀ v : Domain3, g (-v) = (starRingEnd ℂ) (g v)) (ξ : Domain3) :
    (starRingEnd ℂ) ((𝓕 g : SchwartzMap Domain3 ℂ) ξ) = (𝓕 g : SchwartzMap Domain3 ℂ) ξ := by
  -- Move to the underlying function `𝓕 (g : Domain3 → ℂ)`.
  have hcoe : ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((g : Domain3 → ℂ)) :=
    SchwartzMap.fourier_coe g
  rw [show (𝓕 g : SchwartzMap Domain3 ℂ) ξ = 𝓕 ((g : Domain3 → ℂ)) ξ from congrFun hcoe ξ]
  -- LHS: push `conj` into the integral defining `𝓕 _ ξ`.
  rw [Real.fourier_eq, ← integral_conj]
  -- Conjugated integrand `conj(𝐞(-⟪v,ξ⟫) • g v) = 𝐞(⟪v,ξ⟫) • g(-v)`.
  have hconj : (∫ v : Domain3, (starRingEnd ℂ) ((Real.fourierChar (-(inner ℝ v ξ : ℝ))) • g v)
        ∂(volume : Measure Domain3))
      = ∫ v : Domain3, (Real.fourierChar (-(inner ℝ (-v) ξ : ℝ))) • g (-v)
        ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards with v
    simp only [Circle.smul_def, smul_eq_mul, inner_neg_left, map_mul, neg_neg]
    rw [hg v]
    -- character: `conj((𝐞 (-⟪v,ξ⟫) : ℂ)) = (𝐞 (⟪v,ξ⟫) : ℂ)`
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]
  rw [hconj]
  -- substitute `v ↦ -v`: `∫ F(-v) = ∫ F(v)`, recovering `𝓕 g ξ`.
  rw [integral_neg_eq_self (fun v => (Real.fourierChar (-(inner ℝ v ξ : ℝ))) • g v)
    (volume : Measure Domain3)]

/-- **(P2) Schwartz Hermitian preimage extraction (must-prove — item 11 in the plan).**

If `h : 𝓢(ℝ³, ℂ)` is anti-Hermitian in the sense `h(-ξ) = -conj(h(ξ))` (i.e. `h` is an
anti-Hermitian Schwartz symbol, exactly the kind produced by `testSymbol φ` for real `φ`),
then there exists `φ : 𝓢(ℝ³, ℝ)` such that `testSymbol φ = h`.

**Constructibility sketch** (no Mathlib PR needed — all primitives present):
- Let `g = (2πi)⁻¹ • h` (Hermitian: `g(-ξ) = conj(g(ξ))`).
- Let `Ψ : 𝓢(ℝ³, ℂ)` be the Schwartz inverse Fourier transform `𝓕⁻ g`
  (`FourierTransform.fourierCLE.symm` applied to `g`).
- Since `g` is Hermitian, `Ψ` is real-valued: use `fourier_ofReal_reflect_eq_conj` (proved,
  P1 above) to establish that `𝓕⁻ g` is real-valued, so `Im Ψ = 0`.
- Extract the real Schwartz function `φ := Ψ.postcompCLM reCLM`
  (via `SchwartzMap.postcompCLM (RCLike.reCLM : ℂ →L[ℝ] ℝ)`, which gives `φ ξ = Re(Ψ ξ)`).
- Verify `testSymbol φ = h`:
  `testSymbol φ ξ = conj((2πi) · 𝓕(schwartzC φ)(ξ))`.
  Since `Ψ` is real-valued, `schwartzC φ = schwartzC (Re Ψ) = Ψ` (as Schwartz maps).
  Then `𝓕(Ψ) = 𝓕(𝓕⁻ g) = g` by `FourierInvPair`, and `conj((2πi)·g) = h` by definition of `g`.

Key Mathlib decls: `SchwartzMap.postcompCLM`, `Complex.conjCLE`, `RCLike.reCLM`,
`FourierTransform.fourierCLE` (symm), `FourierInvPair`,
`fourier_ofReal_reflect_eq_conj` (item 9, proved above). -/
theorem schwartz_antiHermitian_has_testSymbol_preimage
    (h : SchwartzMap Domain3 ℂ)
    (hH : ∀ ξ : Domain3, h (-ξ) = -(starRingEnd ℂ) (h ξ)) :
    ∃ φ : SchwartzMap Domain3 ℝ, testSymbol φ = h := by
  -- The factor `c = 2π i` and its (non-zero) inverse.
  set c : ℂ := 2 * Real.pi * Complex.I with hc
  have hcne : c ≠ 0 := by
    rw [hc]; simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- `conj c = -c`.
  have hconjc : (starRingEnd ℂ) c = -c := by
    rw [hc, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    ring
  -- `g := c⁻¹ • (conj ∘ h)`, a Schwartz map with `g ξ = c⁻¹ * conj (h ξ)`.
  set g : SchwartzMap Domain3 ℂ :=
    c⁻¹ • (h.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) with hgdef
  have hg_apply : ∀ ξ : Domain3, g ξ = c⁻¹ * (starRingEnd ℂ) (h ξ) := by
    intro ξ
    rw [hgdef, smul_apply, SchwartzMap.postcompCLM_apply, smul_eq_mul]
    rfl
  -- `g` is Hermitian: `g (-ξ) = conj (g ξ)`.
  have hgHerm : ∀ ξ : Domain3, g (-ξ) = (starRingEnd ℂ) (g ξ) := by
    intro ξ
    rw [hg_apply, hg_apply, hH ξ, map_mul, Complex.conj_conj, map_neg, Complex.conj_conj,
      map_inv₀, hconjc]
    ring
  -- `Φ := 𝓕⁻ g`, the Schwartz inverse Fourier transform of `g`.
  set Φ : SchwartzMap Domain3 ℂ := 𝓕⁻ g with hΦdef
  -- `Φ` is real-valued: `conj (Φ ξ) = Φ ξ`.
  have hΦreal : ∀ ξ : Domain3, (starRingEnd ℂ) (Φ ξ) = Φ ξ := by
    intro ξ
    -- pointwise `𝓕⁻ g ξ = 𝓕 g (-ξ)`.
    have hcoeInv : (Φ : Domain3 → ℂ) = 𝓕⁻ ((g : Domain3 → ℂ)) := by
      rw [hΦdef]; exact SchwartzMap.fourierInv_coe g
    have hcoeF : ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((g : Domain3 → ℂ)) :=
      SchwartzMap.fourier_coe g
    have hΦpt : Φ ξ = (𝓕 g : SchwartzMap Domain3 ℂ) (-ξ) := by
      rw [show Φ ξ = (Φ : Domain3 → ℂ) ξ from rfl, hcoeInv,
        Real.fourierInv_eq_fourier_neg,
        show 𝓕 ((g : Domain3 → ℂ)) (-ξ) = ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) (-ξ)
          from (congrFun hcoeF (-ξ)).symm]
    rw [hΦpt, fourier_hermitian_real g hgHerm]
  -- `φ := Re ∘ Φ` as a real Schwartz function.
  refine ⟨Φ.postcompCLM (RCLike.reCLM (K := ℂ)), ?_⟩
  -- `schwartzC φ = Φ` (since `Φ` is real-valued).
  have hschwartzCφ : schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ))) = Φ := by
    apply SchwartzMap.ext
    intro ξ
    rw [schwartzC_apply, SchwartzMap.postcompCLM_apply, RCLike.reCLM_apply]
    -- `(Re (Φ ξ) : ℂ) = Φ ξ` because `Φ ξ` is real (`conj = id`).
    have := hΦreal ξ
    rw [Complex.conj_eq_iff_re] at this
    rw [RCLike.re_to_complex]
    exact this
  -- `𝓕 (schwartzC φ) = 𝓕 Φ = 𝓕 (𝓕⁻ g) = g`.
  have hFourierφ : (𝓕 (schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ))))
      : SchwartzMap Domain3 ℂ) = g := by
    rw [hschwartzCφ, hΦdef, fourier_fourierInv_eq]
  -- Finish: `testSymbol φ ξ = conj (c · g ξ) = conj (conj (h ξ)) = h ξ`.
  funext ξ
  rw [testSymbol]
  rw [show (𝓕 (schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ)))) : SchwartzMap Domain3 ℂ) ξ
      = g ξ from congrFun (congrArg (fun (f : SchwartzMap Domain3 ℂ) => (f : Domain3 → ℂ))
        hFourierφ) ξ]
  rw [hg_apply ξ, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul, Complex.conj_conj]

/-- **General du-Bois-Reymond against Hermitian Schwartz tests.**  A locally integrable
`f : ℝ³ → ℂ` that integrates to zero against every *Hermitian* Schwartz symbol
(`G(-ξ) = conj(G ξ)`) vanishes a.e.

Same even/odd reduction as the forward direction of `mem_sigma_iff_fourier_transverse`, but
the parity assignment is mirrored: for a real smooth compactly-supported test `g`, the
even part `gE = g + g∘neg` complexifies to a *Hermitian* symbol directly, while `i·gO`
(`gO = g − g∘neg`) is Hermitian; both feed the hypothesis, and `2g = gE + gO`. -/
theorem ae_zero_of_hermitianTest
    (f : Domain3 → ℂ) (hf : LocallyIntegrable f (volume : Measure Domain3))
    (htest : ∀ G : SchwartzMap Domain3 ℂ, (∀ ξ : Domain3, G (-ξ) = (starRingEnd ℂ) (G ξ)) →
        ∫ ξ : Domain3, (G : Domain3 → ℂ) ξ * f ξ ∂(volume : Measure Domain3) = 0) :
    ∀ᵐ ξ ∂(volume : Measure Domain3), f ξ = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf ?_
  intro g g_diff g_supp
  have hneg_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => g (-ξ)) :=
    g_diff.comp contDiff_neg
  have hneg_supp : HasCompactSupport (fun ξ : Domain3 => g (-ξ)) := by
    have := g_supp.comp_homeomorph (Homeomorph.neg Domain3)
    simpa [Function.comp_def] using this
  set gE : Domain3 → ℝ := fun ξ => g ξ + g (-ξ) with hgE
  set gO : Domain3 → ℝ := fun ξ => g ξ - g (-ξ) with hgO
  have hgE_diff : ContDiff ℝ (⊤ : ℕ∞) gE := g_diff.add hneg_diff
  have hgO_diff : ContDiff ℝ (⊤ : ℕ∞) gO := g_diff.sub hneg_diff
  have hgE_supp : HasCompactSupport gE := g_supp.add hneg_supp
  have hgO_supp : HasCompactSupport gO := g_supp.sub hneg_supp
  -- complexifications: `gE` (Hermitian) and `i·gO` (Hermitian).
  have hCE_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => (gE ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hgE_diff
  have hCE_supp : HasCompactSupport (fun ξ : Domain3 => (gE ξ : ℂ)) :=
    hgE_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hCO_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => Complex.I * (gO ξ : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hgO_diff)
  have hCO_supp : HasCompactSupport (fun ξ : Domain3 => Complex.I * (gO ξ : ℂ)) :=
    (hgO_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_left
  set hE : SchwartzMap Domain3 ℂ := hCE_supp.toSchwartzMap hCE_diff with hhE
  set hO : SchwartzMap Domain3 ℂ := hCO_supp.toSchwartzMap hCO_diff with hhO
  have hE_coe : ∀ ξ : Domain3, hE ξ = (gE ξ : ℂ) := fun _ => rfl
  have hO_coe : ∀ ξ : Domain3, hO ξ = Complex.I * (gO ξ : ℂ) := fun _ => rfl
  -- Hermitian conditions.
  have hE_H : ∀ ξ : Domain3, hE (-ξ) = (starRingEnd ℂ) (hE ξ) := by
    intro ξ
    rw [hE_coe, hE_coe]
    have heq : gE (-ξ) = gE ξ := by simp only [hgE, neg_neg]; ring
    rw [heq, Complex.conj_ofReal]
  have hO_H : ∀ ξ : Domain3, hO (-ξ) = (starRingEnd ℂ) (hO ξ) := by
    intro ξ
    rw [hO_coe, hO_coe]
    have heq : gO (-ξ) = -gO ξ := by simp only [hgO, neg_neg]; ring
    rw [heq, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
  have hEZero := htest hE hE_H
  have hOZero := htest hO hO_H
  simp only [hE_coe, hO_coe] at hEZero hOZero
  -- integrability of the compactly-supported pieces against the locally integrable `f`.
  have hInt : ∀ k : Domain3 → ℝ, Continuous k → HasCompactSupport k →
      Integrable (fun ξ : Domain3 => (k ξ : ℂ) * f ξ) (volume : Measure Domain3) := by
    intro k hk_cont hk_supp
    have := hf.integrable_smul_left_of_hasCompactSupport (𝕜 := ℂ)
      (g := fun ξ : Domain3 => (k ξ : ℂ))
      (Complex.continuous_ofReal.comp hk_cont)
      (hk_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    simpa [smul_eq_mul] using this
  have hIntE := hInt gE hgE_diff.continuous hgE_supp
  have hIntO := hInt gO hgO_diff.continuous hgO_supp
  -- `∫ (gO:ℂ)·f = 0` (drop the `Complex.I` factor from `hOZero`).
  have hOZero' : ∫ ξ : Domain3, (gO ξ : ℂ) * f ξ ∂(volume : Measure Domain3) = 0 := by
    have hI : Complex.I * ∫ ξ : Domain3, (gO ξ : ℂ) * f ξ ∂(volume : Measure Domain3) = 0 := by
      rw [← integral_const_mul]
      simp_rw [← mul_assoc]
      exact hOZero
    exact (mul_eq_zero.1 hI).resolve_left Complex.I_ne_zero
  -- assemble: `∫ g•f = (∫ gE·f + ∫ gO·f)/2 = 0`.
  have hsplit : ∀ ξ : Domain3,
      (g ξ : ℂ) * f ξ
        = (2 : ℂ)⁻¹ * ((gE ξ : ℂ) * f ξ + (gO ξ : ℂ) * f ξ) := by
    intro ξ
    simp only [hgE, hgO]
    push_cast
    ring
  calc ∫ ξ : Domain3, g ξ • f ξ ∂(volume : Measure Domain3)
      = ∫ ξ : Domain3, (2 : ℂ)⁻¹ * ((gE ξ : ℂ) * f ξ + (gO ξ : ℂ) * f ξ)
          ∂(volume : Measure Domain3) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        rw [Complex.real_smul, hsplit ξ]
    _ = (2 : ℂ)⁻¹ * (∫ ξ : Domain3, ((gE ξ : ℂ) * f ξ + (gO ξ : ℂ) * f ξ)
          ∂(volume : Measure Domain3)) := by rw [integral_const_mul]
    _ = (2 : ℂ)⁻¹ * ((∫ ξ : Domain3, (gE ξ : ℂ) * f ξ ∂(volume : Measure Domain3))
          + ∫ ξ : Domain3, (gO ξ : ℂ) * f ξ ∂(volume : Measure Domain3)) := by
        rw [integral_add hIntE hIntO]
    _ = 0 := by rw [hEZero, hOZero']; ring

/-- **Hermitian Schwartz preimage under `𝓕 ∘ schwartzC`.**  Every Hermitian Schwartz symbol
`G` (`G(-ξ) = conj(G ξ)`) is `𝓕 (schwartzC φ)` for some *real* Schwartz `φ`.  Same construction
as `schwartz_antiHermitian_has_testSymbol_preimage` (P2), minus the `testSymbol` wrapper:
`Φ = 𝓕⁻ G` is real-valued (`fourier_hermitian_real`), `φ = Re ∘ Φ`, and
`𝓕 (schwartzC φ) = 𝓕 (𝓕⁻ G) = G`. -/
theorem schwartz_hermitian_has_fourier_preimage
    (G : SchwartzMap Domain3 ℂ) (hH : ∀ ξ : Domain3, G (-ξ) = (starRingEnd ℂ) (G ξ)) :
    ∃ φ : SchwartzMap Domain3 ℝ, (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) = G := by
  set Φ : SchwartzMap Domain3 ℂ := 𝓕⁻ G with hΦdef
  have hΦreal : ∀ ξ : Domain3, (starRingEnd ℂ) (Φ ξ) = Φ ξ := by
    intro ξ
    have hcoeInv : (Φ : Domain3 → ℂ) = 𝓕⁻ ((G : Domain3 → ℂ)) := by
      rw [hΦdef]; exact SchwartzMap.fourierInv_coe G
    have hcoeF : ((𝓕 G : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((G : Domain3 → ℂ)) :=
      SchwartzMap.fourier_coe G
    have hΦpt : Φ ξ = (𝓕 G : SchwartzMap Domain3 ℂ) (-ξ) := by
      rw [show Φ ξ = (Φ : Domain3 → ℂ) ξ from rfl, hcoeInv,
        Real.fourierInv_eq_fourier_neg,
        show 𝓕 ((G : Domain3 → ℂ)) (-ξ) = ((𝓕 G : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) (-ξ)
          from (congrFun hcoeF (-ξ)).symm]
    rw [hΦpt, fourier_hermitian_real G hH]
  refine ⟨Φ.postcompCLM (RCLike.reCLM (K := ℂ)), ?_⟩
  have hschwartzCφ : schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ))) = Φ := by
    apply SchwartzMap.ext
    intro ξ
    rw [schwartzC_apply, SchwartzMap.postcompCLM_apply, RCLike.reCLM_apply]
    have := hΦreal ξ
    rw [Complex.conj_eq_iff_re] at this
    rw [RCLike.re_to_complex]
    exact this
  rw [hschwartzCφ, hΦdef, fourier_fourierInv_eq]

end LerayHopf
