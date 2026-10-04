import Tengoku.LerayHopf.LerayHopf.R3.Regularity
import Tengoku

open MeasureTheory FourierTransform TemperedDistribution Complex
open scoped FourierTransform SchwartzMap RealInnerProductSpace ENNReal

/-!
# Shared Fourier–L² foundation (`FourierL2`)

**Milestone id:** `fourier-foundation-bd` — PHASE 0 (foundation, blocking).

This file is the **shared Fourier–L² foundation** consumed by Pillar B's T0b
(`RellichBall.lean`, via the Lp-level modulation identity F5 and the Plancherel weight
bookkeeping F7–F9) and, later, by Pillar D (`SchwartzDivFreeBasis.lean`, via the Schwartz↔Lp
Fourier bridge F4/F6 and a future Fourier-of-curl multiplier).

It supplies BOTH:

* the **Lp-level translation→modulation identity** for `Lp.fourierTransformₗᵢ` — the piece
  that `RellichBall.lean:181-193` flagged as the (real but reducible) blocker — assembled from
  a bounded phase multiplier `phaseMulCLM` (F2), the Schwartz-level modulation F4, and the
  `DenseRange.induction_on` density extension F5 (template:
  `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`); and
* the **Plancherel weight bookkeeping** (F7) plus the pointwise phase estimate (F9) needed to
  bound `‖τ_h c − c‖²` by `‖h‖² · viscousFormSq_R3 1 w` componentwise (F8).

## Convention contract (the highest-priority audit point)

The ℝ³ Fourier transform here is mathlib's `EuclideanSpace`-level transform, with character
`𝐞 = Real.fourierChar`, bilinear form `innerₗ V`, and Lebesgue `volume`:

  `𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v`,   where `𝐞 x = Complex.exp (↑(2 * π * x) * I)`.

(`Mathlib.Analysis.Fourier.FourierTransform`, `Real.instFourierTransform`,
`Real.fourier_eq`, `Real.fourierChar_apply`.)

The raw translation→modulation identity
`VectorFourier.fourierIntegral_comp_add_right` then reads, with `L = innerₗ V` and `v₀ = h`,

  `𝓕 (f ∘ (· + h)) w = 𝐞 (⟪h, w⟫) • 𝓕 f w`,

so right-translation by `h` produces the phase factor
`𝐞 (⟪h, w⟫) = Complex.exp (2 * π * I * ⟪h, w⟫)`.  This is exactly `phaseFun h w` (F1), and it
is consistent with the `(2π)²‖ξ‖²` weight in `viscousFormSq_R3` (`Regularity.lean:140`): the
phase derivative `∂` of `𝐞 (⟪h, ξ⟫)` at `h = 0` is `2π i ξ`, whence `‖phaseFun h ξ − 1‖²`
is controlled by `(2π)²‖h‖²‖ξ‖²` (F9), matching the F7 weight.

## Main declarations

* `phaseFun`                                  (F1) — the unimodular modulation phase `ξ ↦ 𝐞 ⟪h,ξ⟫`.
* `norm_phaseFun_eq_one`                       (F1) — `‖phaseFun h ξ‖ = 1`.
* `phaseMulCLM`                                (F2) — bounded (op-norm ≤ 1) Lp phase multiplier.
* `coeFn_phaseMulCLM`                          (F3) — a.e. characterization of `phaseMulCLM`.
* `toLp_fourier_compMeasurePreserving_eq`      (F4) — Schwartz-level modulation identity.
* `fourier_translate_eq`                       (F5) — Lp-level modulation identity (the crux).
* `fourierComponentC_ae_schwartz`             (F6) — Fourier of a Schwartz-rep component is a.e. Schwartz.
* `viscousFormSq_R3_eq_integral_normSq_fourier` (F7) — Plancherel weight bookkeeping (named exposure).
* `normSq_sub_eq_integral_phase_sub`          (F8) — Plancherel core helper for `‖𝓕(τ_h c) − 𝓕 c‖²`.
* `normSq_phaseFun_sub_one_le`                (F9) — pointwise `‖phaseFun h ξ − 1‖² ≤ (2π)²‖h‖²‖ξ‖²`.

## Assumptions

None.  This file introduces **no** `axiom`/`opaque`/`unsafe` and must NOT import
`SolutionInterfaces` (the NS axioms must stay out of its `#print axioms`).

All of F1–F9 (and the linearity/bound fields of F2) are fully proved, `sorry`-free, with
`#print axioms` showing only `[propext, Classical.choice, Quot.sound]`.
-/

namespace LerayHopf

namespace FourierL2

/-! ### F1 — the unimodular modulation phase -/

/-- The **modulation phase** `phaseFun h ξ = 𝐞 ⟪h, ξ⟫ = Complex.exp (2π i ⟪h, ξ⟫)`.

This is the phase factor produced by right-translation by `h` under the ℝ³ Fourier transform
(see the convention contract in the module docstring): for `f ∘ (· + h)`,
`𝓕 (f ∘ (· + h)) ξ = phaseFun h ξ • 𝓕 f ξ`. -/
noncomputable def phaseFun (h : Domain3) : Domain3 → ℂ :=
  fun ξ => (Real.fourierChar (inner ℝ h ξ) : ℂ)

/-- The modulation phase is unimodular: `‖phaseFun h ξ‖ = 1`.

Proof sketch: `Real.fourierChar t` lands in `Circle`, and `‖(c : ℂ)‖ = 1` for `c : Circle`
(`Circle.norm_coe` / `Complex.norm_exp_ofReal_mul_I`-style unimodularity). -/
theorem norm_phaseFun_eq_one (h : Domain3) (ξ : Domain3) : ‖phaseFun h ξ‖ = 1 := by
  simp only [phaseFun]
  exact Circle.norm_coe _

/-- The modulation phase `phaseFun h` is continuous: it is the composition of the continuous
inner product `ξ ↦ ⟪h, ξ⟫`, the continuous character `Real.fourierChar`, and the continuous
`Circle → ℂ` coercion. -/
private theorem continuous_phaseFun (h : Domain3) : Continuous (phaseFun h) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

/-! ### F2 — bounded Lp phase multiplier

`phaseMulCLM h` is multiplication by the unimodular `phaseFun h` on `L²(ℝ³; ℂ)`, a bounded
operator of operator-norm ≤ 1.  Mathlib has no `boundedMulLp`, so it is built here:

1. `phaseMulMemLp` — the a.e. product `phaseFun h · g` stays in `MemLp 2` because `phaseFun h`
   is bounded (norm 1): `MemLp.of_bound`/`eLpNorm` monotone under `‖phaseFun h‖ ≤ 1`.
2. the underlying map `g ↦ (phaseMulMemLp h g).toLp …` is additive and ℂ-linear (a.e.);
3. it is bounded with `C = 1`, giving the CLM via `LinearMap.mkContinuous`.
-/

/-- The a.e. product `fun ξ => phaseFun h ξ * g ξ` stays in `MemLp 2` for `g : L2C_R3`, because
`‖phaseFun h ξ‖ = 1` is bounded (F1).

Proof sketch: `Lp.memLp g` gives `MemLp (g : Domain3 → ℂ) 2 volume`; bound the product
pointwise by `1 * ‖g ξ‖` via `norm_phaseFun_eq_one` and conclude with the `MemLp` mapping
under an a.e.-bounded measurable multiplier (`MemLp.of_le_mul` / `eLpNorm` monotonicity). -/
theorem phaseMulMemLp (h : Domain3) (g : L2C_R3) :
    MemLp (fun ξ : Domain3 => phaseFun h ξ * (g : Domain3 → ℂ) ξ) 2
      (volume : Measure Domain3) := by
  refine MemLp.of_le_mul (c := 1) (Lp.memLp g) ?_ ?_
  · exact ((continuous_phaseFun h).aestronglyMeasurable).mul (Lp.aestronglyMeasurable g)
  · filter_upwards with ξ
    rw [norm_mul, norm_phaseFun_eq_one, one_mul]

/-- The underlying ℂ-linear map of the phase multiplier: `g ↦ toLp (phaseFun h · * g ·)`. -/
noncomputable def phaseMulLM (h : Domain3) : L2C_R3 →ₗ[ℂ] L2C_R3 where
  toFun g := (phaseMulMemLp h g).toLp _
  map_add' := by
    intro g₁ g₂
    refine Lp.ext ?_
    filter_upwards [(phaseMulMemLp h (g₁ + g₂)).coeFn_toLp,
      Lp.coeFn_add ((phaseMulMemLp h g₁).toLp _) ((phaseMulMemLp h g₂).toLp _),
      (phaseMulMemLp h g₁).coeFn_toLp, (phaseMulMemLp h g₂).coeFn_toLp,
      Lp.coeFn_add g₁ g₂] with ξ h0 h1 h2 h3 h4
    rw [h0, h1, Pi.add_apply, h2, h3, h4, Pi.add_apply, mul_add]
  map_smul' := by
    intro c g
    refine Lp.ext ?_
    simp only [RingHom.id_apply]
    filter_upwards [(phaseMulMemLp h (c • g)).coeFn_toLp,
      Lp.coeFn_smul c ((phaseMulMemLp h g).toLp _),
      (phaseMulMemLp h g).coeFn_toLp, Lp.coeFn_smul c g] with ξ h0 h1 h2 h3
    rw [h0, h1, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- **F2.** Multiplication by the unimodular phase `phaseFun h` as a bounded continuous linear
map on `L²(ℝ³; ℂ)`, of operator norm ≤ 1.

This is the phase-multiplier operator absent from mathlib; it is the carrier of the Lp-level
modulation identity F5.  It is pinned a.e. by `coeFn_phaseMulCLM` (F3), confirming it is the
genuine phase multiplier (not a vacuous/zero CLM).

Built via `LinearMap.mkContinuous` with bound `C = 1` from `phaseMulLM` and the pointwise
unimodularity F1 (`‖phaseFun h ξ‖ = 1`), so `‖phaseMulCLM h g‖ ≤ 1 * ‖g‖`. -/
noncomputable def phaseMulCLM (h : Domain3) : L2C_R3 →L[ℂ] L2C_R3 :=
  (phaseMulLM h).mkContinuous 1 (by
    intro g
    rw [one_mul]
    show ‖(phaseMulMemLp h g).toLp _‖ ≤ ‖g‖
    rw [Lp.norm_toLp, Lp.norm_def]
    apply le_of_eq
    congr 1
    refine eLpNorm_congr_norm_ae ?_
    filter_upwards with ξ
    rw [norm_mul, norm_phaseFun_eq_one, one_mul])

/-! ### F3 — a.e. characterization of the phase multiplier -/

/-- **F3.** The phase multiplier acts a.e. as pointwise multiplication by `phaseFun h`.

This pins `phaseMulCLM` down as the genuine phase multiplier.

Proof sketch: unfold `phaseMulCLM`/`phaseMulLM` to `(phaseMulMemLp h g).toLp`, then
`MemLp.coeFn_toLp`. -/
theorem coeFn_phaseMulCLM (h : Domain3) (g : L2C_R3) :
    (phaseMulCLM h g : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => phaseFun h ξ * (g : Domain3 → ℂ) ξ := by
  show ((phaseMulMemLp h g).toLp _ : Domain3 → ℂ) =ᵐ[volume] _
  exact (phaseMulMemLp h g).coeFn_toLp

/-- The right-translation map `v ↦ v + h` on `Domain3` has temperate growth (it is the sum of
the identity and a constant). -/
private theorem hasTemperateGrowth_add_right (h : Domain3) :
    Function.HasTemperateGrowth (fun v : Domain3 => v + h) :=
  Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const h)

/-- The anti-growth bound `‖x‖ ≤ (1 + ‖h‖) * (1 + ‖x + h‖)^1` needed by `SchwartzMap.compCLM`
for the translation `v ↦ v + h`. -/
private theorem antiGrowth_add_right (h : Domain3) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : Domain3, ‖x‖ ≤ C * (1 + ‖x + h‖) ^ k := by
  refine ⟨1, 1 + ‖h‖, fun x => ?_⟩
  have hx : ‖x‖ ≤ ‖x + h‖ + ‖h‖ := by
    calc ‖x‖ = ‖(x + h) - h‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖x + h‖ + ‖h‖ := norm_sub_le _ _
  have h1 : (0:ℝ) ≤ ‖h‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖x + h‖ := norm_nonneg _
  rw [pow_one]
  nlinarith [hx, h1, h2]

/-- The Schwartz right-translate `ψ ∘ (· + h)` as a Schwartz map. -/
private noncomputable def schwartzTranslate (h : Domain3) (ψ : SchwartzMap Domain3 ℂ) :
    SchwartzMap Domain3 ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_add_right h) (antiGrowth_add_right h) ψ

private theorem schwartzTranslate_apply (h : Domain3) (ψ : SchwartzMap Domain3 ℂ) (x : Domain3) :
    schwartzTranslate h ψ x = ψ (x + h) := rfl

/-- The Lp translation `compMeasurePreserving (· + h)` of `ψ.toLp 2` equals the toLp of the
Schwartz translate `ψ ∘ (· + h)`. -/
private theorem compMeasurePreserving_toLp_eq (h : Domain3) (ψ : SchwartzMap Domain3 ℂ) :
    Lp.compMeasurePreserving (· + h)
        (measurePreserving_add_right (volume : Measure Domain3) h) (ψ.toLp 2)
      = (schwartzTranslate h ψ).toLp 2 := by
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving (ψ.toLp 2)
    (measurePreserving_add_right (volume : Measure Domain3) h)
  have h2 := ψ.coeFn_toLp 2 (volume : Measure Domain3)
  have h3 := (schwartzTranslate h ψ).coeFn_toLp 2 (volume : Measure Domain3)
  -- precompose the a.e. equality `ψ.toLp = ψ` with the measure-preserving translation
  have h2' : (fun x => (ψ.toLp 2 : Domain3 → ℂ) (x + h))
      =ᵐ[volume] fun x => ψ (x + h) :=
    (measurePreserving_add_right (volume : Measure Domain3) h).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2', h3] with x hx1 hx2 hx3
  rw [hx1, Function.comp_apply, hx2, hx3, schwartzTranslate_apply]

/-! ### F4 — Schwartz-level modulation -/

/-- The raw (Schwartz-level) modulation identity at every point: the Schwartz Fourier transform
of the translate `ψ ∘ (· + h)` equals the phase `phaseFun h ξ` times `𝓕 ψ ξ`. -/
private theorem fourier_schwartzTranslate_apply (h : Domain3) (ψ : SchwartzMap Domain3 ℂ)
    (ξ : Domain3) :
    (𝓕 (schwartzTranslate h ψ)) ξ = phaseFun h ξ * (𝓕 ψ) ξ := by
  -- pass to raw `fourierIntegral` via `fourier_coe`
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hcoe : ((schwartzTranslate h ψ : Domain3 → ℂ)) = (fun v => (ψ : Domain3 → ℂ) (v + h)) := by
    funext v; exact schwartzTranslate_apply h ψ v
  rw [hcoe]
  -- the raw transform of `(ψ : Domain3 → ℂ)` is `VectorFourier.fourierIntegral 𝐞 volume (innerₗ V)`
  have hmod := VectorFourier.fourierIntegral_comp_add_right
    (E := ℂ) Real.fourierChar (volume : Measure Domain3) (innerₗ Domain3)
    (ψ : Domain3 → ℂ) h
  -- `(fun v => ψ (v + h)) = (ψ : Domain3 → ℂ) ∘ (fun v => v + h)`
  have hcomp : (fun v => (ψ : Domain3 → ℂ) (v + h))
      = ((ψ : Domain3 → ℂ) ∘ fun v => v + h) := rfl
  rw [hcomp]
  -- LHS `𝓕 (ψ ∘ (·+h)) ξ` unfolds (rfl) to the VectorFourier integral
  have hL : 𝓕 ((ψ : Domain3 → ℂ) ∘ fun v => v + h) ξ
      = (VectorFourier.fourierIntegral Real.fourierChar (volume : Measure Domain3)
          (innerₗ Domain3) ((ψ : Domain3 → ℂ) ∘ fun v => v + h)) ξ := rfl
  have hR : 𝓕 (ψ : Domain3 → ℂ) ξ
      = (VectorFourier.fourierIntegral Real.fourierChar (volume : Measure Domain3)
          (innerₗ Domain3) (ψ : Domain3 → ℂ)) ξ := rfl
  rw [hL, hR, hmod]
  -- now: `𝐞 ((innerₗ V) h ξ) • (fourierIntegral … ψ) ξ = phaseFun h ξ * (fourierIntegral … ψ) ξ`
  simp only [Circle.smul_def]
  congr 1

/-- **F4.** Schwartz-level modulation identity: for a scalar Schwartz map `ψ : 𝓢(Domain3, ℂ)`,
the Fourier transform of the right-translated Schwartz map `ψ ∘ (· + h)` (carried to `Lp`)
equals the phase multiplier applied to `𝓕 (ψ.toLp 2)`:

  `𝓕 ((ψ.compTranslate h).toLp 2) = phaseMulCLM h (𝓕 (ψ.toLp 2))`,

where the left translate is `SchwartzMap.compCLMOfContinuousLinearEquiv`-style precomposition
with `(· + h)`.  Here we state it directly on the `Lp` translate of the representative, matching
the form consumed by F5's density base case.

Proof sketch: `fourier_coe` reduces both sides to the raw `VectorFourier.fourierIntegral`;
`VectorFourier.fourierIntegral_comp_add_right` (with `L = innerₗ Domain3`, `v₀ = h`) yields the
phase factor `𝐞 ⟪h, ·⟫ = phaseFun h`; conclude a.e. with `F3` and `SchwartzMap.toLp_fourier_eq`.
The convention bookkeeping (the `(2π)`, the sign, `innerₗ` vs `⟪·,·⟫`) is the substance. -/
theorem toLp_fourier_compMeasurePreserving_eq (h : Domain3) (ψ : SchwartzMap Domain3 ℂ) :
    𝓕 (Lp.compMeasurePreserving (· + h)
        (measurePreserving_add_right (volume : Measure Domain3) h) (ψ.toLp 2))
      = phaseMulCLM h (𝓕 (ψ.toLp 2)) := by
  rw [compMeasurePreserving_toLp_eq, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  refine Lp.ext ?_
  have hl := (𝓕 (schwartzTranslate h ψ)).coeFn_toLp 2 (volume : Measure Domain3)
  have hr := coeFn_phaseMulCLM h ((𝓕 ψ).toLp 2 (volume : Measure Domain3))
  have hr2 := (𝓕 ψ).coeFn_toLp 2 (volume : Measure Domain3)
  filter_upwards [hl, hr, hr2] with ξ hxl hxr hxr2
  rw [hxl, hxr, hxr2, fourier_schwartzTranslate_apply]

/-! ### F5 — Lp-level modulation (the crux) -/

/-- **F5.** Lp-level translation→modulation identity — *the missing piece* that retires the
`RellichBall.lean:181-193` blocker.  For any `f : L²(ℝ³; ℂ)`, the Fourier transform of the
L²-translate by `h` is the phase multiplier applied to `𝓕 f`:

  `𝓕 (Lp.compMeasurePreserving (· + h) … f) = phaseMulCLM h (𝓕 f)`.

Proof sketch: `DenseRange.induction_on` over `SchwartzMap.denseRange_toLpCLM` (the
Schwartz-dense engine).  The predicate is `isClosed_eq` of the two continuous maps
`f ↦ 𝓕 (compMeasurePreserving … f)` and `f ↦ phaseMulCLM h (𝓕 f)` (continuity of
`compMeasurePreserving`, `𝓕`, and `phaseMulCLM`).  The base case on Schwartz reps is F4.
Template: `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`. -/
theorem fourier_translate_eq (h : Domain3) (f : L2C_R3) :
    𝓕 (Lp.compMeasurePreserving (· + h)
        (measurePreserving_add_right (volume : Measure Domain3) h) f)
      = phaseMulCLM h (𝓕 f) := by
  -- the translation as a continuous (linear isometry) map on L²
  set T : L2C_R3 → L2C_R3 := fun g =>
    Lp.compMeasurePreserving (· + h)
      (measurePreserving_add_right (volume : Measure Domain3) h) g with hT
  -- `T` is continuous: it is the underlying map of `compMeasurePreservingₗᵢ`.
  have hTcont : Continuous T :=
    (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (· + h)
      (measurePreserving_add_right (volume : Measure Domain3) h)).continuous
  set pr : L2C_R3 → Prop := fun g => 𝓕 (T g) = phaseMulCLM h (𝓕 g) with hpr
  apply DenseRange.induction_on (p := pr)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · refine isClosed_eq ?_ ?_
    · exact continuous_fourier.comp hTcont
    · exact (phaseMulCLM h).continuous.comp continuous_fourier
  · intro ψ
    show 𝓕 (T (SchwartzMap.toLpCLM ℝ ℂ 2 volume ψ)) = phaseMulCLM h (𝓕 (SchwartzMap.toLpCLM ℝ ℂ 2 volume ψ))
    rw [SchwartzMap.toLpCLM_apply, hT]
    exact toLp_fourier_compMeasurePreserving_eq h ψ

/-! ### F6 — Fourier of a Schwartz-rep component is a.e. Schwartz -/

/-- **F6.** Generalization of `GalerkinODEExistence.galerkinSpan_fourier_ae`: if the complex
component `L2VF_projComponentC_R3 j u` has a Schwartz representative, then the pointwise
coercion of its L²-Fourier transform is a.e. equal to a genuine Schwartz `𝓕`.

This lifts the (private, span-specific) `galerkinSpan_fourier_ae` to a public, domain-general
hypothesis-form lemma reusable by both consumers.

Proof sketch: from the Schwartz rep `hφ : component = (φ).toLp 2`, rewrite and apply
`SchwartzMap.toLp_fourier_eq` then `coeFn_toLp` (exactly the `galerkinSpan_fourier_ae`
argument). -/
theorem fourierComponentC_ae_schwartz (j : Fin 3) (u : L2VF_R3)
    (φ : SchwartzMap Domain3 ℂ)
    (hφ : L2VF_projComponentC_R3 j u = φ.toLp 2 (volume : Measure Domain3)) :
    ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] ((𝓕 φ : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) := by
  have hF : (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3)
      = (𝓕 φ).toLp 2 (volume : Measure Domain3) := by
    rw [hφ]; exact SchwartzMap.toLp_fourier_eq φ
  rw [hF]
  exact (𝓕 φ).coeFn_toLp 2 (volume : Measure Domain3)

/-! ### F7 — Plancherel weight bookkeeping -/

/-- **F7.** Named exposure of the spectral definition of `viscousFormSq_R3` at `ν = 1`, so the
consumers cite a stable name rather than `unfold`ing:

  `viscousFormSq_R3 1 w = ∑ j, ∫ ξ, (2π)² ‖ξ‖² ‖(𝓕 (L2VF_projComponentC_R3 j w)) ξ‖² dξ`.

Proof sketch: `simp [viscousFormSq_R3, one_mul]` (definitional). -/
theorem viscousFormSq_R3_eq_integral_normSq_fourier (w : L2VF_R3) :
    viscousFormSq_R3 1 w
      = ∑ j : Fin 3, ∫ ξ : Domain3,
          (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
            ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2
          ∂(volume : Measure Domain3) := by
  rw [viscousFormSq_R3, one_mul]

/-! ### F8 — Plancherel core helper -/

/-- L²-norm-squared of a complex-scalar `L²` element as an integral of the pointwise squared
norm. -/
theorem normSq_eq_integral_normSq_C (g : L2C_R3) :
    ‖g‖ ^ 2 = ∫ ξ : Domain3, ‖(g : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  have hre : ‖g‖ ^ 2 = RCLike.re (inner ℂ g g) := norm_sq_eq_re_inner (𝕜 := ℂ) g
  rw [hre, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner g g)]
  refine integral_congr_ae ?_
  filter_upwards with ξ
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **F8.** Plancherel core helper: for a complex component `c : L2C_R3`, the squared L²-norm
of `𝓕 (τ_h c) − 𝓕 c` is the integral of `‖phaseFun h ξ − 1‖² ‖(𝓕 c) ξ‖²`:

  `‖𝓕 (Lp.compMeasurePreserving (· + h) … c) − 𝓕 c‖²
     = ∫ ξ, ‖phaseFun h ξ − 1‖² ‖(𝓕 c) ξ‖² dξ`.

Proof sketch: F5 rewrites `𝓕 (τ_h c) = phaseMulCLM h (𝓕 c)`; F3 gives the a.e. pointwise form
`(phaseFun h ξ − 1) * (𝓕 c) ξ`; `Lp.norm_sq` as an integral of the pointwise squared norm
(via `Lp.norm_def`/`eLpNorm` and `‖·‖²` integrand) closes it. -/
theorem normSq_sub_eq_integral_phase_sub (h : Domain3) (c : L2C_R3) :
    ‖𝓕 (Lp.compMeasurePreserving (· + h)
          (measurePreserving_add_right (volume : Measure Domain3) h) c) - 𝓕 c‖ ^ 2
      = ∫ ξ : Domain3,
          ‖phaseFun h ξ - 1‖ ^ 2 * ‖(𝓕 c : L2C_R3) ξ‖ ^ 2
        ∂(volume : Measure Domain3) := by
  set g : L2C_R3 := 𝓕 (Lp.compMeasurePreserving (· + h)
      (measurePreserving_add_right (volume : Measure Domain3) h) c) - 𝓕 c with hg
  rw [normSq_eq_integral_normSq_C g]
  -- pointwise a.e.: `g ξ = (phaseFun h ξ - 1) * (𝓕 c) ξ`
  have hcoe : (g : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (phaseFun h ξ - 1) * (𝓕 c : L2C_R3) ξ := by
    have hsub := Lp.coeFn_sub
      (𝓕 (Lp.compMeasurePreserving (· + h)
        (measurePreserving_add_right (volume : Measure Domain3) h) c)) (𝓕 c)
    have hF5 : 𝓕 (Lp.compMeasurePreserving (· + h)
        (measurePreserving_add_right (volume : Measure Domain3) h) c)
      = phaseMulCLM h (𝓕 c) := fourier_translate_eq h c
    have hmul := coeFn_phaseMulCLM h (𝓕 c)
    filter_upwards [hsub, hmul] with ξ hxsub hxmul
    rw [hg, hxsub, Pi.sub_apply, hF5, hxmul, sub_mul, one_mul]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with ξ hxξ
  rw [hxξ, norm_mul, mul_pow]

/-! ### F9 — pointwise phase estimate -/

/-- **F9.** Pointwise modulus estimate for the phase increment:

  `‖phaseFun h ξ − 1‖² ≤ (2π)² ‖h‖² ‖ξ‖²`.

The `(2π)²` factor matches the F7 spectral weight; the inequality direction is `≤` so that F8
integrates up to `‖h‖² · viscousFormSq_R3 1 w` (consumed by `RellichBall.lean`'s T0b).

Proof sketch: `phaseFun h ξ = 𝐞 ⟪h,ξ⟫ = exp(2π i ⟪h,ξ⟫)`; `|e^{iθ} − 1| ≤ |θ|` with
`θ = 2π ⟪h,ξ⟫` gives `‖phaseFun h ξ − 1‖ ≤ 2π |⟪h,ξ⟫|`; Cauchy–Schwarz
`|⟪h,ξ⟫| ≤ ‖h‖ ‖ξ‖` and squaring give the claim. -/
theorem normSq_phaseFun_sub_one_le (h : Domain3) (ξ : Domain3) :
    ‖phaseFun h ξ - 1‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖h‖ ^ 2 * ‖ξ‖ ^ 2 := by
  -- write `phaseFun h ξ = exp (I * (2π⟪h,ξ⟫ : ℝ))`
  set θ : ℝ := 2 * Real.pi * inner ℝ h ξ with hθ
  have hphase : phaseFun h ξ = Complex.exp (Complex.I * (θ : ℂ)) := by
    simp only [phaseFun, Real.fourierChar_apply, hθ]
    push_cast
    ring_nf
  -- `‖phaseFun h ξ − 1‖ ≤ ‖θ‖ = |θ|`
  have hbound : ‖phaseFun h ξ - 1‖ ≤ |θ| := by
    rw [hphase]
    exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq (Real.norm_eq_abs θ))
  -- square both sides
  have hsq : ‖phaseFun h ξ - 1‖ ^ 2 ≤ θ ^ 2 := by
    calc ‖phaseFun h ξ - 1‖ ^ 2 ≤ |θ| ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _) hbound
      _ = θ ^ 2 := sq_abs θ
  -- bound `θ² = (2π)² ⟪h,ξ⟫² ≤ (2π)² ‖h‖² ‖ξ‖²` via Cauchy–Schwarz
  refine hsq.trans ?_
  have hcs : |inner ℝ h ξ| ≤ ‖h‖ * ‖ξ‖ := abs_real_inner_le_norm h ξ
  have hcs2 : (inner ℝ h ξ : ℝ) ^ 2 ≤ ‖h‖ ^ 2 * ‖ξ‖ ^ 2 := by
    calc (inner ℝ h ξ : ℝ) ^ 2 = |inner ℝ h ξ| ^ 2 := (sq_abs _).symm
      _ ≤ (‖h‖ * ‖ξ‖) ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) hcs
      _ = ‖h‖ ^ 2 * ‖ξ‖ ^ 2 := by ring
  have : θ ^ 2 = (2 * Real.pi) ^ 2 * (inner ℝ h ξ : ℝ) ^ 2 := by rw [hθ]; ring
  rw [this]
  have hpi : (0:ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  calc (2 * Real.pi) ^ 2 * (inner ℝ h ξ : ℝ) ^ 2
      ≤ (2 * Real.pi) ^ 2 * (‖h‖ ^ 2 * ‖ξ‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left hcs2 hpi
    _ = (2 * Real.pi) ^ 2 * ‖h‖ ^ 2 * ‖ξ‖ ^ 2 := by ring

end FourierL2

end LerayHopf
