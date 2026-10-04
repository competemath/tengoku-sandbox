import Tengoku.LerayHopf.LerayHopf.R3.SpatialCompactness
import Tengoku.LerayHopf.LerayHopf.R3.FourierL2
import Tengoku.Seed.Analysis.Fourier.LpSpace
import Tengoku.Seed.MeasureTheory.Measure.Haar.Unique
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Indicator

namespace LerayHopf
open MeasureTheory Filter Topology Metric
open scoped FourierTransform

/-!
# LOCAL Rellich–Kondrachov on a ball, reduced to Fréchet–Kolmogorov (Pillar B)

**Milestone:** `rellich-balls`

This file supplies the analytic frontier formerly carried by the
`spatial_compactness_R3` axiom (via `LocalRellichInput.ballCompact`,
`SpatialCompactness.lean:94-99`).  As of PR #35
the FK chain is `sorry`-free, and `spatial_compactness_R3` is no longer an axiom — it is a
proved `theorem` assembled from this file's deliverable (see `SolutionInterfaces.lean`).
Concretely this file does two things:

1. the Navier–Stokes-specific bridge "global spectral gradient bound ⇒ uniform
   L²-translation modulus" — its PEELING/ASSEMBLY (T0c) is axiom-free, and the Plancherel
   core T0b it consumes is now fully proved; and
2. the **reduction** of `LocalRellichInput` to the *standard, domain-agnostic*
   Fréchet–Kolmogorov (Riesz) L²-precompactness criterion `FrechetKolmogorovInput` —
   fully assembled (T1b + T2), `sorry`-free; only `FrechetKolmogorovInput` is assumed
   (as an explicit hypothesis, not an axiom).

`FrechetKolmogorovInput` is the **global-representative** precompactness criterion: each
family member `f : L2ballR3 R` carries a global representative `rep f : L2VF_R3` with
`restrictToBall R (rep f) = f`, the family is uniformly L²-bounded both inside the ball
(`‖f‖ ≤ C`) and GLOBALLY on the representative (`‖rep f‖ ≤ C`, the standard Riesz full-mass
control), and the uniform modulus is the GLOBAL L²-translation modulus
`‖translate_L2VF h (rep f) − rep f‖`.  This is a legitimate, sound, non-smuggling criterion
(it mentions no Sobolev/gradient/`L2Sigma`/velocity object); it is INTENTIONALLY phrased on
the global representative.  The Navier–Stokes bridge content lives entirely in T0b/T0c (the
Plancherel gradient ⇒ global-translation-modulus estimate), NOT in any bespoke ball-modulus
plus a separate ball/global bridge lemma.  The deliverable feeds T0c's global modulus directly
into the criterion (with `rep := the admissible global field` and `hrep` from `restrictToBall`).

## Honest scope (no overclaim) — `sorry`-free FK chain

This file does **NOT** prove Rellich–Kondrachov in the abstract (that is the assumed
`FrechetKolmogorovInput`); it substantiates the FK reduction and the gradient ⇒ modulus
bridge, `sorry`-free.  The status of each piece, with no rounding up:

**PROVED (axiom-free; no `sorryAx` on their own statements):**
- T0a `translate_L2VF` — L² translation `τ_h w (x) = w (x − h)` (pure Lp plumbing).
- T0c `norm_translate_sub_le_of_viscousBound` — the gradient ⇒ uniform-modulus PEELING
  step (square-root + sign bookkeeping).  Its *body* is axiom-free; it consumes T0b's
  statement, which is now fully proved.
- T1b `admissible_family_uniform_bound` — the restricted family is uniformly `‖·‖ ≤ M`.

**ASSEMBLED (deliverable, fully wired, axiom-free assembly):**
- T2 `localRellichInput_of_frechetKolmogorov` — the conditional constructor.  Its
  assembly logic (build `rep`/`S`, feed T0c's modulus + T1b's bound into the FK
  criterion) is complete and `sorry`-free.

**PROVED (closed via the shared Fourier–L² foundation `FourierL2.lean`):**
- T0b `normSq_translate_sub_le_viscousFormSq` — the Plancherel translation-modulation
  estimate `‖τ_h w − w‖² ≤ ‖h‖²·viscousFormSq_R3 1 w`.  The Lp-level Fourier modulation
  identity that previously blocked it (`𝓕(τ_h f) = phase · 𝓕 f`) is supplied by
  `FourierL2` (F5), together with the Plancherel weight bookkeeping (F7), the Plancherel
  core (F8), and the pointwise phase estimate (F9).  The component decomposition (step (a))
  is `componentC_translate_ae` + the Euclidean norm decomposition.  The proof body is
  axiom-free, including the integrability input below.

**PROVED (the former frontier, now discharged):**
- `integrable_viscous_integrand_of_memH1` — the H¹ ⇒ concrete weighted-L²
  integrability of the L²-Fourier transform.  `memH1VF_R3 w` (= `MemSobolev 1 2` on each
  complex component) implies `Integrable (fun ξ ↦ (2π)²‖ξ‖²‖(𝓕 cⱼ) ξ‖²)`.  This is now
  fully proved here (via the self-contained Bessel-weight machinery and
  `memSobolev_iff_exists_smulLeftCLM_fourier`); it was previously the sole marked `sorry`
  in the file and is no longer.

**Isolated hypothesis (mathlib-absent, a hypothesis is not an axiom):**
- `FrechetKolmogorovInput` — the standard Fréchet–Kolmogorov (Riesz) L²-precompactness
  criterion that mathlib still lacks, carried as an explicit hypothesis structure exactly
  as P3's `LocalRellichInput` and R3-d's `hdiv`.

Net: this file substantiates the FK reduction + the gradient ⇒ modulus bridge `sorry`-free —
translation plumbing, the Plancherel core T0b, the modulus peeling, the uniform bound, and
the assembly into a `LocalRellichInput` are all proved here.

The deliverable is the conditional constructor
`localRellichInput_of_frechetKolmogorov : FrechetKolmogorovInput → LocalRellichInput`,
whose conclusion reproduces `LocalRellichInput` verbatim.  As of PR #35,
`spatial_compactness_R3` has been rewritten from `axiom` to a proved `theorem` (in
`SolutionInterfaces.lean`, assembled from this deliverable via the FK chain); the only
remaining gap on this path is discharging `FrechetKolmogorovInput` itself (a future mathlib
FK development), carried as an explicit hypothesis.

## Architecture (standalone sibling)

This file imports `R3.SpatialCompactness` (reusing `LocalRellichInput`, `L2ballR3`,
`restrictToBall`), but NOT `R3.SolutionInterfaces`.  Its `#print axioms` for the deliverable
stays clean of the NS axioms and is `sorryAx`-free — it carries NO
`sorry`/`axiom`/`opaque`/`constant`.

DAG position:
```
R3/Regularity.lean   (L2VF_R3, L2Sigma_R3, memH1VF_R3, viscousFormSq_R3, Domain3)
  └── R3/SpatialCompactness.lean   (L2ballR3, restrictToBall, LocalRellichInput) [P3]
        └── R3/RellichBall.lean    [THIS FILE; imports SpatialCompactness, NOT SolutionInterfaces]
```

## Declarations (dependency order)

- `translate_L2VF`                              : T0a — L² translation `τ_h w (x) = w (x − h)`
- `FrechetKolmogorovInput`                      : isolated frontier (abstract FK precompactness)
- `integrable_viscous_integrand_of_memH1`       : T0b integrability input [PROVED]
- `normSq_translate_sub_le_viscousFormSq`       : T0b — Plancherel translation-modulus core [PROVED via FourierL2 F5/F7/F8/F9]
- `norm_translate_sub_le_of_viscousBound`       : T0c — uniform modulus from the gradient bound
- `admissible_family_uniform_bound`             : T1b — uniform L²-bound of the restricted family
- `localRellichInput_of_frechetKolmogorov`      : T2 — DELIVERABLE (conditional `LocalRellichInput`)

## Assumptions

Zero new `axiom`/`opaque`/`constant`, and zero `sorry`.  One gap is carried, which is not an
axiom:

1. **Hypothesis** `FrechetKolmogorovInput` — the mathlib-absent Fréchet–Kolmogorov
   precompactness criterion, carried as an explicit hypothesis structure exactly as
   P3's `LocalRellichInput` and R3-d's `hdiv`.  A hypothesis is not an axiom.

The former marked `sorry` on `integrable_viscous_integrand_of_memH1` (the H¹ ⇒ concrete
weighted-L² integrability of the L²-Fourier transform) is now fully proved here via the
self-contained Bessel-weight machinery and `memSobolev_iff_exists_smulLeftCLM_fourier`; the
FK chain is `sorry`-free, so the deliverable carries no `sorryAx`.
-/

/-! ### Tier 0 — translation plumbing -/

/-- **T0a.** L² translation `τ_h w (x) = w (x − h)` of an L²(ℝ³) velocity field, as an element
of `L2VF_R3`.

Translation `(· + h)` is measure-preserving for the Lebesgue `volume`, so — unlike
`restrictToBall` — this goes through `Lp.compMeasurePreserving` with the translation map and
its `MeasurePreserving` proof (`measurePreserving_add_right`).  This is pure Lp plumbing: it
mentions no Sobolev/gradient/divergence object. -/
noncomputable def translate_L2VF (h : Domain3) (w : L2VF_R3) : L2VF_R3 :=
  Lp.compMeasurePreserving (· + h)
    (measurePreserving_add_right (volume : Measure Domain3) h) w

/-- Isolated analytic frontier: the **Fréchet–Kolmogorov (Riesz) L²-precompactness criterion**
on a fixed ball.

A family of `L²(B_R)` elements that (i) is uniformly L²-bounded and (ii) has a uniform
L²-translation modulus vanishing as the shift `h → 0` is contained in a compact set of
`L²(B_R)`.  This is the ONE thing mathlib still lacks (no Fréchet–Kolmogorov / Riesz
criterion, no Rellich).

**No-smuggle (Codex Gate 1).**  This structure is a pure statement about abstract L²
families and translation.  It mentions NONE of: `memH1VF_R3`, `viscousFormSq_R3`,
`L2Sigma_R3`, gradients/`∇`, the word Sobolev, the velocity sequence, a subsequence, or a
limit.  The translation modulus is phrased via the global-field translation
`translate_L2VF` (pure Lp plumbing, NS-agnostic) of an explicitly supplied global
representative `rep f` of each family member: the family element `f : L2ballR3 R` is the
ball-restriction of `rep f : L2VF_R3` (hypothesis `hrep`), and the modulus is the GLOBAL
L²-norm `‖translate_L2VF h (rep f) − rep f‖` (NOT an in-ball translation, which would run
off the domain — see G-MOD).  This is strictly SMALLER than `LocalRellichInput.ballCompact`:
it is the abstract compactness *criterion*, not the H¹↪↪L² embedding.

The implication direction (modulus ⇒ precompact) is exactly the content mathlib lacks; the
modulus *hypothesis* itself is supplied downstream from the gradient bound (T0c) — whose
peeling is axiom-free and consumes the now-proved Plancherel core T0b.

**Global mass bound `bddGlobal` (Codex Gate round 3 fix).**  Beyond the single-radius ball
mass bound `∀ f ∈ S, ‖f‖ ≤ C` (= `‖restrictToBall R (rep f)‖`), the criterion ALSO demands a
uniform GLOBAL L²-norm bound on the representatives, `∀ f ∈ S, ‖rep f‖ ≤ C`.  This is the
honest, standard form of Fréchet–Kolmogorov (the classical Riesz criterion controls the FULL
L²-mass, not just the mass inside one fixed ball): single-ball mass + a translation modulus do
NOT control the mass on an annulus `B_{R+r} ∖ B_R`, so the mollifier helpers' enlarged-ball
bound (kernel reach) is NOT recoverable from the single-ball datum alone.  A plain global
L²-norm bound makes any enlarged-ball bound `‖restrictToBall R' (rep f)‖ ≤ C` (for ANY radius
`R'`) immediate by monotonicity of ball mass.  This is STILL a genuine FK criterion: it is a
plain L²-norm bound only — it mentions NO Sobolev/gradient/`viscousFormSq`/`L2Sigma`/subsequence/
limit object, smuggling none of the Rellich conclusion.  Making the hypothesis stronger (more
to supply) is sound: the actual Navier–Stokes admissible family is GLOBALLY `‖w‖ ≤ M` bounded,
so the call site `localRellichInput_of_frechetKolmogorov` can supply it. -/
structure FrechetKolmogorovInput where
  precompact_of_uniform_modulus :
    ∀ (R C : ℝ) (S : Set (L2ballR3 R))
      (rep : L2ballR3 R → L2VF_R3)
      -- interface condition kept in the contract: `rep` is a section of `restrictToBall`
      (_hrep : ∀ f ∈ S, restrictToBall R (rep f) = f),
    (∀ f ∈ S, ‖f‖ ≤ C) →
    (∀ f ∈ S, ‖rep f‖ ≤ C) →
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
        ‖translate_L2VF h (rep f) - rep f‖ < ε) →
    ∃ K : Set (L2ballR3 R), IsCompact K ∧ S ⊆ K

-- `normSq_eq_integral_normSq_VF` (was a private copy of `SpatialCompactness`'s
-- `normSq_eq_integral_normSq`, now public, issue #111 PR-3) is gone; its one call site
-- below uses the shared version directly.

/-- The complex `j`-component of the L²-translate equals the L²-translate of the complex
`j`-component, a.e.:
`(L2VF_projComponentC_R3 j (translate_L2VF h w)) ξ = (compMeasurePreserving (·+h) cⱼ) ξ`. -/
private theorem componentC_translate_ae (h : Domain3) (w : L2VF_R3) (j : Fin 3) :
    ((L2VF_projComponentC_R3 j (translate_L2VF h w) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] (Lp.compMeasurePreserving (· + h)
          (measurePreserving_add_right (volume : Measure Domain3) h)
          (L2VF_projComponentC_R3 j w) : L2C_R3) := by
  -- LHS a.e. = `((translate_L2VF h w) ξ) j` (componentC of an element)
  have hL : ((L2VF_projComponentC_R3 j (translate_L2VF h w) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (((translate_L2VF h w : L2VF_R3) ξ) j : ℂ) := by
    have h1 := (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL
      (L2VF_projComponent_R3 j (translate_L2VF h w))
    have h2 := (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (translate_L2VF h w)
    filter_upwards [h1, h2] with ξ hx1 hx2
    simp only [L2VF_projComponentC_R3, ContinuousLinearMap.compLpL,
      ContinuousLinearMap.coe_comp, Function.comp_apply] at hx1 ⊢
    rw [hx1]
    simp only [L2VF_projComponent_R3] at hx2 ⊢
    rw [hx2, RCLike.ofRealCLM_apply]
    rfl
  -- RHS a.e. = `(cⱼ (ξ+h))` = `((w (ξ+h)) j : ℂ)`
  have hR : (Lp.compMeasurePreserving (· + h)
        (measurePreserving_add_right (volume : Measure Domain3) h)
        (L2VF_projComponentC_R3 j w) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (((w : L2VF_R3) (ξ + h)) j : ℂ) := by
    have h1 := Lp.coeFn_compMeasurePreserving (L2VF_projComponentC_R3 j w)
      (measurePreserving_add_right (volume : Measure Domain3) h)
    have h2 : ((L2VF_projComponentC_R3 j w : L2C_R3) : Domain3 → ℂ)
        =ᵐ[volume] fun ξ => (((w : L2VF_R3) ξ) j : ℂ) := by
      have k1 := (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (L2VF_projComponent_R3 j w)
      have k2 := (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL w
      filter_upwards [k1, k2] with ξ hk1 hk2
      simp only [L2VF_projComponentC_R3, ContinuousLinearMap.compLpL,
        ContinuousLinearMap.coe_comp, Function.comp_apply] at hk1 ⊢
      rw [hk1]
      simp only [L2VF_projComponent_R3] at hk2 ⊢
      rw [hk2, RCLike.ofRealCLM_apply]
      rfl
    have h2' : (fun ξ => ((L2VF_projComponentC_R3 j w : L2C_R3) : Domain3 → ℂ) (ξ + h))
        =ᵐ[volume] fun ξ => (((w : L2VF_R3) (ξ + h)) j : ℂ) :=
      (measurePreserving_add_right (volume : Measure Domain3) h).quasiMeasurePreserving.ae_eq_comp h2
    filter_upwards [h1, h2'] with ξ hx1 hx2
    rw [hx1, Function.comp_apply]
    exact hx2
  -- combine, after expanding the LHS translate's coeFn
  have hL2 : (fun ξ => (((translate_L2VF h w : L2VF_R3) ξ) j : ℂ))
      =ᵐ[volume] fun ξ => (((w : L2VF_R3) (ξ + h)) j : ℂ) := by
    have ht := Lp.coeFn_compMeasurePreserving w
      (measurePreserving_add_right (volume : Measure Domain3) h)
    -- `translate_L2VF h w = compMeasurePreserving (·+h) w`
    filter_upwards [ht] with ξ hxt
    simp only [translate_L2VF]
    rw [hxt, Function.comp_apply]
  exact hL.trans (hL2.trans hR.symm)

/-! ### Local Bessel-weight helpers for the T0b integrability input

The H¹ ⇒ weighted-L² integrability technique below is self-contained in `RellichBall`, using
only `FourierL2`'s imports (`Mathlib.Analysis.Fourier.LpSpace` +
`Mathlib.Analysis.Distribution.Sobolev`, transitively) — `FrechetKolmogorov.lean` IMPORTS this
file, so a helper defined there could never have been reused here (it would be circular); a
now-deleted copy of this same machinery once lived in `FrechetKolmogorov.lean` for that reason
(issue #113 PR-2 removed it as dead code, since it never had any callers). These `private`
declarations support exactly one lemma, `integrable_viscous_integrand_of_memH1`. -/

/-- The Bessel weight `ξ ↦ ((1 + ‖ξ‖²)^(1/2) : ℝ) : ℂ` of order `s = 1` (`s/2 = 1/2`), the
multiplier appearing in `memSobolev_iff_exists_smulLeftCLM_fourier` for `MemSobolev 1 2`. -/
private noncomputable def besselWeightC_R : Domain3 → ℂ :=
  fun ξ => (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

/-- The Bessel weight is real-valued and nonnegative, with squared modulus `1 + ‖ξ‖²`. -/
private theorem normSq_besselWeightC_R (ξ : Domain3) :
    ‖besselWeightC_R ξ‖ ^ 2 = 1 + ‖ξ‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  rw [besselWeightC_R, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hnn _),
    ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hnn]
  norm_num

/-- The Bessel weight has temperate growth (`= ofReal ∘ (1+‖·‖²)^(1/2)`). -/
private theorem hasTemperateGrowth_besselWeightC_R :
    Function.HasTemperateGrowth besselWeightC_R := by
  have hr : Function.HasTemperateGrowth (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow Domain3 ((1 : ℝ) / 2)
  exact (Complex.ofRealCLM.hasTemperateGrowth).comp hr

/-- The Bessel weight is continuous. -/
private theorem continuous_besselWeightC_R : Continuous besselWeightC_R :=
  hasTemperateGrowth_besselWeightC_R.1.continuous

/-- The pointwise product `ξ ↦ besselWeightC_R ξ • g ξ` (unbounded multiplier) is locally
integrable: on each ball the continuous weight is bounded and `g ∈ L²` is integrable. -/
private theorem locallyIntegrable_besselWeight_smul_R (g : L2C_R3) :
    LocallyIntegrable (fun ξ : Domain3 => besselWeightC_R ξ • (g : Domain3 → ℂ) ξ)
      (volume : Measure Domain3) := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hK : IsCompact (Metric.closedBall x 1) := isCompact_closedBall x 1
  have hg_int : IntegrableOn (g : Domain3 → ℂ) (Metric.closedBall x 1) volume :=
    ((Lp.memLp g).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_besselWeightC_R.continuousOn (s := Metric.closedBall x 1))
  have hmul : IntegrableOn (fun ξ => besselWeightC_R ξ * (g : Domain3 → ℂ) ξ)
      (Metric.closedBall x 1) volume := by
    refine hg_int.bdd_mul (c := C) ?_ ?_
    · exact (continuous_besselWeightC_R.aestronglyMeasurable).restrict
    · refine ae_restrict_of_forall_mem measurableSet_closedBall (fun y hy => ?_)
      exact hC y hy
  simpa only [smul_eq_mul] using hmul

/-- **Local H¹ ⇒ Bessel-weighted-L² integrability**, self-contained here since a helper defined
in the downstream `FrechetKolmogorov.lean` could never be imported back into this (upstream)
file.  For `w ∈ H¹(ℝ³)`, the L²-Fourier transform `𝓕 cⱼ` is square-integrable against the
genuine `H¹` weight `1 + ‖ξ‖²`. -/
private theorem memH1_weightedL2_integrable_R (w : L2VF_R3) (hw : memH1VF_R3 w) (j : Fin 3) :
    Integrable (fun ξ : Domain3 =>
        (1 + ‖ξ‖ ^ 2) * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2)
      (volume : Measure Domain3) := by
  classical
  set cF : L2C_R3 := 𝓕 (L2VF_projComponentC_R3 j w) with hcF
  have hsob : TemperedDistribution.MemSobolev (1 : ℝ) 2
      (L2VF_projComponentC_R3 j w : TemperedDistribution Domain3 ℂ) := hw j
  obtain ⟨f', hf'⟩ :=
    TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mp hsob
  have hbridge : (𝓕 (L2VF_projComponentC_R3 j w : TemperedDistribution Domain3 ℂ))
      = (cF : TemperedDistribution Domain3 ℂ) := by
    rw [hcF]; exact (MeasureTheory.Lp.fourier_toTemperedDistribution_eq _)
  rw [hbridge] at hf'
  have hweq : (fun x : Domain3 => (((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) = besselWeightC_R :=
    rfl
  rw [hweq] at hf'
  have hlhs_li : LocallyIntegrable
      (fun ξ : Domain3 => besselWeightC_R ξ • (cF : Domain3 → ℂ) ξ)
      (volume : Measure Domain3) := locallyIntegrable_besselWeight_smul_R cF
  have hrhs_li : LocallyIntegrable (f' : Domain3 → ℂ) (volume : Measure Domain3) :=
    (Lp.memLp f').locallyIntegrable (by norm_num)
  have hae : (fun ξ : Domain3 => besselWeightC_R ξ • (cF : Domain3 → ℂ) ξ)
      =ᵐ[volume] (f' : Domain3 → ℂ) := by
    refine ae_eq_of_integral_contDiff_smul_eq hlhs_li hrhs_li ?_
    intro g g_smooth g_cpt
    have hg_supp : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg_diff := Complex.ofRealCLM.contDiff.comp g_smooth
    set φ : SchwartzMap Domain3 ℂ := hg_supp.toSchwartzMap hg_diff with hφ
    have hφ_coe : (φ : Domain3 → ℂ) = fun x => ((g x : ℝ) : ℂ) := rfl
    have hpair : TemperedDistribution.smulLeftCLM ℂ besselWeightC_R
          (cF : TemperedDistribution Domain3 ℂ) φ
        = ((f' : TemperedDistribution Domain3 ℂ) φ) := by rw [hf']
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
    rw [show (fun x => (g x : ℝ) • (besselWeightC_R x • (cF : Domain3 → ℂ) x))
          = fun x => ((SchwartzMap.smulLeftCLM ℂ besselWeightC_R φ) x)
              • (cF : Domain3 → ℂ) x from ?_,
        show (fun x => (g x : ℝ) • (f' : Domain3 → ℂ) x)
          = fun x => (φ x) • (f' : Domain3 → ℂ) x from ?_]
    · exact hpair
    · funext x
      show (g x : ℝ) • (f' : Domain3 → ℂ) x = (φ x) • (f' : Domain3 → ℂ) x
      rw [hφ_coe]
      simp only [Complex.real_smul, smul_eq_mul]
    · funext x
      show (g x : ℝ) • (besselWeightC_R x • (cF : Domain3 → ℂ) x)
          = ((SchwartzMap.smulLeftCLM ℂ besselWeightC_R φ) x) • (cF : Domain3 → ℂ) x
      rw [SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_besselWeightC_R, hφ_coe]
      simp only [Complex.real_smul, smul_eq_mul]
      ring
  have hf'_sq : Integrable (fun ξ : Domain3 => ‖(f' : Domain3 → ℂ) ξ‖ ^ 2)
      (volume : Measure Domain3) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f')).mp (Lp.memLp f')
  refine hf'_sq.congr ?_
  filter_upwards [hae] with ξ hξ
  rw [← hξ, norm_smul, mul_pow, normSq_besselWeightC_R]

/-- **T0b integrability input.** For `w ∈ H¹(ℝ³)`, the spectral viscous integrand
`(2π)² ‖ξ‖² ‖(𝓕 cⱼ) ξ‖²` (with `cⱼ = L2VF_projComponentC_R3 j w`) is Lebesgue-integrable.

This is the ONE genuinely missing analytic fact: it is the statement that the H¹-membership
`memH1VF_R3 w` (defined as `TemperedDistribution.MemSobolev 1 2` on each complex component)
implies the *concrete* weighted-L² integrability `∫ (1+‖ξ‖²) ‖(𝓕 cⱼ) ξ‖² < ∞` of the
**L²-Fourier transform** `𝓕 cⱼ = Lp.fourierTransformₗᵢ cⱼ`.

**OPEN — isolated frontier (see TODO):** `MemSobolev 1 2 (cⱼ : 𝓢')` unfolds to
`∃ f' : Lp ℂ 2, besselPotential E ℂ 1 (cⱼ : 𝓢') = f'`, equivalently (mathlib
`memSobolev_iff_exists_smulLeftCLM_fourier`) `∃ f', smulLeftCLM (fun ξ ↦ (1+‖ξ‖²)^(1/2)) (𝓕 (cⱼ : 𝓢')) = f'`.
To turn this into the concrete integrability one must (i) bridge `𝓕 (cⱼ : 𝓢')` to the
L²-Fourier `(𝓕 cⱼ : Lp)` via `Lp.fourier_toTemperedDistribution_eq`, and (ii) extract the
a.e. pointwise identity `(1+‖ξ‖²)^(1/2) · (𝓕 cⱼ) ξ = f' ξ` from
`smulLeftCLM weight ((𝓕 cⱼ : Lp) : 𝓢') = (f' : 𝓢')`.  Step (ii) needs an a.e. characterization
of `smulLeftCLM` applied to an `Lp`-coerced distribution for an **unbounded** multiplier
`weight = (1+‖ξ‖²)^(1/2)`; mathlib's `Lp.toTemperedDistribution_smul_eq` only covers
`MemLp`-bounded multipliers (and `weight ∉ Lᵖ`), so this a.e.-extraction-for-unbounded-weights
is the missing piece.  Once it lands, `‖ξ‖² ≤ 1 + ‖ξ‖²` gives the claim by domination.
Everything else in T0b is fully proved and consumes only this lemma. -/
theorem integrable_viscous_integrand_of_memH1 (w : L2VF_R3) (hw : memH1VF_R3 w)
    (j : Fin 3) :
    Integrable (fun ξ : Domain3 =>
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2)
      (volume : Measure Domain3) := by
  -- The Bessel-weighted integrand `(1+‖ξ‖²)·‖𝓕 cⱼ ξ‖²` is integrable (H¹ ⇒ weighted L²).
  have hbessel := memH1_weightedL2_integrable_R w hw j
  -- The `(2π)²‖ξ‖²`-weighted integrand is dominated by `(2π)²` times the Bessel one, since
  -- `‖ξ‖² ≤ 1 + ‖ξ‖²`.  Both are nonnegative, so `Integrable.mono'` transfers integrability.
  refine Integrable.mono' (g := fun ξ : Domain3 =>
      (2 * Real.pi) ^ 2 * ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2))
    (hbessel.const_mul ((2 * Real.pi) ^ 2)) ?_ ?_
  · -- the dominated integrand is (a.e. strongly) measurable
    refine (Continuous.aestronglyMeasurable ?_).mul ?_
    · exact (continuous_const.mul (continuous_norm.pow 2))
    · exact ((Lp.aestronglyMeasurable (𝓕 (L2VF_projComponentC_R3 j w))).norm.pow 2)
  · -- pointwise domination ‖·‖ ≤ dominating function
    filter_upwards with ξ
    have hnn : (0 : ℝ) ≤ ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2 := by positivity
    have hle : ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by linarith [sq_nonneg ‖ξ‖]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2
        = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2) := by
          ring
      _ ≤ (2 * Real.pi) ^ 2
            * ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hle hnn

/-- **T0b.** L²-translation modulus controlled by the spectral gradient form (Plancherel):
`‖τ_h w − w‖²_{L²(ℝ³)} ≤ ‖h‖² · viscousFormSq_R3 1 w`.

This is the Navier–Stokes-specific core, now CLOSED via the shared Fourier–L² foundation
(`FourierL2.lean`, F5/F7/F8/F9).  The proof: (a) decompose the ℝ³-valued L²-norm into the
sum over the three complex components `cⱼ = L2VF_projComponentC_R3 j w`
(`componentC_translate_ae` + the Euclidean norm decomposition); (b) Plancherel
`‖τ_h^C cⱼ − cⱼ‖ = ‖𝓕(τ_h^C cⱼ) − 𝓕 cⱼ‖` (`Lp.norm_fourier_eq`); (c) the Fourier-modulation
Plancherel core `FourierL2.normSq_sub_eq_integral_phase_sub` (F8); (d) the pointwise phase
estimate `FourierL2.normSq_phaseFun_sub_one_le` (F9) integrated up to recognize
`FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier` (F7).

Everything downstream (T0c, T1b, T2/deliverable) consumes ONLY this statement, so closing it
discharges the whole pillar modulo the `FrechetKolmogorovInput` hypothesis. -/
theorem normSq_translate_sub_le_viscousFormSq (h : Domain3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    ‖translate_L2VF h w - w‖ ^ 2 ≤ ‖h‖ ^ 2 * viscousFormSq_R3 1 w := by
  classical
  -- abbreviations for the three complex components and their L²-translates
  set c : Fin 3 → L2C_R3 := fun j => L2VF_projComponentC_R3 j w with hc
  set τc : Fin 3 → L2C_R3 := fun j =>
    Lp.compMeasurePreserving (· + h)
      (measurePreserving_add_right (volume : Measure Domain3) h) (c j) with hτc
  -- (a) `‖translate_L2VF h w − w‖² = ∑_j ‖τc j − c j‖²`
  have hstepa : ‖translate_L2VF h w - w‖ ^ 2 = ∑ j : Fin 3, ‖τc j - c j‖ ^ 2 := by
    -- ℝ³-valued L² norm as integral of pointwise squared norm
    rw [normSq_eq_integral_normSq (translate_L2VF h w - w)]
    -- pointwise: `‖(D ξ)‖²_{ℝ³} = ∑_j ‖(τc j − c j) ξ‖²`
    have hpt : (fun ξ : Domain3 =>
          ‖((translate_L2VF h w - w) ξ : EuclideanSpace ℝ (Fin 3))‖ ^ 2)
        =ᵐ[volume] fun ξ => ∑ j : Fin 3, ‖((τc j - c j : L2C_R3) : Domain3 → ℂ) ξ‖ ^ 2 := by
      have hsub := Lp.coeFn_sub (translate_L2VF h w) w
      have hcomp : ∀ j : Fin 3,
          ((τc j - c j : L2C_R3) : Domain3 → ℂ)
            =ᵐ[volume] fun ξ => (((translate_L2VF h w - w : L2VF_R3) ξ) j : ℂ) := by
        intro j
        have ha := componentC_translate_ae h w j
        have hbsub := Lp.coeFn_sub (τc j) (c j)
        have hcj : ((c j : L2C_R3) : Domain3 → ℂ)
            =ᵐ[volume] fun ξ => (((w : L2VF_R3) ξ) j : ℂ) := by
          have k1 := (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (L2VF_projComponent_R3 j w)
          have k2 := (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL w
          filter_upwards [k1, k2] with ξ hk1 hk2
          simp only [hc, L2VF_projComponentC_R3, ContinuousLinearMap.compLpL,
            ContinuousLinearMap.coe_comp, Function.comp_apply] at hk1 ⊢
          rw [hk1]
          simp only [L2VF_projComponent_R3] at hk2 ⊢
          rw [hk2, RCLike.ofRealCLM_apply]
          rfl
        -- `τc j` a.e. = componentC of translate (by `componentC_translate_ae`, reversed)
        have hτcj : ((τc j : L2C_R3) : Domain3 → ℂ)
            =ᵐ[volume] fun ξ => (((translate_L2VF h w : L2VF_R3) ξ) j : ℂ) := by
          have hLcomp : ((L2VF_projComponentC_R3 j (translate_L2VF h w) : L2C_R3) : Domain3 → ℂ)
              =ᵐ[volume] fun ξ => (((translate_L2VF h w : L2VF_R3) ξ) j : ℂ) := by
            have k1 := (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL
              (L2VF_projComponent_R3 j (translate_L2VF h w))
            have k2 := (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (translate_L2VF h w)
            filter_upwards [k1, k2] with ξ hk1 hk2
            simp only [L2VF_projComponentC_R3, ContinuousLinearMap.compLpL,
              ContinuousLinearMap.coe_comp, Function.comp_apply] at hk1 ⊢
            rw [hk1]
            simp only [L2VF_projComponent_R3] at hk2 ⊢
            rw [hk2, RCLike.ofRealCLM_apply]
            rfl
          exact (ha.symm.trans hLcomp)
        filter_upwards [hbsub, hτcj, hcj, hsub] with ξ hxb hxτ hxc hxs
        rw [hxb, Pi.sub_apply, hxτ, hxc, hxs, Pi.sub_apply]
        rw [PiLp.sub_apply]
        push_cast
        ring
      -- combine pointwise
      filter_upwards [hsub, hcomp 0, hcomp 1, hcomp 2] with ξ hxs hx0 hx1 hx2
      rw [EuclideanSpace.norm_sq_eq]
      rw [Fin.sum_univ_three, Fin.sum_univ_three, hx0, hx1, hx2]
      simp only [Complex.norm_real]
    rw [integral_congr_ae hpt]
    -- swap sum and integral; each summand integral = ‖τc j − c j‖²
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← FourierL2.normSq_eq_integral_normSq_C (τc j - c j)]
    · intro j _
      exact (memLp_two_iff_integrable_sq_norm
        (Lp.aestronglyMeasurable (τc j - c j))).mp (Lp.memLp (τc j - c j))
  rw [hstepa]
  -- (b)+(c)+(d): bound each summand
  have hbound : ∀ j : Fin 3, ‖τc j - c j‖ ^ 2
      ≤ ‖h‖ ^ 2 * ∫ ξ : Domain3,
          (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2
          ∂(volume : Measure Domain3) := by
    intro j
    -- (b) Plancherel
    have hb : ‖τc j - c j‖ ^ 2 = ‖𝓕 (τc j) - 𝓕 (c j)‖ ^ 2 := by
      have hfs : 𝓕 (τc j - c j) = 𝓕 (τc j) - 𝓕 (c j) :=
        (Lp.fourierTransformₗᵢ Domain3 ℂ).map_sub (τc j) (c j)
      rw [← hfs, Lp.norm_fourier_eq]
    -- (c) F8
    rw [hb, FourierL2.normSq_sub_eq_integral_phase_sub]
    -- (d) F9 pointwise + integrate
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with ξ
      positivity
    · -- integrability of the dominating function (the isolated frontier; see lemma above)
      have hint : Integrable (fun ξ : Domain3 =>
          (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2)
          (volume : Measure Domain3) :=
        integrable_viscous_integrand_of_memH1 w hw j
      exact hint.const_mul (‖h‖ ^ 2)
    · filter_upwards with ξ
      have hF9 := FourierL2.normSq_phaseFun_sub_one_le h ξ
      have hnn : (0:ℝ) ≤ ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2 := by positivity
      calc ‖FourierL2.phaseFun h ξ - 1‖ ^ 2 * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2
          ≤ ((2 * Real.pi) ^ 2 * ‖h‖ ^ 2 * ‖ξ‖ ^ 2) * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hF9 hnn
        _ = ‖h‖ ^ 2 * ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2) := by ring
  calc ∑ j : Fin 3, ‖τc j - c j‖ ^ 2
      ≤ ∑ j : Fin 3, ‖h‖ ^ 2 * ∫ ξ : Domain3,
          (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2
          ∂(volume : Measure Domain3) := Finset.sum_le_sum (fun j _ => hbound j)
    _ = ‖h‖ ^ 2 * ∑ j : Fin 3, ∫ ξ : Domain3,
          (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (c j) : L2C_R3) ξ‖ ^ 2
          ∂(volume : Measure Domain3) := by rw [Finset.mul_sum]
    _ = ‖h‖ ^ 2 * viscousFormSq_R3 1 w := by
        rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]

/-- **T0c.** Uniform translation modulus for the admissible family: from `0 ≤ M` and
`viscousFormSq_R3 1 w ≤ M²`, `‖τ_h w − w‖ ≤ ‖h‖·M`.  Supplies the modulus hypothesis of
`FrechetKolmogorovInput`.

The sign hypothesis `hM : 0 ≤ M` is REQUIRED: the squared bound `viscousFormSq_R3 1 w ≤ M²`
alone does not control the sign of `M` (e.g. `M = -1`, `w = 0` would give the false
`0 ≤ -‖h‖`).  Taking square roots of the T0b estimate only yields `‖h‖·|M|`; the conclusion
`‖h‖·M` is correct precisely when `M ≥ 0`.  Downstream (`localRellichInput_of_frechetKolmogorov`)
`0 ≤ M` is discharged from `‖w‖ ≤ M` on any admissible witness. -/
theorem norm_translate_sub_le_of_viscousBound (M : ℝ) (h : Domain3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) (hM : 0 ≤ M) (hvf : viscousFormSq_R3 1 w ≤ M ^ 2) :
    ‖translate_L2VF h w - w‖ ≤ ‖h‖ * M := by
  have hsq : ‖translate_L2VF h w - w‖ ^ 2 ≤ (‖h‖ * M) ^ 2 := by
    refine le_trans (normSq_translate_sub_le_viscousFormSq h w hw) ?_
    have : ‖h‖ ^ 2 * viscousFormSq_R3 1 w ≤ ‖h‖ ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hvf (by positivity)
    calc ‖h‖ ^ 2 * viscousFormSq_R3 1 w ≤ ‖h‖ ^ 2 * M ^ 2 := this
      _ = (‖h‖ * M) ^ 2 := by ring
  have hrhs : 0 ≤ ‖h‖ * M := mul_nonneg (norm_nonneg _) hM
  nlinarith [norm_nonneg (translate_L2VF h w - w), hsq, hrhs]

/-! ### Tier 1 — assemble the modulus into the FK-criterion input -/

/-- **T1b.** The restricted admissible family `S_{M,R} := {restrictToBall R w | w admissible}`
is uniformly `‖·‖ ≤ M`: each restriction does not increase the norm and `‖w‖ ≤ M`. -/
theorem admissible_family_uniform_bound (M R : ℝ) (w : L2VF_R3) (hbd : ‖w‖ ≤ M) :
    ‖restrictToBall R w‖ ≤ M :=
  -- `norm_restrictToBall_le` is public in `SpatialCompactness` (issue #111 PR-3).
  le_trans (norm_restrictToBall_le R w) hbd

/-! ### Tier 2 — DELIVERABLE -/

/-- **T2 (DELIVERABLE).  LOCAL Rellich input on ℝ³, from the abstract Fréchet–Kolmogorov
criterion.**

Constructs a `LocalRellichInput` (per-ball precompactness of the H¹-bounded div-free family)
from `FrechetKolmogorovInput`.  The Navier–Stokes-specific content (gradient bound ⇒ uniform
translation modulus, via Plancherel on `viscousFormSq_R3`) is ASSEMBLED axiom-free here, and
its Plancherel core T0b is fully proved, so this deliverable is `sorry`-free; only the
domain-agnostic FK precompactness criterion is assumed as a hypothesis.  The conclusion
reproduces `LocalRellichInput` verbatim (no weakening; Hard rule 3). -/
theorem localRellichInput_of_frechetKolmogorov (FK : FrechetKolmogorovInput) :
    LocalRellichInput := by
  classical
  refine ⟨fun M R => ?_⟩
  -- Admissibility predicate for the global field.
  set adm : L2VF_R3 → Prop :=
    fun w => w ∈ L2Sigma_R3 ∧ memH1VF_R3 w ∧ ‖w‖ ≤ M ∧ viscousFormSq_R3 1 w ≤ M ^ 2 with hadm
  -- The restricted admissible family in `L2ballR3 R`.
  set S : Set (L2ballR3 R) :=
    {f | ∃ w : L2VF_R3, adm w ∧ restrictToBall R w = f} with hS
  -- Global representative: for `f ∈ S`, choose an admissible witness; otherwise arbitrary.
  have hex : ∀ f ∈ S, ∃ w : L2VF_R3, adm w ∧ restrictToBall R w = f := fun f hf => hf
  let rep : L2ballR3 R → L2VF_R3 := fun f =>
    if hf : f ∈ S then (hex f hf).choose else 0
  -- `rep f` is admissible and restricts back to `f`, for `f ∈ S`.
  have hrep_adm : ∀ f ∈ S, adm (rep f) := by
    intro f hf
    simp only [rep, dite_eq_left hf]
    exact (hex f hf).choose_spec.1
  have hrep : ∀ f ∈ S, restrictToBall R (rep f) = f := by
    intro f hf
    simp only [rep, dite_eq_left hf]
    exact (hex f hf).choose_spec.2
  -- Uniform L²-bound C := M on the family (T1b).
  have hbound : ∀ f ∈ S, ‖f‖ ≤ M := by
    intro f hf
    obtain ⟨w, hw, rfl⟩ := hf
    exact admissible_family_uniform_bound M R w hw.2.2.1
  -- Uniform GLOBAL L²-bound C := M on the representatives (the new `bddGlobal` slot).
  -- The admissible family is globally `‖w‖ ≤ M` (admissibility), and `rep f` is admissible.
  have hboundGlobal : ∀ f ∈ S, ‖rep f‖ ≤ M := by
    intro f hf
    exact (hrep_adm f hf).2.2.1
  -- Uniform global translation modulus (T0c), the slot FK consumes.
  have hmod : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
      ‖translate_L2VF h (rep f) - rep f‖ < ε := by
    intro ε hε
    -- Use `max M 0 + 1 > 0` as denominator so `δ > 0` holds unconditionally; on a nonempty
    -- family `M ≥ 0`, so `max M 0 = M`.
    have hden : (0 : ℝ) < max M 0 + 1 := by positivity
    refine ⟨ε / (max M 0 + 1), by positivity, ?_⟩
    intro f hf h hh
    -- `rep f` is admissible: gives `0 ≤ M`, `memH1VF_R3`, and the viscous bound.
    obtain ⟨hmemf, hH1f, hnormf, hvff⟩ := hrep_adm f hf
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hnormf
    have hmaxM : max M 0 = M := max_eq_left hMnn
    -- T0c: `‖τ_h (rep f) − rep f‖ ≤ ‖h‖·M`.
    have hT0c : ‖translate_L2VF h (rep f) - rep f‖ ≤ ‖h‖ * M :=
      norm_translate_sub_le_of_viscousBound M h (rep f) hH1f hMnn hvff
    calc ‖translate_L2VF h (rep f) - rep f‖ ≤ ‖h‖ * M := hT0c
      _ ≤ ‖h‖ * (max M 0 + 1) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            rw [hmaxM]; linarith
      _ < (ε / (max M 0 + 1)) * (max M 0 + 1) := by
            apply mul_lt_mul_of_pos_right hh hden
      _ = ε := by field_simp
  obtain ⟨K, hK, hKS⟩ :=
    FK.precompact_of_uniform_modulus R M S rep hrep hbound hboundGlobal hmod
  refine ⟨K, hK, ?_⟩
  intro w hmem hH1 hnorm hvf
  apply hKS
  exact ⟨w, ⟨hmem, hH1, hnorm, hvf⟩, rfl⟩

end LerayHopf
