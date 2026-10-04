import Tengoku.LerayHopf.LerayHopf.R3.RellichBall
import Tengoku.Seed.Analysis.Convolution
import Tengoku.Seed.Analysis.Calculus.BumpFunction.Normed
import Tengoku.Seed.Topology.UniformSpace.Cauchy
import Tengoku.Seed.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

namespace LerayHopf
open MeasureTheory Filter Topology Metric TemperedDistribution
open scoped FourierTransform ENNReal SchwartzMap

/-!
# Fréchet–Kolmogorov L²-precompactness criterion (Pillar B, Stream B)

**Milestone id:** `frechet-kolmogorov` (Stream B — discharge the isolated FK hypothesis).

This file **discharges** the isolated analytic frontier
`FrechetKolmogorovInput` defined in `RellichBall.lean` (the standard Fréchet–Kolmogorov /
Riesz L²-precompactness criterion that mathlib still lacks).  It produces a genuine term

  `frechetKolmogorov_holds : FrechetKolmogorovInput`,

whose type is copied **verbatim** from `RellichBall.lean` — no weakening, no added
hypotheses.  Once proved, `localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds`
becomes an *unconditional* `LocalRellichInput`, which later (a separate capstone) lets
`SolutionInterfaces.lean` rewrite `spatial_compactness_R3` from `axiom` to `theorem`.

## What `FrechetKolmogorovInput` actually demands (copied from `RellichBall.lean`)

A family `S : Set (L2ballR3 R)`, with a global representative `rep f : L2VF_R3` for each
`f ∈ S` (`restrictToBall R (rep f) = f`), that is

* uniformly L²-bounded inside the ball (`∀ f ∈ S, ‖f‖ ≤ C`),
* uniformly L²-bounded GLOBALLY on the representative (`∀ f ∈ S, ‖rep f‖ ≤ C` — the standard
  Riesz full-mass control), and
* uniformly translation-equicontinuous in the GLOBAL L²-norm
  (`∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h, ‖h‖ < δ → ‖translate_L2VF h (rep f) − rep f‖ < ε`)

is contained in a compact `K ⊆ L2ballR3 R`.

It mentions NO Sobolev/gradient/`viscousFormSq`/`L2Sigma`/subsequence/limit object — it is
the pure abstract compactness *criterion*.  This file proves exactly that criterion.

## The standard FK route (decomposition into local lemmas)

The proof is the classical mollification + Arzelà–Ascoli + total-boundedness argument:

1. **Equicontinuity / equiboundedness of the mollified family.**
   `mollified_family_equicontinuous` + `mollified_family_uniformly_bounded`: the explicit
   representative `mollifyRep K (rep f)`, restricted to `x ∈ B_R`, is uniformly bounded and
   uniformly equicontinuous (Young's inequality `‖(η ⋆ g) x‖ ≤ ‖η‖₂‖g‖₂` + the kernel-only modulus
   of `η`).  The mass factor `‖g‖₂` localizes to the kernel-support enlargement `B_{R+r}` (the
   only region the kernel reaches from `B_R`), so these bounds need only the ENLARGED-BALL bound
   `‖restrictToBall (R+r) (rep f)‖ ≤ C`, which is supplied directly from the criterion's GLOBAL
   bound `hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity (the strengthened
   `FrechetKolmogorovInput`, round 4).  They are stated for the genuine smooth representative
   `mollifyRep` on `B_R`,
   NOT for an arbitrary operator `L2VF_R3 → L2VF_R3` (for which they would be false — e.g. `ρ = id`).
2. **Arzelà–Ascoli ⇒ total boundedness of the mollified family in C(ball), hence in L²(ball).**
   `mollified_family_totallyBounded_L2`.
3. **Mollification (approximate identity), assembled from steps 1–2.**  Convolve every family
   member with a CONCRETE smooth compactly-supported scalar kernel `K : MollifierKernel`, whose
   explicit continuous representative is `mollifyRep K f = η ⋆ f`.
   `convolution_l2_tendsto_uniform`: the convolutions approximate the originals in L² *uniformly
   over the family*, with the rate controlled by the uniform translation modulus (this is where
   the FK hypothesis is consumed), delegating the total-boundedness conjunct to step 2.
4. **Total-boundedness transfer.**  `totallyBounded_of_uniform_approx`: a set that is
   uniformly ε-approximable (step 3) by a totally bounded set (step 2) is itself totally
   bounded; with completeness of `L2ballR3 R` this gives precompactness
   (`isCompact_iff_totallyBounded_isComplete`).

The top-level `frechetKolmogorov_holds` assembles 1–4 into the FK criterion.

## History: `RellichBall.lean`'s residual `sorry` (`integrable_viscous_integrand_of_memH1`)

That residual `sorry` (H¹ ⇒ concrete `(2π)²‖ξ‖²`-weighted L²-integrability of the L²-Fourier
transform) was eventually discharged directly in `RellichBall.lean`, via a **self-contained**
`private` Bessel-weight helper chain there (`RellichBall.memH1_weightedL2_integrable_R` and
its supporting lemmas) — NOT via a helper exposed from this file, since `RellichBall.lean` is
*upstream* of `FrechetKolmogorov.lean` (this file imports `RellichBall`, not the reverse), so a
helper defined here could never have been importable there. This file used to carry its own
now-orphaned copy of that same Bessel-weight scaffolding (`besselWeightC` family,
`memH1_weightedL2_integrable`) built on the aspiration described in the superseded version of
this section; it had zero callers anywhere in the repo (confirmed by repo-wide grep) and was
deleted (issue #113 PR-2). See `RellichBall.lean`'s own docstring at
`memH1_weightedL2_integrable_R` for the (intentionally duplicated, not further refactored here)
self-contained route actually used.

## Honest scope (no overclaim) — ONE isolated frontier remains

This file is **fully proved (no `sorry`)**.  Both named analytic cores
(`young_convolution_memLp_L2`, `convolution_sub_L2_le_translation_modulus`), all assembly
plumbing, and the deliverable `frechetKolmogorov_holds` are proved.  The previously-isolated
`Lp`-valued Bochner-integral coeFn identity `convL2_coeFn_ae`
(`coeFn(∫ h, K.η h • τ_h g) =ᵐ mollifyRep K g`) is now DISCHARGED by the finite-set
inner-product-duality / shear-Fubini route (`convL2_setIntegral_inner`,
`mollifyRep_setIntegral_inner`, `fubini_integrand_integrable`, then
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`) — mathlib lacks the coeFn lemma directly and the
raw `ℝ³×ℝ³` double integral is not absolutely convergent, so the proof restricts Fubini to
finite-measure sets where absolute convergence holds.  No `axiom`/`opaque`/`constant` is introduced
and no `sorry` remains.  `frechetKolmogorov_holds` is a genuine DISCHARGE of the existing
`FrechetKolmogorovInput` type (not a new isolated hypothesis).

**Codex Gate round 3 (high) — local helper bounds vs. the deliverable, RESOLVED upstream.**
The mollifier-family helper bounds (steps 1–3) are TRUE only with an ENLARGED-BALL mass bound on
the kernel-support enlargement `B_{R + r}` (`r =` kernel support radius `K.supportRadius`), since
the mollified field on `B_R` only sees the original field over `B_{R+r}`.  A single-radius ball
bound on `B_R` plus a translation modulus does NOT control annulus mass on `B_{R+r} ∖ B_R`, so
the enlarged-ball bound is not recoverable from those two data alone.  This is now fixed UPSTREAM:
`RellichBall.FrechetKolmogorovInput` was strengthened to ALSO carry a uniform GLOBAL L²-norm bound
`hbddGlobal : ∀ f ∈ S, ‖rep f‖ ≤ C` (the standard Riesz full-mass control), from which any
enlarged-ball bound `‖restrictToBall (R + r₀) (rep f)‖ ≤ C` follows immediately by monotonicity of
ball mass in the radius (`‖restrictToBall R' g‖ ≤ ‖g‖`).  Hence the helper chain's `hbdEnl` is now
supplied directly from the criterion's own data, and `frechetKolmogorov_holds` is a pure
(proof-body) discharge — no upstream blocker remains.

## Architecture (standalone sibling)

Imports `R3.RellichBall` (for `FrechetKolmogorovInput`, `translate_L2VF`, `L2ballR3`,
`restrictToBall`), plus targeted mathlib (convolution + uniform-space compactness).  It does
NOT import `SolutionInterfaces.lean` and does NOT edit the root `LerayHopf.lean` (deferred wiring).

DAG position:
```
R3/SpatialCompactness.lean   (L2ballR3, restrictToBall, LocalRellichInput)
  └── R3/RellichBall.lean     (FrechetKolmogorovInput, translate_L2VF) [Stream B prereq]
        └── R3/FrechetKolmogorov.lean   [THIS FILE; discharges FrechetKolmogorovInput]
```

## Declarations (dependency order)

- `MollifierKernel`                        : concrete smooth compactly-supported scalar kernel (mollifier data)
- `mollifyRep`                             : explicit continuous representative of the mollified field (`η ⋆ f`)
- `exists_normalized_mollifierKernel`      : mass-one nonneg smooth kernel of support `≤ r` (from `ContDiffBump.normed`)
- `kernelL1R`                              : the kernel coerced to a scalar L¹-class (`‖η‖₁` in Young)
- `young_convolution_memLp_L2`             : analytic core SIG — global Young `‖η ⋆ g‖₂ ≤ ‖η‖₁·‖g‖₂` + `MemLp`
- `convolution_sub_L2_le_translation_modulus` : analytic core SIG — vector Minkowski form of the approximation rate
- `mollified_family_uniformly_bounded`     : FK step 1 — equibounded smoothed family (concrete `mollifyRep`)
- `mollified_family_equicontinuous`        : FK step 1 — equicontinuous smoothed family (concrete `mollifyRep`)
- `mollified_family_totallyBounded_L2`     : FK step 2 — Arzelà–Ascoli ⇒ totally bounded in L²(ball)
- `convolution_l2_tendsto_uniform`         : FK step 3 (assembly) — uniform L²-mollification approximate identity (routes through the two cores)
- `totallyBounded_of_uniform_approx`       : FK step 4 — total-boundedness transfer under uniform approximation
- `frechetKolmogorov_holds`                : DELIVERABLE — discharges `FrechetKolmogorovInput`

## Assumptions

Zero new `axiom`/`opaque`/`constant` and zero `sorry`.  The `Lp`-valued Bochner-integral coeFn
identity `convL2_coeFn_ae` is now fully proved (finite-set inner-product-duality / shear-Fubini).
`frechetKolmogorov_holds` is a real discharge of an existing hypothesis type, not a new
hypothesis.
-/

/-! ### Concrete mollifier — kernel data and explicit continuous representative

The Codex statement-gate flagged that mollifier-family bounds are FALSE when phrased for an
*arbitrary* operator `ρ : L2VF_R3 → L2VF_R3` (e.g. `ρ = id`): an L²-bounded family need not have
a pointwise sup bound or an equicontinuous representative, and pointwise evaluation of an `Lp`
class is not a faithful smooth representative.  The fix is to fix a CONCRETE mollification by an
explicit smooth, compactly supported scalar kernel `η : Domain3 → ℝ`, and to state every bound
for an EXPLICIT continuous representative

  `mollifyRep η f x := ∫ y, η (x − y) • (f y) ∂volume`,

which is a genuine pointwise-defined function of `x` (a vector-valued convolution `η ⋆ f`).  The
kernel-smoothness/compact-support hypotheses are exactly what make the bounds TRUE (Young's
inequality on the sup norm; equicontinuity from the kernel's own modulus). -/

/-- **Kernel data for the mollifier.**  A scalar approximate-identity kernel
`η : Domain3 → ℝ` that is smooth (`ContDiff ℝ ⊤`) and compactly supported — i.e. an admissible
mollifier.  Bundling the smoothness/compact-support hypotheses makes the family bounds below
genuinely true (rather than vacuously or falsely true for an arbitrary operator). -/
structure MollifierKernel where
  /-- The scalar kernel function. -/
  η : Domain3 → ℝ
  /-- The kernel is `C^∞`. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) η
  /-- The kernel has compact support (so all convolution integrals converge and are smooth). -/
  hasCompactSupport : HasCompactSupport η
  /-- An explicit support radius `r ≥ 0`: the kernel vanishes outside `closedBall 0 r`.  This
  is the enlargement radius the local family bounds are parameterized by — the mollified field
  on `B_R` only sees the original field over `B_{R+r}` (kernel reach), so an enlarged-ball bound
  on `B_{R+r}` is exactly what Young / Arzelà–Ascoli on `B_R` need; it is obtained from the
  criterion's GLOBAL bound `hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity. -/
  supportRadius : ℝ
  /-- The support radius is nonnegative. -/
  supportRadius_nonneg : 0 ≤ supportRadius
  /-- The kernel is supported in `closedBall 0 supportRadius`. -/
  tsupport_subset : tsupport η ⊆ Metric.closedBall (0 : Domain3) supportRadius
  /-- The kernel is nonnegative (an approximate-identity weight).  From
  `ContDiffBump.nonneg_normed`. -/
  nonneg : ∀ x, 0 ≤ η x
  /-- The kernel has unit mass (normalized approximate identity).  From
  `ContDiffBump.integral_normed`. -/
  mass_one : ∫ x, η x ∂(volume : Measure Domain3) = 1
  /-- The kernel is even (radial): `η (−h) = η h`.  `ContDiffBump.normed` depends on `x` only
  through `‖x‖`, and `‖−h‖ = ‖h‖`. -/
  even : ∀ h, η (-h) = η h

/-- **Explicit continuous representative of the mollified field.**

`mollifyRep K f x = ∫ y, K.η (x − y) • (f y : EuclideanSpace ℝ (Fin 3)) ∂volume` is the
genuine pointwise-defined vector-valued convolution `η ⋆ f`.  Because `K.η` is smooth and
compactly supported, this integral converges for every `x` and defines a smooth (in particular
continuous) function `Domain3 → EuclideanSpace ℝ (Fin 3)` — a *faithful* representative of the
mollified L²-class, on which pointwise sup and equicontinuity bounds are legitimate.

This is the concrete operator the family lemmas below are stated for, replacing the unsound
arbitrary `ρ : L2VF_R3 → L2VF_R3`. -/
noncomputable def mollifyRep (K : MollifierKernel) (f : L2VF_R3) :
    Domain3 → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∫ y : Domain3, K.η (x - y) • (f y : EuclideanSpace ℝ (Fin 3))
    ∂(volume : Measure Domain3)

/-- **Existence of a normalized mollifier kernel of arbitrarily small support.**

For every `r > 0` there is a `MollifierKernel K` whose support radius is `≤ r`.  It is the
`ContDiffBump (0 : Domain3)`-mollifier with `rIn = r/3 < rOut = r/2`, normalized to unit mass by
`ContDiffBump.normed volume`.  The resulting `K.η = bump.normed volume` is `C^∞`
(`contDiff_normed`), nonnegative (`nonneg_normed`), of mass one (`integral_normed`), and supported
in `closedBall 0 (r/2)` (`tsupport_normed_eq`), so `K.supportRadius = r/2 ≤ r`.

This is the concrete approximate-identity kernel feeding `convolution_l2_tendsto_uniform`: choosing
support `< δ` (the FK uniform translation-modulus radius for the target `ε`) drives the uniform
L²-approximation rate. -/
private noncomputable def exists_normalized_mollifierKernel (r : ℝ) (hr : 0 < r) :
    {K : MollifierKernel // K.supportRadius ≤ r} := by
  -- The bump with `0 < rIn = r/3 < rOut = r/2`.
  refine
    let bump : ContDiffBump (0 : Domain3) :=
      { rIn := r / 3
        rOut := r / 2
        rIn_pos := by positivity
        rIn_lt_rOut := by linarith }
    ⟨{ η := bump.normed (volume : Measure Domain3)
       smooth := bump.contDiff_normed
       hasCompactSupport := bump.hasCompactSupport_normed
       supportRadius := bump.rOut
       supportRadius_nonneg := bump.rOut_pos.le
       tsupport_subset := by
         rw [bump.tsupport_normed_eq (μ := (volume : Measure Domain3))]
       nonneg := fun x => bump.nonneg_normed (μ := (volume : Measure Domain3)) x
       mass_one := bump.integral_normed (μ := (volume : Measure Domain3))
       even := fun h => bump.normed_neg (μ := (volume : Measure Domain3)) h }, ?_⟩
  show bump.rOut ≤ r
  show r / 2 ≤ r
  linarith

/-! ### Mollifier sub-library — kernel as a scalar L²-class and reusable estimates

The two mollifier-family lemmas (`mollified_family_uniformly_bounded`,
`mollified_family_equicontinuous`) are short consequences of three reusable estimates about the
CONCRETE kernel.  We factor them out as named lemmas so each family lemma becomes a bounded
derivation rather than a monolithic analytic proof:

* `kernel_translate_L2_tendsto` — the kernel's own L²-translation modulus vanishes (η smooth +
  compact support ⇒ uniformly continuous ⇒ DCT).  This is the *uniform* (g-independent) modulus
  driving equicontinuity.
* `mollifyRep_sup_le` — Cauchy–Schwarz/Young pointwise sup bound on `B_R`, with the mass factor
  localized to the kernel-reach enlargement `B_{R + K.supportRadius}`.
* `mollifyRep_sub_le` — the convolution-difference estimate on `B_R`, factoring the modulus of
  `mollifyRep K f` through the kernel's L²-translation modulus times the enlarged-ball mass.

To state the kernel modulus we coerce the scalar kernel `K.η : Domain3 → ℝ` into the scalar L²
space `Lp ℝ 2 volume` (`kernelL2R`) and use the scalar translation `translate_L2R` (the scalar
mirror of `translate_L2VF`, same measure-preserving `(· + h)` plumbing). -/

/-- Scalar L² translation `τ_h g (x) = g (x − h)`, the `Lp ℝ 2 volume` mirror of
`translate_L2VF` (same measure-preserving `(· + h)` route). -/
noncomputable def translate_L2R (h : Domain3) (g : Lp ℝ 2 (volume : Measure Domain3)) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  Lp.compMeasurePreserving (· + h)
    (measurePreserving_add_right (volume : Measure Domain3) h) g

/-- The scalar kernel `K.η`, coerced to a scalar L²-class.  It is `MemLp` because it is continuous
(`K.smooth.continuous`) with compact support (`K.hasCompactSupport`). -/
noncomputable def kernelL2R (K : MollifierKernel) : Lp ℝ 2 (volume : Measure Domain3) :=
  MemLp.toLp K.η
    (K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport)

/-- The scalar kernel `K.η`, coerced to a scalar L¹-class.  It is `MemLp 1` because it is
continuous (`K.smooth.continuous`) with compact support (`K.hasCompactSupport`).  This is the mass
factor `‖η‖₁` in Young's convolution inequality `‖η ⋆ g‖₂ ≤ ‖η‖₁ · ‖g‖₂`. -/
noncomputable def kernelL1R (K : MollifierKernel) : Lp ℝ 1 (volume : Measure Domain3) :=
  MemLp.toLp K.η
    (K.smooth.continuous.memLp_of_hasCompactSupport (p := 1) (μ := volume) K.hasCompactSupport)

/-- Ball-mass monotonicity in the radius: restricting to a smaller ball does not increase the
`L²`-norm (`closedBall 0 a ⊆ closedBall 0 b` for `a ≤ b`, so the restricted measures are nested
and `eLpNorm_mono_measure` applies).  Mirrors `SpatialCompactness.norm_restrictToBall_le`
(which is the `b = ∞`/global case) at finite radii. -/
private theorem norm_restrictToBall_mono {a b : ℝ} (hab : a ≤ b) (w : L2VF_R3) :
    ‖restrictToBall a w‖ ≤ ‖restrictToBall b w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hsub : Metric.closedBall (0 : Domain3) a ⊆ Metric.closedBall (0 : Domain3) b :=
    Metric.closedBall_subset_closedBall hab
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) a)
      ≤ volume.restrict (Metric.closedBall (0 : Domain3) b) := Measure.restrict_mono hsub le_rfl
  have hca : ⇑(restrictToBall a w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) a)]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  have hcb : ⇑(restrictToBall b w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) b)]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hca, eLpNorm_congr_ae hcb]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcb]
  exact (Lp.memLp (restrictToBall b w)).2.ne

-- `norm_restrictToBall_le_global` (byte-identical to `SpatialCompactness.norm_restrictToBall_le`)
-- and `restrictToBall_sub` (byte-identical to the newly-public `SpatialCompactness.restrictToBall_sub`,
-- issue #111 PR-3) were private duplicates here; deleted, callers below use the imported public
-- versions directly (`RellichBall` already imports `R3.SpatialCompactness`).

/-- **Helper 1 — the kernel's L²-translation modulus vanishes.**

For a `MollifierKernel K`, the map `h ↦ ‖translate_L2R h (kernelL2R K) − kernelL2R K‖` tends to `0`
as `h → 0` in `Domain3`.  `K.η` is smooth with compact support, hence uniformly continuous and
dominated by a fixed compactly supported `L²` envelope, so dominated convergence gives L²-continuity
of translation of the kernel.  This is the *uniform* (g-independent) modulus that drives the
equicontinuity of the mollified family. -/
theorem kernel_translate_L2_tendsto (K : MollifierKernel) :
    Filter.Tendsto
      (fun h : Domain3 => ‖translate_L2R h (kernelL2R K) - kernelL2R K‖)
      (𝓝 (0 : Domain3)) (𝓝 (0 : ℝ)) := by
  -- mathlib provides L²-translation continuity off the shelf: `compMeasurePreserving` of an `Lp`
  -- class with a measure-preserving continuous map is continuous in both arguments
  -- (`Filter.Tendsto.compMeasurePreservingLp`).  We feed in the translations `(· + h)` (a continuous
  -- measure-preserving family on `Domain3`) and the constant class `kernelL2R K`.
  set μ : Measure Domain3 := volume with hμ
  -- the translation maps as continuous maps, measure preserving for every `h`.
  set g : Domain3 → C(Domain3, Domain3) :=
    fun h => ⟨(· + h), continuous_id.add continuous_const⟩ with hg
  have hgm : ∀ h : Domain3, MeasurePreserving (g h) μ μ := fun h =>
    measurePreserving_add_right μ h
  -- `Tendsto (g ·) (𝓝 0) (𝓝 (g 0))`: the family `h ↦ (· + h)` is continuous in `h`.
  have hgcont : Continuous g := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : Domain3 × Domain3 => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have htend := Filter.Tendsto.compMeasurePreservingLp
    (μ := μ) (ν := μ) (E := ℝ) (p := 2)
    (f := fun _ : Domain3 => kernelL2R K) (f₀ := kernelL2R K)
    (g := g) (g₀ := g 0)
    tendsto_const_nhds (hgcont.tendsto 0) hgm (hgm 0) (by simp)
  -- identify the two `compMeasurePreserving` expressions with `translate_L2R` and `kernelL2R K`.
  have heq : (fun h : Domain3 => Lp.compMeasurePreserving (g h) (hgm h) (kernelL2R K))
      = fun h : Domain3 => translate_L2R h (kernelL2R K) := rfl
  have h0 : Lp.compMeasurePreserving (g 0) (hgm 0) (kernelL2R K) = kernelL2R K := by
    have : (g 0 : Domain3 → Domain3) = id := by
      funext x; simp [hg]
    -- `g 0 = (· + 0) = id`, so the composition is the identity on `Lp`.
    refine Lp.ext ?_
    have hcoe := Lp.coeFn_compMeasurePreserving (kernelL2R K) (hgm 0)
    filter_upwards [hcoe] with x hx
    rw [hx]
    simp [hg]
  rw [heq, h0] at htend
  -- continuity of the norm-of-difference turns the `Lp`-convergence into the scalar `Tendsto`.
  have hsub : Filter.Tendsto
      (fun h : Domain3 => translate_L2R h (kernelL2R K) - kernelL2R K)
      (𝓝 0) (𝓝 (kernelL2R K - kernelL2R K)) := htend.sub tendsto_const_nhds
  have hnorm := hsub.norm
  simpa using hnorm

/-- **Helper 2 — pointwise sup bound for the mollified field (Cauchy–Schwarz / Young).**

For `x ∈ closedBall 0 R`, the convolution value `mollifyRep K f x = ∫ y, K.η (x−y) • f y` is bounded
by `‖kernelL2R K‖ · ‖restrictToBall (R + K.supportRadius) f‖`.  Cauchy–Schwarz on the integrand
`K.η(x−y) • f y` gives `‖kernel‖₂ · ‖f‖₂`, and because `K.η` is supported in
`closedBall 0 K.supportRadius` the integral only sees `f` over `y ∈ B_{R + K.supportRadius}`
(kernel reach from `B_R`), localizing the mass factor to the enlarged ball. -/
theorem mollifyRep_sup_le (K : MollifierKernel) (f : L2VF_R3) (R : ℝ)
    {x : Domain3} (hx : x ∈ Metric.closedBall (0 : Domain3) R) :
    ‖mollifyRep K f x‖
      ≤ ‖kernelL2R K‖ * ‖restrictToBall (R + K.supportRadius) f‖ := by
  classical
  set r := K.supportRadius with hr
  -- The enlarged ball `B_{R+r}` (kernel reach from `B_R`).
  set B : Set Domain3 := Metric.closedBall (0 : Domain3) (R + r) with hB
  -- The kernel as an `L²`-class envelope, and the two scalar L² factors of Cauchy–Schwarz.
  have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
  have hηaesm : AEStronglyMeasurable K.η (volume : Measure Domain3) := hηmem.aestronglyMeasurable
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Domain3) x
  -- factor `a = |K.η(x−·)|` (kernel slice), `b = 1_B · ‖f·‖` (localized mass).
  have ha : MemLp (fun y : Domain3 => |K.η (x - y)|) 2 (volume : Measure Domain3) :=
    (hηmem.comp_measurePreserving hmp).abs
  have hfnorm : MemLp (fun y : Domain3 => ‖(f y : EuclideanSpace ℝ (Fin 3))‖) 2
      (volume : Measure Domain3) := (Lp.memLp f).norm
  have hb : MemLp (B.indicator (fun y : Domain3 => ‖(f y : EuclideanSpace ℝ (Fin 3))‖)) 2
      (volume : Measure Domain3) := hfnorm.indicator measurableSet_closedBall
  -- STEP 1: `‖mollifyRep K f x‖ ≤ ∫ |K.η(x−y)| · 1_B(y) ‖f y‖` (kernel-reach localization).
  have hstep1 : ‖mollifyRep K f x‖
      ≤ ∫ y : Domain3, |K.η (x - y)| * B.indicator
          (fun z : Domain3 => ‖(f z : EuclideanSpace ℝ (Fin 3))‖) y
          ∂(volume : Measure Domain3) := by
    rw [mollifyRep]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae ?_))
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hzero : K.η (x - y) = 0
    · simp [hzero]
    · have hmem : x - y ∈ tsupport K.η := subset_tsupport K.η (by simpa using hzero)
      have hball : x - y ∈ Metric.closedBall (0 : Domain3) r := K.tsupport_subset hmem
      have hxy : ‖x - y‖ ≤ r := by simpa [dist_eq_norm] using hball
      have hxR : ‖x‖ ≤ R := by simpa [dist_eq_norm] using hx
      have hyR : ‖y‖ ≤ R + r := by
        have h1 : y = x - (x - y) := by abel
        have h2 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
          rw [h1]; exact (norm_sub_le _ _).trans_eq (by rw [sub_sub_cancel])
        linarith
      have hyball : y ∈ B := by simpa [hB, dist_eq_norm] using hyR
      rw [Set.indicator_of_mem hyball]
  -- STEP 2: Cauchy–Schwarz in `Lp ℝ 2` on the two factors.
  have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
  rw [L2.inner_def] at hcs
  have heq : (∫ y : Domain3, |K.η (x - y)| * B.indicator
        (fun z : Domain3 => ‖(f z : EuclideanSpace ℝ (Fin 3))‖) y ∂(volume : Measure Domain3))
      = ∫ y : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) y) ((hb.toLp _ : Domain3 → ℝ) y))
          ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y hay hby
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hay, hby, mul_comm]
  -- STEP 3: identify the two `Lp`-norms with `‖kernelL2R K‖` and `‖restrictToBall (R+r) f‖`.
  have hna : ‖ha.toLp _‖ = ‖kernelL2R K‖ := by
    rw [kernelL2R, Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    have habs : AEStronglyMeasurable (fun y : Domain3 => |K.η y|) (volume : Measure Domain3) :=
      hηaesm.norm.congr (by filter_upwards with y using (Real.norm_eq_abs _))
    rw [show (fun y : Domain3 => |K.η (x - y)|) = (fun y : Domain3 => |K.η y|) ∘ (fun y => x - y)
        from rfl, eLpNorm_comp_measurePreserving habs hmp]
    rw [show (fun y : Domain3 => |K.η y|) = (fun y : Domain3 => ‖K.η y‖) from
        funext fun y => (Real.norm_eq_abs _).symm, eLpNorm_norm]
  have hnb : ‖hb.toLp _‖ = ‖restrictToBall (R + r) f‖ := by
    rw [restrictToBall, Lp.norm_toLp, Lp.norm_toLp,
      ← eLpNorm_norm (f : Domain3 → EuclideanSpace ℝ (Fin 3)),
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  -- Assemble.
  calc ‖mollifyRep K f x‖
      ≤ ∫ y : Domain3, |K.η (x - y)| * B.indicator
          (fun z : Domain3 => ‖(f z : EuclideanSpace ℝ (Fin 3))‖) y
          ∂(volume : Measure Domain3) := hstep1
    _ = ∫ y : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) y) ((hb.toLp _ : Domain3 → ℝ) y))
          ∂(volume : Measure Domain3) := heq
    _ ≤ ‖ha.toLp _‖ * ‖hb.toLp _‖ := hcs
    _ = ‖kernelL2R K‖ * ‖restrictToBall (R + r) f‖ := by rw [hna, hnb]

/-- **Textbook step (kernel reach).**  If `‖p‖ ≤ R` and the kernel slice `z ↦ K.η (p − z)` is
nonzero at `z`, then `z` lies in the enlarged ball `B_{R + K.supportRadius}`.

This is the geometric content of "the mollified field on `B_R` only sees `f` over `B_{R+r}`":
`K.η` vanishes off `closedBall 0 K.supportRadius`, so `K.η (p − z) ≠ 0` forces `‖p − z‖ ≤ r`,
and the triangle inequality then bounds `‖z‖` by `R + r`. -/
private theorem mem_closedBall_add_supportRadius_of_kernel_ne_zero
    (K : MollifierKernel) (R : ℝ) {p z : Domain3} (hpR : ‖p‖ ≤ R)
    (hpne : K.η (p - z) ≠ 0) :
    z ∈ Metric.closedBall (0 : Domain3) (R + K.supportRadius) := by
  have hmemt : p - z ∈ tsupport K.η := subset_tsupport K.η (by simpa using hpne)
  have hball : p - z ∈ Metric.closedBall (0 : Domain3) K.supportRadius :=
    K.tsupport_subset hmemt
  have hpz : ‖p - z‖ ≤ K.supportRadius := by simpa [dist_eq_norm] using hball
  have hzR : ‖z‖ ≤ R + K.supportRadius := by
    have h1 : z = p - (p - z) := by abel
    have h2 : ‖z‖ ≤ ‖p‖ + ‖p - z‖ := by
      rw [h1]; exact (norm_sub_le _ _).trans_eq (by rw [sub_sub_cancel])
    linarith
  simpa [dist_eq_norm] using hzR

/-- **Textbook step (translated-kernel difference, `coeFn` form).**  The `L²`-class
`translate_L2R v (kernelL2R K) − kernelL2R K` is represented pointwise a.e. by the shifted
kernel difference `w ↦ K.η (w + v) − K.η w`.

Unfolding `translate_L2R` (a `compMeasurePreserving` by `(· + v)`) and `kernelL2R` (a `toLp`)
and transporting the kernel's `coeFn` identity along the measure-preserving shift. -/
private theorem coeFn_translate_kernelL2R_sub (K : MollifierKernel) (v : Domain3) :
    ((translate_L2R v (kernelL2R K) - kernelL2R K :
        Lp ℝ 2 (volume : Measure Domain3)) : Domain3 → ℝ)
      =ᵐ[volume] fun w : Domain3 => K.η (w + v) - K.η w := by
  have hsub := Lp.coeFn_sub (translate_L2R v (kernelL2R K)) (kernelL2R K)
  have htr : (translate_L2R v (kernelL2R K) : Domain3 → ℝ)
      =ᵐ[volume] fun w : Domain3 => (kernelL2R K : Domain3 → ℝ) (w + v) := by
    rw [translate_L2R]
    exact Lp.coeFn_compMeasurePreserving (kernelL2R K)
      (measurePreserving_add_right (volume : Measure Domain3) v)
  have hker : (kernelL2R K : Domain3 → ℝ) =ᵐ[volume] K.η := by
    rw [kernelL2R]; exact MemLp.coeFn_toLp _
  have hkershift : (fun w : Domain3 => (kernelL2R K : Domain3 → ℝ) (w + v))
      =ᵐ[volume] fun w : Domain3 => K.η (w + v) :=
    (measurePreserving_add_right (volume : Measure Domain3)
      v).quasiMeasurePreserving.ae_eq_comp hker
  filter_upwards [hsub, htr, hkershift, hker] with w hw1 hw2 hw3 hw4
  rw [hw1]
  simp only [Pi.sub_apply]
  rw [hw2, hw3, hw4]

/-- **Textbook step (kernel translation modulus).**  The `L²`-norm of the kernel slice difference
`z ↦ |K.η (x − z) − K.η (y − z)|` equals the kernel's own translation modulus at the shift `x − y`,
namely `‖translate_L2R (x − y) (kernelL2R K) − kernelL2R K‖`.

The change of variables `z ↦ y − z` (measure-preserving) turns the slice difference into
`w ↦ |K.η (w + (x − y)) − K.η w|`, which by `coeFn_translate_kernelL2R_sub` is the modulus of the
translate-difference class. -/
private theorem norm_toLp_kernel_slice_sub_eq_translate_modulus (K : MollifierKernel)
    (x y : Domain3)
    (ha : MemLp (fun z : Domain3 => |K.η (x - z) - K.η (y - z)|) 2
      (volume : Measure Domain3)) :
    ‖ha.toLp _‖ = ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ := by
  have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
  have hηaesm : AEStronglyMeasurable K.η (volume : Measure Domain3) :=
    hηmem.aestronglyMeasurable
  have hmpy := Measure.measurePreserving_sub_left (volume : Measure Domain3) y
  rw [Lp.norm_toLp]
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_translate_kernelL2R_sub K (x - y))]
  have hcompose : (fun z : Domain3 => |K.η (x - z) - K.η (y - z)|)
      = (fun w : Domain3 => |K.η (w + (x - y)) - K.η w|) ∘ (fun z : Domain3 => y - z) := by
    funext z
    simp only [Function.comp_apply]
    congr 2
    · congr 1; abel
  have hshiftm : AEStronglyMeasurable (fun w : Domain3 => K.η (w + (x - y)))
      (volume : Measure Domain3) :=
    hηaesm.comp_measurePreserving
      (measurePreserving_add_right (volume : Measure Domain3) (x - y))
  have habsm : AEStronglyMeasurable (fun w : Domain3 => |K.η (w + (x - y)) - K.η w|)
      (volume : Measure Domain3) :=
    (hshiftm.sub hηaesm).norm.congr (by filter_upwards with w using (Real.norm_eq_abs _))
  rw [hcompose, eLpNorm_comp_measurePreserving habsm hmpy]
  rw [show (fun w : Domain3 => |K.η (w + (x - y)) - K.η w|)
      = (fun w : Domain3 => ‖K.η (w + (x - y)) - K.η w‖) from
      funext fun w => (Real.norm_eq_abs _).symm, eLpNorm_norm]

/-- **Helper 3 — convolution-difference estimate (modulus of the mollified field).**

For `x, y ∈ closedBall 0 R`, the increment of the mollified field is bounded by the enlarged-ball
mass of `f` times the kernel's own L²-translation modulus at the shift `x − y`:

  `‖mollifyRep K f x − mollifyRep K f y‖`
      `≤ ‖restrictToBall (R + K.supportRadius) f‖ · ‖translate_L2R (x − y) (kernelL2R K) − kernelL2R K‖`.

After the change of variables `z = x − y'` the difference is `∫ (K.η(x−·) − K.η(y−·)) • f`, and
Cauchy–Schwarz factors it as (kernel translation-modulus)·(enlarged-ball mass of `f`). -/
theorem mollifyRep_sub_le (K : MollifierKernel) (f : L2VF_R3) (R : ℝ)
    {x y : Domain3} (hx : x ∈ Metric.closedBall (0 : Domain3) R)
    (hy : y ∈ Metric.closedBall (0 : Domain3) R) :
    ‖mollifyRep K f x - mollifyRep K f y‖
      ≤ ‖restrictToBall (R + K.supportRadius) f‖
          * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ := by
  classical
  set r := K.supportRadius with hr
  -- The enlarged ball `B_{R+r}` (kernel reach from `B_R`).
  set B : Set Domain3 := Metric.closedBall (0 : Domain3) (R + r) with hB
  -- The kernel as an `L²`-class envelope.
  have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
  -- the two measure-preserving slice maps `(x − ·)` and `(y − ·)`.
  have hmpx := Measure.measurePreserving_sub_left (volume : Measure Domain3) x
  have hmpy := Measure.measurePreserving_sub_left (volume : Measure Domain3) y
  -- factor `a = |K.η(x−·) − K.η(y−·)|` (kernel slice difference).
  have haxmem : MemLp (fun z : Domain3 => K.η (x - z)) 2 (volume : Measure Domain3) :=
    hηmem.comp_measurePreserving hmpx
  have haymem : MemLp (fun z : Domain3 => K.η (y - z)) 2 (volume : Measure Domain3) :=
    hηmem.comp_measurePreserving hmpy
  have ha : MemLp (fun z : Domain3 => |K.η (x - z) - K.η (y - z)|) 2
      (volume : Measure Domain3) := (haxmem.sub haymem).abs
  -- factor `b = 1_B · ‖f·‖` (localized mass).
  have hfnorm : MemLp (fun y : Domain3 => ‖(f y : EuclideanSpace ℝ (Fin 3))‖) 2
      (volume : Measure Domain3) := (Lp.memLp f).norm
  have hb : MemLp (B.indicator (fun y : Domain3 => ‖(f y : EuclideanSpace ℝ (Fin 3))‖)) 2
      (volume : Measure Domain3) := hfnorm.indicator measurableSet_closedBall
  -- STEP 0: `mollifyRep K f x − mollifyRep K f y = ∫ z, (K.η(x−z) − K.η(y−z)) • f z`.
  have hdiff : mollifyRep K f x - mollifyRep K f y
      = ∫ z : Domain3, (K.η (x - z) - K.η (y - z)) • (f z : EuclideanSpace ℝ (Fin 3))
          ∂(volume : Measure Domain3) := by
    rw [mollifyRep, mollifyRep, ← integral_sub]
    · refine integral_congr_ae ?_
      filter_upwards with z
      rw [sub_smul]
    · exact memLp_one_iff_integrable.mp (MemLp.smul (Lp.memLp f) haxmem (r := 1))
    · exact memLp_one_iff_integrable.mp (MemLp.smul (Lp.memLp f) haymem (r := 1))
  -- STEP 1: `‖·‖ ≤ ∫ |K.η(x−z) − K.η(y−z)| · 1_B(z) ‖f z‖` (kernel-reach localization).
  have hstep1 : ‖mollifyRep K f x - mollifyRep K f y‖
      ≤ ∫ z : Domain3, |K.η (x - z) - K.η (y - z)| * B.indicator
          (fun w : Domain3 => ‖(f w : EuclideanSpace ℝ (Fin 3))‖) z
          ∂(volume : Measure Domain3) := by
    rw [hdiff]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae ?_))
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hzero : K.η (x - z) - K.η (y - z) = 0
    · simp [hzero]
    · -- at least one of the two kernel slices is nonzero; either reaches `z` into `B`.
      have hxR : ‖x‖ ≤ R := by simpa [dist_eq_norm] using hx
      have hyR : ‖y‖ ≤ R := by simpa [dist_eq_norm] using hy
      -- kernel reach: a nonzero kernel slice pulls `z` into the enlarged ball `B_{R+r}`.
      have hreach : ∀ {p : Domain3}, ‖p‖ ≤ R → K.η (p - z) ≠ 0 → z ∈ B := by
        intro p hpR hpne
        simpa [hB, hr] using
          mem_closedBall_add_supportRadius_of_kernel_ne_zero K R hpR hpne
      have hmem : z ∈ B := by
        rcases (not_and_or.mp (fun hpair => hzero (by rw [hpair.1, hpair.2, sub_self])) :
            K.η (x - z) ≠ 0 ∨ K.η (y - z) ≠ 0) with hxne | hyne
        · exact hreach hxR hxne
        · exact hreach hyR hyne
      rw [Set.indicator_of_mem hmem]
  -- STEP 2: Cauchy–Schwarz in `Lp ℝ 2` on the two factors.
  have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
  rw [L2.inner_def] at hcs
  have heq : (∫ z : Domain3, |K.η (x - z) - K.η (y - z)| * B.indicator
        (fun w : Domain3 => ‖(f w : EuclideanSpace ℝ (Fin 3))‖) z ∂(volume : Measure Domain3))
      = ∫ z : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) z) ((hb.toLp _ : Domain3 → ℝ) z))
          ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z haz hbz
    simp only [RCLike.inner_apply, conj_trivial]
    rw [haz, hbz, mul_comm]
  -- STEP 3: identify the two `Lp`-norms.
  -- The mass factor identifies with `‖restrictToBall (R+r) f‖` (verbatim from `mollifyRep_sup_le`).
  have hnb : ‖hb.toLp _‖ = ‖restrictToBall (R + r) f‖ := by
    rw [restrictToBall, Lp.norm_toLp, Lp.norm_toLp,
      ← eLpNorm_norm (f : Domain3 → EuclideanSpace ℝ (Fin 3)),
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  -- The kernel-difference factor identifies with the translation modulus
  -- `‖translate_L2R (x−y) (kernelL2R K) − kernelL2R K‖` via the change of variables
  -- `z ↦ y − z`:  `K.η(x−z) − K.η(y−z) = D(y−z)` with `D(w) = K.η(w + (x−y)) − K.η(w)`,
  -- and `D` is the coeFn of `translate_L2R (x−y) (kernelL2R K) − kernelL2R K`.
  have hna : ‖ha.toLp _‖
      = ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ :=
    norm_toLp_kernel_slice_sub_eq_translate_modulus K x y ha
  -- Assemble.
  calc ‖mollifyRep K f x - mollifyRep K f y‖
      ≤ ∫ z : Domain3, |K.η (x - z) - K.η (y - z)| * B.indicator
          (fun w : Domain3 => ‖(f w : EuclideanSpace ℝ (Fin 3))‖) z
          ∂(volume : Measure Domain3) := hstep1
    _ = ∫ z : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) z) ((hb.toLp _ : Domain3 → ℝ) z))
          ∂(volume : Measure Domain3) := heq
    _ ≤ ‖ha.toLp _‖ * ‖hb.toLp _‖ := hcs
    _ = ‖restrictToBall (R + r) f‖ * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ := by
        rw [hna, hnb, mul_comm]

/-! ### FK step 0 — preliminaries: global Young + vector Minkowski analytic cores

The two genuinely-missing analytic facts behind `convolution_l2_tendsto_uniform`, isolated as
named helper SIGNATURES (bodies deferred to `lean-prover`):

* `young_convolution_memLp_L2` — GLOBAL Young inequality `‖η ⋆ g‖₂ ≤ ‖η‖₁ · ‖g‖₂`: the convolution
  `mollifyRep K g` is itself in `L²(ℝ³)` (not just locally on `B_R`), with its `L²`-norm bounded by
  the kernel's `L¹`-mass times `‖g‖₂`.  Mathlib has `MeasureTheory.convolution` continuity / Young
  on `L^p` only fragmentarily for this vector-valued, measure-`volume` setting.
* `convolution_sub_L2_le_translation_modulus` — the vector-valued Minkowski integral inequality
  `‖∫ F(h) dh‖₂ ≤ ∫ ‖F(h)‖₂ dh` applied to `(η ⋆ g) − g = ∫ h, η(h) (τ_h g − g) dh` (mass-one
  kernel), yielding `‖η ⋆ g − g‖₂ ≤ ∫ h, η(h) · ‖τ_h g − g‖₂ dh`.  Combined with the FK uniform
  translation modulus and `K.supportRadius < δ`, this gives the uniform `< ε` approximation rate.
-/

/-! ### Shared Bochner-`Lp` integral primitive for the two analytic cores

Both analytic cores (`young_convolution_memLp_L2`, `convolution_sub_L2_le_translation_modulus`)
follow from a single identity expressing the `L²`-class of the convolution `mollifyRep K g` as an
`Lp`-valued Bochner integral of kernel-weighted translates:

  `toLp (mollifyRep K g) = ∫ h, K.η h • translate_L2VF h g ∂volume`   (an `L2VF_R3`-valued integral).

Once this identity and the Bochner-integrability of `h ↦ K.η h • translate_L2VF h g` are in hand,
`MeasureTheory.norm_integral_le_integral_norm` (valid in the Banach space `L2VF_R3`) plus
`‖translate_L2VF h g‖ = ‖g‖` and the kernel facts (`nonneg`, `mass_one`) deliver both cores. -/

/-- The translation family `h ↦ translate_L2VF h g` is continuous (`Lp` translation-continuity,
the vector-valued mirror of `kernel_translate_L2_tendsto`'s ingredient). -/
private theorem continuous_translate_L2VF (g : L2VF_R3) :
    Continuous (fun h : Domain3 => translate_L2VF h g) := by
  set g' : Domain3 → C(Domain3, Domain3) :=
    fun h => ⟨(· + h), continuous_id.add continuous_const⟩ with hg'
  have hgm : ∀ h : Domain3, MeasurePreserving (g' h) (volume : Measure Domain3) volume :=
    fun h => measurePreserving_add_right (volume : Measure Domain3) h
  have hg'cont : Continuous g' := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : Domain3 × Domain3 => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have := Continuous.compMeasurePreservingLp (μ := (volume : Measure Domain3))
    (ν := (volume : Measure Domain3)) (E := EuclideanSpace ℝ (Fin 3)) (p := 2)
    (f := fun _ : Domain3 => g) (g := g') continuous_const hg'cont hgm (by simp)
  exact this

/-- The kernel-weighted translation family `h ↦ K.η h • translate_L2VF h g` is Bochner
integrable as an `L2VF_R3`-valued map: it is continuous (so strongly measurable) and supported in
`tsupport K.η ⊆ closedBall 0 K.supportRadius` (compact), with `‖K.η h • translate_L2VF h g‖
= |K.η h| · ‖g‖` bounded. -/
private theorem integrable_kernel_smul_translate (K : MollifierKernel) (g : L2VF_R3) :
    Integrable (fun h : Domain3 => K.η h • translate_L2VF h g) (volume : Measure Domain3) := by
  have hcont : Continuous (fun h : Domain3 => K.η h • translate_L2VF h g) :=
    (K.smooth.continuous).smul (continuous_translate_L2VF g)
  -- compact support: outside `tsupport K.η` the scalar factor is `0`.
  have hsupp : HasCompactSupport (fun h : Domain3 => K.η h • translate_L2VF h g) := by
    apply HasCompactSupport.intro (K.hasCompactSupport.isCompact) (fun h hh => ?_)
    have : K.η h = 0 := by
      by_contra hne
      exact hh (subset_tsupport K.η (by simpa using hne))
    simp [this]
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- `‖K.η h • translate_L2VF h g‖ = K.η h · ‖g‖` (using `K.nonneg` so `|K.η h| = K.η h`). -/
private theorem norm_kernel_smul_translate (K : MollifierKernel) (g : L2VF_R3) (h : Domain3) :
    ‖K.η h • translate_L2VF h g‖ = K.η h * ‖g‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (K.nonneg h)]
  congr 1
  rw [translate_L2VF, Lp.norm_compMeasurePreserving]

/-- The `L¹`-mass of the kernel is `1` (`K.nonneg` ⇒ `|η| = η`, `K.mass_one`). -/
private theorem norm_kernelL1R (K : MollifierKernel) : ‖kernelL1R K‖ = 1 := by
  rw [kernelL1R]
  -- `‖MemLp.toLp K.η _‖ = ∫ |K.η| = ∫ K.η = 1`.
  have hmem : MemLp K.η 1 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 1) (μ := volume) K.hasCompactSupport
  have hint : Integrable K.η (volume : Measure Domain3) := memLp_one_iff_integrable.mp hmem
  rw [show MemLp.toLp K.η hmem = (hint.toL1 K.η) from rfl, L1.norm_of_fun_eq_integral_norm]
  rw [show (fun a => ‖K.η a‖) = K.η from funext fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (K.nonneg a)]]
  exact K.mass_one

/-- **The kernel-weighted-translate `Lp`-valued Bochner integral** — the convolution `η ⋆ g`
realized as a genuine element of `L²(ℝ³)` (no `MemLp` side-condition needed: the integrand is
Bochner integrable by `integrable_kernel_smul_translate`). -/
private noncomputable def convL2 (K : MollifierKernel) (g : L2VF_R3) : L2VF_R3 :=
  ∫ h : Domain3, K.η h • translate_L2VF h g ∂(volume : Measure Domain3)

/-- **Global Young bound at the `Lp`-Bochner level (PROVED, no frontier).**
`‖convL2 K g‖ ≤ ‖g‖` straight from `‖∫ F‖ ≤ ∫ ‖F‖` in the Banach space `L2VF_R3`,
`‖K.η h • τ_h g‖ = K.η h · ‖g‖` (`norm_kernel_smul_translate`), and `∫ K.η = 1` (`K.mass_one`).
This is the entire norm content of Young's inequality — it needs neither the pointwise
convolution nor the (isolated) coeFn identity. -/
private theorem convL2_norm_le (K : MollifierKernel) (g : L2VF_R3) :
    ‖convL2 K g‖ ≤ ‖g‖ := by
  have hle : ‖convL2 K g‖
      ≤ ∫ h : Domain3, ‖K.η h • translate_L2VF h g‖ ∂(volume : Measure Domain3) :=
    norm_integral_le_integral_norm _
  have hcongr : (∫ h : Domain3, ‖K.η h • translate_L2VF h g‖ ∂(volume : Measure Domain3))
      = ∫ h : Domain3, K.η h * ‖g‖ ∂(volume : Measure Domain3) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    exact norm_kernel_smul_translate K g h
  rw [hcongr, integral_mul_const, K.mass_one, one_mul] at hle
  exact hle

/-! ### Discharging the coeFn identity `convL2_coeFn_ae` — finite-set inner-product duality

The coeFn identity `⇑(convL2 K g) =ᵐ mollifyRep K g` is the last genuine frontier.  We prove it
by the route advertised in its docstring, broken into reusable pieces:

* `mollifyRep_apply_bound` / `continuous_mollifyRep` / `integrableOn_mollifyRep` — the pointwise
  convolution `mollifyRep K g` is globally bounded (Cauchy–Schwarz, `‖kernelL2R K‖·‖g‖`),
  continuous, hence integrable on every finite-measure set;
* `convL2_setIntegral_inner` — pairing the `Lp`-valued integral `convL2 K g` with a constant `c`
  over a finite set `s`, commuting the inner product through the Bochner integral
  (`integral_inner` / `ContinuousLinearMap.integral_comp_comm`) and `inner_indicatorConstLp_*`;
* `mollifyRep_setIntegral_inner` — the matching scalar double integral for `mollifyRep`, with the
  finite-set Fubini (`integral_integral_swap`) and shear (`measurePreserving_prod_add`) made
  legitimate by absolute convergence on the FINITE set `s`;
* the two agree (via `K.even`), so `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` closes it. -/

/-- Global Cauchy–Schwarz / Young sup bound for the pointwise convolution, valid at EVERY `x`
(no ball localization): `‖mollifyRep K g x‖ ≤ ‖kernelL2R K‖ · ‖g‖`.  Same Cauchy–Schwarz as
`mollifyRep_sup_le` but with the trivial enlarged ball `B = univ`. -/
private theorem mollifyRep_apply_bound (K : MollifierKernel) (g : L2VF_R3) (x : Domain3) :
    ‖mollifyRep K g x‖ ≤ ‖kernelL2R K‖ * ‖g‖ := by
  classical
  have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
  have hηaesm : AEStronglyMeasurable K.η (volume : Measure Domain3) := hηmem.aestronglyMeasurable
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Domain3) x
  have ha : MemLp (fun y : Domain3 => |K.η (x - y)|) 2 (volume : Measure Domain3) :=
    (hηmem.comp_measurePreserving hmp).abs
  have hb : MemLp (fun y : Domain3 => ‖(g y : EuclideanSpace ℝ (Fin 3))‖) 2
      (volume : Measure Domain3) := (Lp.memLp g).norm
  have hstep1 : ‖mollifyRep K g x‖
      ≤ ∫ y : Domain3, |K.η (x - y)| * ‖(g y : EuclideanSpace ℝ (Fin 3))‖
          ∂(volume : Measure Domain3) := by
    rw [mollifyRep]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae ?_))
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs]
  have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
  rw [L2.inner_def] at hcs
  have heq : (∫ y : Domain3, |K.η (x - y)| * ‖(g y : EuclideanSpace ℝ (Fin 3))‖
        ∂(volume : Measure Domain3))
      = ∫ y : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) y) ((hb.toLp _ : Domain3 → ℝ) y))
          ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y hay hby
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hay, hby, mul_comm]
  have hna : ‖ha.toLp _‖ = ‖kernelL2R K‖ := by
    rw [kernelL2R, Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    have habs : AEStronglyMeasurable (fun y : Domain3 => |K.η y|) (volume : Measure Domain3) :=
      hηaesm.norm.congr (by filter_upwards with y using (Real.norm_eq_abs _))
    rw [show (fun y : Domain3 => |K.η (x - y)|) = (fun y : Domain3 => |K.η y|) ∘ (fun y => x - y)
        from rfl, eLpNorm_comp_measurePreserving habs hmp]
    rw [show (fun y : Domain3 => |K.η y|) = (fun y : Domain3 => ‖K.η y‖) from
        funext fun y => (Real.norm_eq_abs _).symm, eLpNorm_norm]
  have hnb : ‖hb.toLp _‖ = ‖g‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, ← eLpNorm_norm (g : Domain3 → EuclideanSpace ℝ (Fin 3))]
  calc ‖mollifyRep K g x‖
      ≤ ∫ y : Domain3, |K.η (x - y)| * ‖(g y : EuclideanSpace ℝ (Fin 3))‖
          ∂(volume : Measure Domain3) := hstep1
    _ = ∫ y : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) y) ((hb.toLp _ : Domain3 → ℝ) y))
          ∂(volume : Measure Domain3) := heq
    _ ≤ ‖ha.toLp _‖ * ‖hb.toLp _‖ := hcs
    _ = ‖kernelL2R K‖ * ‖g‖ := by rw [hna, hnb]

/-- `mollifyRep K g` is the `lsmul`-convolution `K.η ⋆ ⇑g`, so it is **continuous**: the kernel is
continuous with compact support and `⇑g ∈ L²` is locally integrable. -/
private theorem continuous_mollifyRep (K : MollifierKernel) (g : L2VF_R3) :
    Continuous (mollifyRep K g) := by
  have hconv : mollifyRep K g
      = MeasureTheory.convolution K.η (g : Domain3 → EuclideanSpace ℝ (Fin 3))
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure Domain3) := by
    funext x
    rw [mollifyRep, convolution_lsmul_swap]
  rw [hconv]
  exact K.hasCompactSupport.continuous_convolution_left _ K.smooth.continuous
    ((Lp.memLp g).locallyIntegrable (by norm_num))

/-- `mollifyRep K g` is **integrable on every finite-measure set** (continuous and globally
bounded by `‖kernelL2R K‖·‖g‖`). -/
private theorem integrableOn_mollifyRep (K : MollifierKernel) (g : L2VF_R3)
    {s : Set Domain3} (hμs : (volume : Measure Domain3) s ≠ ∞) :
    IntegrableOn (mollifyRep K g) s (volume : Measure Domain3) :=
  Measure.integrableOn_of_bounded hμs (continuous_mollifyRep K g).aestronglyMeasurable
    (ae_of_all _ fun x => mollifyRep_apply_bound K g x)

/-- Coeff of the translate `τ_h g = compMeasurePreserving (·+h) g` is `g (x + h)` a.e.:
`(translate_L2VF h g) x = g (x + h)` for a.e. `x`. -/
private theorem coeFn_translate_L2VF (h : Domain3) (g : L2VF_R3) :
    (translate_L2VF h g : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume] fun x => (g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h) := by
  rw [translate_L2VF]
  exact Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right _ h)

/-- The inner integrand `y ↦ K.η (x − y) • g y` of `mollifyRep K g x` is Bochner integrable:
its norm `|K.η (x − y)| · ‖g y‖` is the product of two `L²` functions (Hölder, `p = q = 2`),
hence `L¹`. -/
private theorem integrable_kernel_translate_smul (K : MollifierKernel) (g : L2VF_R3) (x : Domain3) :
    Integrable (fun y : Domain3 => K.η (x - y) • (g : Domain3 → EuclideanSpace ℝ (Fin 3)) y)
      (volume : Measure Domain3) := by
  classical
  have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Domain3) x
  have hηx : MemLp (fun y : Domain3 => K.η (x - y)) 2 (volume : Measure Domain3) :=
    hηmem.comp_measurePreserving hmp
  have hgaesm : AEStronglyMeasurable (g : Domain3 → EuclideanSpace ℝ (Fin 3))
      (volume : Measure Domain3) := (Lp.memLp g).aestronglyMeasurable
  have haesm : AEStronglyMeasurable
      (fun y : Domain3 => K.η (x - y) • (g : Domain3 → EuclideanSpace ℝ (Fin 3)) y)
      (volume : Measure Domain3) := hηx.aestronglyMeasurable.smul hgaesm
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hnormint : Integrable (fun y : Domain3 => |K.η (x - y)|
      * ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) y‖) (volume : Measure Domain3) :=
    MemLp.integrable_mul (q := 2) hηx.abs ((Lp.memLp g).norm)
  refine ⟨haesm, ?_⟩
  refine hnormint.hasFiniteIntegral.congr' ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs]

/-- Joint a.e.-strong measurability of the sheared field `(x, h) ↦ g (x + h)` over the product
measure `(volume.restrict s).prod volume`: pull `g ∘ snd` back along the measure-preserving shear
`(x, h) ↦ (x, x + h)`, then transfer to the restricted product (absolutely continuous). -/
private theorem aesm_g_add (g : L2VF_R3) (s : Set Domain3) :
    AEStronglyMeasurable
      (fun z : Domain3 × Domain3 => (g : Domain3 → EuclideanSpace ℝ (Fin 3)) (z.1 + z.2))
      (((volume : Measure Domain3).restrict s).prod (volume : Measure Domain3)) := by
  have hgaesm : AEStronglyMeasurable (g : Domain3 → EuclideanSpace ℝ (Fin 3))
      (volume : Measure Domain3) := (Lp.memLp g).aestronglyMeasurable
  have hsnd : AEStronglyMeasurable
      (fun z : Domain3 × Domain3 => (g : Domain3 → EuclideanSpace ℝ (Fin 3)) z.2)
      ((volume : Measure Domain3).prod (volume : Measure Domain3)) := hgaesm.comp_snd
  have hshear := (measurePreserving_prod_add
    (volume : Measure Domain3) (volume : Measure Domain3)).quasiMeasurePreserving
  have hcomp : AEStronglyMeasurable
      (fun z : Domain3 × Domain3 => (g : Domain3 → EuclideanSpace ℝ (Fin 3)) (z.1 + z.2))
      ((volume : Measure Domain3).prod (volume : Measure Domain3)) :=
    hsnd.comp_quasiMeasurePreserving hshear
  exact hcomp.mono_ac
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      (Measure.AbsolutelyContinuous.refl _))

/-- **Joint integrability for the finite-set Fubini swap (PROVED).**  On a finite-measure
measurable set `s`, the integrand `F (x, h) = K.η h · ⟪c, g (x + h)⟫` is integrable for the
product measure `(volume.restrict s).prod volume`: each `h`-slice is integrable (kernel `× L²`,
Hölder) and `x ↦ ∫ h, ‖F (x, h)‖` is bounded by the constant `‖kernelL2R K‖ · ‖c‖ · ‖g‖`,
integrable on the finite set `s`.  This absolute convergence is exactly what makes Fubini
legitimate on `s` even though the raw `ℝ³ × ℝ³` double integral is not. -/
private theorem fubini_integrand_integrable (K : MollifierKernel) (g : L2VF_R3)
    {s : Set Domain3} (_hs : MeasurableSet s) (hμs : (volume : Measure Domain3) s ≠ ∞)
    (c : EuclideanSpace ℝ (Fin 3)) :
    Integrable
      (Function.uncurry fun x h : Domain3 => K.η h
        * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)))
      (((volume : Measure Domain3).restrict s).prod (volume : Measure Domain3)) := by
  classical
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hKaesm : AEStronglyMeasurable (fun z : Domain3 × Domain3 => K.η z.2)
      (((volume : Measure Domain3).restrict s).prod (volume : Measure Domain3)) :=
    (K.smooth.continuous.aestronglyMeasurable).comp_snd
  have hinner : AEStronglyMeasurable
      (fun z : Domain3 × Domain3 =>
        inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (z.1 + z.2)))
      (((volume : Measure Domain3).restrict s).prod (volume : Measure Domain3)) :=
    (continuous_const.inner continuous_id).comp_aestronglyMeasurable (aesm_g_add g s)
  have hF : AEStronglyMeasurable
      (Function.uncurry fun x h : Domain3 => K.η h
        * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)))
      (((volume : Measure Domain3).restrict s).prod (volume : Measure Domain3)) := by
    have heq : (Function.uncurry fun x h : Domain3 => K.η h
        * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)))
        = fun z : Domain3 × Domain3 => K.η z.2
            * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (z.1 + z.2)) := by
      funext z; rfl
    rw [heq]; exact hKaesm.mul hinner
  have hsliceMemLp : ∀ x : Domain3,
      MemLp (fun h : Domain3 => |K.η h|) 2 (volume : Measure Domain3) ∧
      MemLp (fun h : Domain3 => ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)‖) 2
        (volume : Measure Domain3) := by
    intro x
    have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
      K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
    have hmp := measurePreserving_add_left (volume : Measure Domain3) x
    exact ⟨hηmem.abs, ((Lp.memLp g).comp_measurePreserving hmp).norm⟩
  rw [integrable_prod_iff hF]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · obtain ⟨ha, hb⟩ := hsliceMemLp x
    have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
      K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
    have hmp := measurePreserving_add_left (volume : Measure Domain3) x
    have hgx : MemLp (fun h : Domain3 =>
        inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))) 2
        (volume : Measure Domain3) :=
      ((Lp.memLp g).comp_measurePreserving hmp).const_inner c
    have hint := MemLp.integrable_mul (q := 2) hηmem hgx
    rw [show (K.η * fun h : Domain3 => inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)))
        = (fun y : Domain3 => K.η y
            * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + y))) from rfl] at hint
    simpa only [Function.uncurry] using hint
  · set Φ : Domain3 → ℝ := fun x => ∫ h : Domain3,
      ‖Function.uncurry (fun x h : Domain3 => K.η h
        * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))) (x, h)‖
        ∂(volume : Measure Domain3) with hΦ
    have hΦaesm : AEStronglyMeasurable Φ ((volume : Measure Domain3).restrict s) :=
      hF.norm.integral_prod_right'
    have hΦbound : ∀ x : Domain3, ‖Φ x‖ ≤ ‖kernelL2R K‖ * ‖c‖ * ‖g‖ := by
      intro x
      obtain ⟨ha, hb⟩ := hsliceMemLp x
      have hmp := measurePreserving_add_left (volume : Measure Domain3) x
      have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
      rw [L2.inner_def] at hcs
      have hΦnn : 0 ≤ Φ x := integral_nonneg fun h => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hΦnn, hΦ]
      have hpt : ∀ h : Domain3,
          ‖Function.uncurry (fun x h : Domain3 => K.η h
            * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))) (x, h)‖
            ≤ |K.η h| * ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)‖ * ‖c‖ := by
        intro h
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        rw [mul_assoc]
        gcongr
        exact (abs_real_inner_le_norm c _).trans (by rw [mul_comm])
      have hintRHS : Integrable (fun h : Domain3 =>
          |K.η h| * ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)‖ * ‖c‖)
          (volume : Measure Domain3) :=
        ((MemLp.integrable_mul (q := 2) ha hb).mul_const ‖c‖)
      have hintLHS : Integrable (fun h : Domain3 =>
          ‖Function.uncurry (fun x h : Domain3 => K.η h
            * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))) (x, h)‖)
          (volume : Measure Domain3) := by
        have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
          K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
        have hgx : MemLp (fun h : Domain3 =>
            inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))) 2
            (volume : Measure Domain3) :=
          ((Lp.memLp g).comp_measurePreserving hmp).const_inner c
        exact ((MemLp.integrable_mul (q := 2) hηmem hgx).norm).congr
          (by filter_upwards with h using rfl)
      calc Φ x ≤ ∫ h : Domain3,
            |K.η h| * ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)‖ * ‖c‖
              ∂(volume : Measure Domain3) :=
            integral_mono_ae hintLHS hintRHS (Filter.Eventually.of_forall hpt)
        _ = (∫ h : Domain3, |K.η h| * ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)‖
              ∂(volume : Measure Domain3)) * ‖c‖ := by rw [integral_mul_const]
        _ = (∫ h : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) h)
              ((hb.toLp _ : Domain3 → ℝ) h)) ∂(volume : Measure Domain3)) * ‖c‖ := by
            congr 1
            refine integral_congr_ae ?_
            filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with h hah hbh
            simp only [RCLike.inner_apply, conj_trivial, hah, hbh]
            ring
        _ ≤ (‖ha.toLp _‖ * ‖hb.toLp _‖) * ‖c‖ := by
            gcongr
        _ = ‖kernelL2R K‖ * ‖c‖ * ‖g‖ := by
            have hna : ‖ha.toLp _‖ = ‖kernelL2R K‖ := by
              rw [kernelL2R, Lp.norm_toLp, Lp.norm_toLp]
              congr 1
              rw [show (fun h : Domain3 => |K.η h|) = (fun h : Domain3 => ‖K.η h‖) from
                  funext fun h => (Real.norm_eq_abs _).symm, eLpNorm_norm]
            have hnb : ‖hb.toLp _‖ = ‖g‖ := by
              rw [Lp.norm_toLp, Lp.norm_def, ← eLpNorm_norm
                (g : Domain3 → EuclideanSpace ℝ (Fin 3))]
              congr 1
              rw [show (fun h : Domain3 =>
                  ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)‖)
                  = (fun y : Domain3 => ‖(g : Domain3 → EuclideanSpace ℝ (Fin 3)) y‖)
                      ∘ (fun h : Domain3 => x + h) from rfl,
                eLpNorm_comp_measurePreserving
                  ((Lp.memLp g).aestronglyMeasurable.norm)
                  (measurePreserving_add_left (volume : Measure Domain3) x)]
            rw [hna, hnb]; ring
    exact ⟨hΦaesm, HasFiniteIntegral.restrict_of_bounded (‖kernelL2R K‖ * ‖c‖ * ‖g‖)
      hμs.lt_top (ae_of_all _ fun x => hΦbound x)⟩

/-- **LHS scalar reduction (PROVED).**  For any constant `c` and finite-measure measurable `s`,
the inner product of `c` with the set-integral of the `Lp`-valued Bochner integral `convL2 K g`
over `s` equals the iterated scalar integral
`∫ h, K.η h · (∫ x in s, ⟪c, g (x + h)⟫)`.  Commutes the inner product through the Bochner
integral via `integral_inner` and `inner_indicatorConstLp_eq_inner_setIntegral`. -/
private theorem convL2_setIntegral_inner (K : MollifierKernel) (g : L2VF_R3)
    {s : Set Domain3} (hs : MeasurableSet s) (hμs : (volume : Measure Domain3) s ≠ ∞)
    (c : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ c (∫ x in s, (convL2 K g : Domain3 → EuclideanSpace ℝ (Fin 3)) x
        ∂(volume : Measure Domain3)))
      = ∫ h : Domain3, K.η h
          * (∫ x in s, inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))
              ∂(volume : Measure Domain3)) ∂(volume : Measure Domain3) := by
  classical
  set w : L2VF_R3 := indicatorConstLp 2 hs hμs c with hw
  have hpair : inner ℝ c (∫ x in s, (convL2 K g : Domain3 → EuclideanSpace ℝ (Fin 3)) x
        ∂(volume : Measure Domain3)) = inner ℝ w (convL2 K g) :=
    (L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hs hμs c (convL2 K g)).symm
  rw [hpair, convL2]
  rw [← integral_inner (integrable_kernel_smul_translate K g) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [real_inner_smul_right]
  congr 1
  rw [show (inner ℝ w (translate_L2VF h g) : ℝ)
      = inner ℝ (indicatorConstLp 2 hs hμs c) (translate_L2VF h g) from rfl,
    L2.inner_indicatorConstLp_eq_setIntegral_inner (𝕜 := ℝ) (translate_L2VF h g) hs c hμs]
  refine setIntegral_congr_ae hs ((coeFn_translate_L2VF h g).mono fun x hx _ => ?_)
  rw [hx]

/-- **RHS scalar reduction (PROVED).**  For any constant `c` and finite-measure measurable `s`,
the inner product of `c` with the set-integral of the pointwise convolution `mollifyRep K g`
over `s` equals the iterated scalar integral
`∫ x in s, ∫ h, K.η h · ⟪c, g (x + h)⟫`.  Uses `integral_inner` on the inner `∫ y` integral,
the translation substitution `y ↦ x + h`, and `K.even`. -/
private theorem mollifyRep_setIntegral_inner (K : MollifierKernel) (g : L2VF_R3)
    {s : Set Domain3} (hs : MeasurableSet s) (hμs : (volume : Measure Domain3) s ≠ ∞)
    (c : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ c (∫ x in s, mollifyRep K g x ∂(volume : Measure Domain3)))
      = ∫ x in s, (∫ h : Domain3, K.η h
          * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))
            ∂(volume : Measure Domain3)) ∂(volume : Measure Domain3) := by
  classical
  rw [← integral_inner (integrableOn_mollifyRep K g hμs) c]
  refine setIntegral_congr_ae hs (Filter.Eventually.of_forall fun x _ => ?_)
  rw [mollifyRep]
  rw [← integral_inner (integrable_kernel_translate_smul K g x) c]
  rw [show (∫ y : Domain3, inner ℝ c (K.η (x - y) • (g : Domain3 → EuclideanSpace ℝ (Fin 3)) y)
        ∂(volume : Measure Domain3))
      = ∫ h : Domain3, inner ℝ c (K.η (x - (x + h))
          • (g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h)) ∂(volume : Measure Domain3) from
    (integral_add_left_eq_self
      (fun y => inner ℝ c (K.η (x - y) • (g : Domain3 → EuclideanSpace ℝ (Fin 3)) y)) x).symm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [real_inner_smul_right, show x - (x + h) = -h by abel, K.even]

/-- **The isolated coeFn identity — now PROVED (no `sorry`, no axiom).**

The coeFn of the `Lp`-valued Bochner integral `convL2 K g = ∫ h, K.η h • τ_h g` agrees a.e. with
the pointwise convolution `mollifyRep K g x = ∫ y, K.η (x − y) • g y`.

mathlib provides **no** "coeFn of an `Lp`-valued Bochner integral as the scalar integral of
coeFns" lemma for this `volume`-on-ℝ³ vector-valued setting, and the raw double integral is NOT
absolutely convergent on `ℝ³ × ℝ³` (`φ, g ∈ L²` are not `L¹`), so a naive global scalar Fubini is
unavailable.  The honest provable route, carried out here:

* both `convL2 K g` (an `Lp` element) and `mollifyRep K g` (continuous, globally bounded by
  `mollifyRep_apply_bound`, hence `integrableOn_mollifyRep`) are integrable on every finite-measure
  set, so `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` reduces the goal to
  `∫_s convL2 K g = ∫_s mollifyRep K g` for all finite measurable `s`;
* equality of two `EuclideanSpace ℝ (Fin 3)` vectors is tested by `ext_inner_left`: it suffices to
  show `⟪c, ∫_s convL2 K g⟫ = ⟪c, ∫_s mollifyRep K g⟫` for every `c`;
* `convL2_setIntegral_inner` rewrites the LHS to `∫ h, K.η h · ∫ x in s, ⟪c, g (x+h)⟫` and
  `mollifyRep_setIntegral_inner` rewrites the RHS to `∫ x in s, ∫ h, K.η h · ⟪c, g (x+h)⟫`;
* on the FINITE set `s` the double integral of `F (x,h) = K.η h · ⟪c, g (x+h)⟫` is absolutely
  convergent (`fubini_integrand_integrable`), so `integral_integral_swap` (Fubini over
  `(volume.restrict s).prod volume`) exchanges the two orders. -/
private theorem convL2_coeFn_ae (K : MollifierKernel) (g : L2VF_R3) :
    (convL2 K g : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume] mollifyRep K g := by
  classical
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hμs => integrableOn_Lp_of_measure_ne_top (convL2 K g) (by norm_num) hμs.ne)
    (fun s _ hμs => integrableOn_mollifyRep K g hμs.ne)
    (fun s hs hμs => ?_)
  refine ext_inner_left ℝ (fun c => ?_)
  rw [convL2_setIntegral_inner K g hs hμs.ne c, mollifyRep_setIntegral_inner K g hs hμs.ne c]
  -- Pull `K.η h` out of the inner set-integral, then Fubini-swap.
  rw [show (∫ h : Domain3, K.η h
        * (∫ x in s, inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))
            ∂(volume : Measure Domain3)) ∂(volume : Measure Domain3))
      = ∫ h : Domain3, (∫ x in s, K.η h
          * inner ℝ c ((g : Domain3 → EuclideanSpace ℝ (Fin 3)) (x + h))
            ∂(volume : Measure Domain3)) ∂(volume : Measure Domain3) from
    integral_congr_ae (Filter.Eventually.of_forall fun h => (integral_const_mul _ _).symm)]
  exact (integral_integral_swap (fubini_integrand_integrable K g hs hμs.ne c)).symm

/-- `mollifyRep K g`, as an a.e. function, lies in `L²`: it agrees a.e. with `convL2 K g`. -/
private theorem memLp_mollifyRep (K : MollifierKernel) (g : L2VF_R3) :
    MemLp (mollifyRep K g) 2 (volume : Measure Domain3) :=
  (Lp.memLp (convL2 K g)).ae_eq (convL2_coeFn_ae K g)

/-- **Shared primitive.**  The `L²`-class of `mollifyRep K g` equals the `Lp`-valued Bochner
integral `convL2 K g = ∫ h, K.η h • τ_h g`.  Proved (no sorry) from the isolated coeFn identity
`convL2_coeFn_ae` by `Lp.ext`. -/
private theorem mollifyRep_eq_lp_integral (K : MollifierKernel) (g : L2VF_R3)
    (hmem : MemLp (mollifyRep K g) 2 (volume : Measure Domain3)) :
    hmem.toLp = ∫ h : Domain3, K.η h • translate_L2VF h g ∂(volume : Measure Domain3) := by
  show hmem.toLp = convL2 K g
  apply Lp.ext
  refine (MemLp.coeFn_toLp hmem).trans ?_
  exact (convL2_coeFn_ae K g).symm

/-- **Analytic core — global Young convolution inequality in `L²`.**

The mollified field `mollifyRep K g = K.η ⋆ g` lies in `L²(ℝ³)` globally, with
`‖mollifyRep K g‖_{L²} ≤ ‖kernelL1R K‖ · ‖g‖`.  The `MemLp` witness is bundled with the bound on its
`toLp` class so callers can both form `(mollifyRep K g : L2VF_R3)` and control its norm. -/
theorem young_convolution_memLp_L2 (K : MollifierKernel) (g : L2VF_R3) :
    ∃ hmem : MemLp (mollifyRep K g) 2 (volume : Measure Domain3),
      ‖hmem.toLp‖ ≤ ‖kernelL1R K‖ * ‖g‖ := by
  -- PROVED (the coeFn frontier `convL2_coeFn_ae` is now discharged).  The `MemLp` witness comes from
  -- `mollifyRep K g =ᵐ convL2 K g` (an honest `Lp` element); the norm bound is `convL2_norm_le`
  -- (the entire Young content) plus `‖kernelL1R K‖ = 1`.
  refine ⟨memLp_mollifyRep K g, ?_⟩
  have heq : (memLp_mollifyRep K g).toLp = convL2 K g :=
    mollifyRep_eq_lp_integral K g (memLp_mollifyRep K g)
  rw [heq, norm_kernelL1R, one_mul]
  exact convL2_norm_le K g

/-- **Analytic core — vector Minkowski form of the convolution approximation rate.**

`(K.η ⋆ g) − g = ∫ h, K.η h · (τ_h g − g) dh` for a mass-one kernel, so by the vector-valued
Minkowski integral inequality `‖∫ F(h) dh‖₂ ≤ ∫ ‖F(h)‖₂ dh` the `L²`-defect of the mollification is
controlled by the kernel-weighted integral of the translation modulus:

  `‖toLp(mollifyRep K g) − g‖ ≤ ∫ h, K.η h • ‖translate_L2VF h g − g‖ ∂volume`.

Composed with `K.supportRadius < δ` (so the integration variable `h` ranges over `‖h‖ < δ` on the
kernel support) and the FK uniform translation modulus, this delivers the uniform `< ε` rate. -/
theorem convolution_sub_L2_le_translation_modulus (K : MollifierKernel) (g : L2VF_R3)
    (hmem : MemLp (mollifyRep K g) 2 (volume : Measure Domain3)) :
    ‖hmem.toLp - g‖
      ≤ ∫ h : Domain3, K.η h • ‖translate_L2VF h g - g‖ ∂(volume : Measure Domain3) := by
  -- PROVED (the coeFn frontier `convL2_coeFn_ae` is now discharged; consumed via the primitive).
  -- `hmem.toLp = convL2 K g = ∫ h, K.η h • τ_h g`, and `g = ∫ h, K.η h • g` (`K.mass_one`), so the
  -- defect is the single Bochner integral `∫ h, K.η h • (τ_h g − g)`; `‖∫ F‖ ≤ ∫ ‖F‖` plus
  -- `‖K.η h • v‖ = K.η h · ‖v‖` (`K.nonneg`) gives the modulus bound, with the kernel weight `K.η h`
  -- (not `|K.η h|`) since `K.nonneg`.
  classical
  have hI1 : Integrable (fun h : Domain3 => K.η h • translate_L2VF h g)
      (volume : Measure Domain3) := integrable_kernel_smul_translate K g
  have hηL1 : Integrable K.η (volume : Measure Domain3) :=
    memLp_one_iff_integrable.mp
      (K.smooth.continuous.memLp_of_hasCompactSupport (p := 1) (μ := volume) K.hasCompactSupport)
  have hI2 : Integrable (fun h : Domain3 => K.η h • g) (volume : Measure Domain3) :=
    hηL1.smul_const g
  have hg_int : (∫ h : Domain3, K.η h • g ∂(volume : Measure Domain3)) = g := by
    rw [integral_smul_const, K.mass_one, one_smul]
  have hdefect : hmem.toLp - g
      = ∫ h : Domain3, K.η h • (translate_L2VF h g - g) ∂(volume : Measure Domain3) := by
    have e1 : hmem.toLp - g
        = (∫ h : Domain3, K.η h • translate_L2VF h g ∂(volume : Measure Domain3))
          - ∫ h : Domain3, K.η h • g ∂(volume : Measure Domain3) := by
      rw [mollifyRep_eq_lp_integral K g hmem, hg_int]
    rw [e1, ← integral_sub hI1 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [smul_sub]
  rw [hdefect]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only []
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (K.nonneg h), smul_eq_mul]

/-! ### FK step 1 — equiboundedness + equicontinuity of the mollified family -/

/-- **FK step 1 (equiboundedness).**  The CONCRETE mollified family has a uniform sup bound on
its explicit representative.

For a fixed smooth compactly supported kernel `K`, convolving an L²-bounded family with `K.η`
gives a family with a common `L^∞`-bound via Young's inequality
`‖η ⋆ g‖_∞ ≤ ‖η‖₂ · ‖g‖₂` (the kernel is in `L²` because it is continuous with compact support).
The bound is stated for the genuine representative `mollifyRep K (rep f)`, NOT for the pointwise
evaluation of an arbitrary `Lp`-class.

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  Young's inequality bounds
`‖η ⋆ g‖_∞` by `‖η‖₂‖g‖₂`.  The OUTPUT bound is needed only on `x ∈ B_R` (the region the
ball-restriction of `mollifyRep` keeps), and there `mollifyRep K (rep f) x = ∫ y, η(x−y)·rep f(y)`
only sees `rep f` over the kernel-reach `B_{R + K.supportRadius}` (since `η` is supported in
`closedBall 0 K.supportRadius`).  Hence the local hypothesis is the ENLARGED-BALL bound
`hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C`
on the kernel-support enlargement `B_{R+r}` — exactly what Young needs on `B_R`.  This bound is
supplied at the call site directly from `FrechetKolmogorovInput`'s GLOBAL bound
`hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity (`‖restrictToBall (R+r) g‖ ≤ ‖g‖`), so
there is no longer any upstream gap: the criterion's own strengthened data furnishes it.  The
output bound is stated for `x ∈ B_R` only. -/
theorem mollified_family_uniformly_bounded (R C : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3) (K : MollifierKernel)
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C) :
    ∃ B : ℝ, ∀ f ∈ S, ∀ x : Domain3, x ∈ Metric.closedBall (0 : Domain3) R →
        ‖mollifyRep K (rep f) x‖ ≤ B := by
  -- Uniform sup-bound `B := ‖kernelL2R K‖ · C`: each pointwise value is bounded by the kernel
  -- L²-norm times the enlarged-ball mass (`mollifyRep_sup_le`), which is ≤ C by `hbdEnl`.
  refine ⟨‖kernelL2R K‖ * C, fun f hf x hx => ?_⟩
  calc ‖mollifyRep K (rep f) x‖
      ≤ ‖kernelL2R K‖ * ‖restrictToBall (R + K.supportRadius) (rep f)‖ :=
        mollifyRep_sup_le K (rep f) R hx
    _ ≤ ‖kernelL2R K‖ * C :=
        mul_le_mul_of_nonneg_left (hbdEnl f hf) (norm_nonneg _)

/-- **FK step 1 (equicontinuity).**  The CONCRETE mollified family is uniformly equicontinuous on
its explicit representative.

For a fixed smooth compactly supported kernel `K`, the modulus of continuity of `η ⋆ g` is
controlled by `‖g‖₂` times the (kernel-only) modulus of `η`
(`‖(η ⋆ g)(x) − (η ⋆ g)(y)‖ ≤ ‖g‖₂ · ‖τ_{x−y} η − η‖₂`), uniformly over the L²-bounded family —
because `K.η`, being smooth with compact support, is uniformly continuous with an L²-modulus
independent of `g`.  Stated for `mollifyRep K (rep f)`, NOT for an arbitrary operator.

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  Restricting attention to
`x, y ∈ B_R` (the region the ball-restriction keeps) and bounding the difference quotient by the
kernel modulus localizes the mass factor `‖g‖₂` to the kernel-reach `B_{R + K.supportRadius}`:
the relevant inequality is
`‖(η⋆g)(x)−(η⋆g)(y)‖ ≤ ‖restrictToBall (R+K.supportRadius) g‖ · ‖τ_{x−y}K.η − K.η‖₂` for
`x, y ∈ B_R`.  Hence the local hypothesis is the ENLARGED-BALL bound `hbdEnl` on `B_{R+r}`, which
the call site supplies from `FrechetKolmogorovInput`'s GLOBAL bound `hbddGlobal : ‖rep f‖ ≤ C`
by ball-mass monotonicity (no upstream gap).  The equicontinuity conclusion is stated for
`x, y ∈ B_R` only. -/
theorem mollified_family_equicontinuous (R C : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3) (K : MollifierKernel)
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C) :
    ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ x y : Domain3,
      x ∈ Metric.closedBall (0 : Domain3) R → y ∈ Metric.closedBall (0 : Domain3) R →
      ‖x - y‖ < δ →
      ‖mollifyRep K (rep f) x - mollifyRep K (rep f) y‖ < ε := by
  -- ε→δ via the kernel's L²-translation modulus `kernel_translate_L2_tendsto`, scaled by the
  -- uniform enlarged-ball mass (≤ |C|+1).  The increment is bounded by
  -- (enlarged mass)·(kernel modulus) via `mollifyRep_sub_le`.
  intro ε hε
  -- Uniform mass bound `M := |C| + 1 > 0`, so it can divide ε.
  set M : ℝ := |C| + 1 with hM
  have hMpos : 0 < M := by positivity
  -- The kernel modulus `m h := ‖τ_h kernel − kernel‖ → 0` as `h → 0`; choose δ making it < ε/M.
  have htend := kernel_translate_L2_tendsto K
  have hpos : 0 < ε / M := div_pos hε hMpos
  -- Pull back the `< ε/M` neighborhood of `0 ∈ ℝ` along the modulus to a `0`-neighborhood in
  -- `Domain3`, then extract a metric radius δ.
  have hball : {z : ℝ | z < ε / M} ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds (isOpen_Iio) (by simpa using hpos)
  have hpre : (fun h : Domain3 => ‖translate_L2R h (kernelL2R K) - kernelL2R K‖) ⁻¹'
      {z : ℝ | z < ε / M} ∈ 𝓝 (0 : Domain3) := htend hball
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨δ, hδpos, hδsub⟩ := hpre
  refine ⟨δ, hδpos, fun f hf x y hx hy hxy => ?_⟩
  -- The shift `x − y` lies in the δ-ball around 0, so the kernel modulus there is `< ε/M`.
  have hmem : (x - y) ∈ Metric.ball (0 : Domain3) δ := by
    simp only [Metric.mem_ball, dist_zero_right]
    simpa using hxy
  have hmod_lt : ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ < ε / M := hδsub hmem
  have hmod_nonneg : 0 ≤ ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ := norm_nonneg _
  -- Enlarged-ball mass ≤ C ≤ |C| < M.
  have hmass : ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ M :=
    le_trans (hbdEnl f hf) (by rw [hM]; linarith [le_abs_self C])
  have hmass_nonneg : 0 ≤ ‖restrictToBall (R + K.supportRadius) (rep f)‖ := norm_nonneg _
  -- Combine: increment ≤ mass · modulus ≤ M · (ε/M) = ε  (strict because modulus < ε/M, M > 0).
  calc ‖mollifyRep K (rep f) x - mollifyRep K (rep f) y‖
      ≤ ‖restrictToBall (R + K.supportRadius) (rep f)‖
          * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ :=
        mollifyRep_sub_le K (rep f) R hx hy
    _ ≤ M * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ :=
        mul_le_mul_of_nonneg_right hmass hmod_nonneg
    _ < M * (ε / M) := by
        exact mul_lt_mul_of_pos_left hmod_lt hMpos
    _ = ε := by field_simp

/-- The volume of the closed ball `B_R ⊆ ℝ³` is finite (it is compact in a proper space), so the
restricted measure `volume.restrict B_R` is a finite measure: needed to invoke
`Lp.norm_le_of_ae_bound` for the sup→L² transfer. -/
instance isFiniteMeasure_volume_restrict_closedBall (R : ℝ) :
    IsFiniteMeasure ((volume : Measure Domain3).restrict (Metric.closedBall (0 : Domain3) R)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (isCompact_closedBall (0 : Domain3) R).measure_lt_top

/-- The "ball mass factor" `V_R := (volume B_R)^{1/2}` controlling the sup→L²(B_R) transfer. -/
noncomputable def ballMassSqrt (R : ℝ) : ℝ :=
  (measureUnivNNReal ((volume : Measure Domain3).restrict
    (Metric.closedBall (0 : Domain3) R)) : ℝ) ^ ((2 : ℝ)⁻¹)

/-- The ball-mass factor `ballMassSqrt R` is nonnegative, as a square root of a measure. -/
theorem ballMassSqrt_nonneg (R : ℝ) : 0 ≤ ballMassSqrt R := by
  unfold ballMassSqrt
  positivity

/-- **Sup→L²(B_R) transfer.**  If two L²(ℝ³) fields `u, v` agree a.e. on `B_R` with functions
whose pointwise difference is `≤ c` everywhere on `B_R`, then their ball-restrictions are within
`ballMassSqrt R · c` in `L²(B_R)`. -/
theorem dist_restrictToBall_le_of_ae_bound (R c : ℝ) (hc : 0 ≤ c) (u v : L2VF_R3)
    (g₁ g₂ : Domain3 → EuclideanSpace ℝ (Fin 3))
    (hu : (u : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[(volume : Measure Domain3).restrict (Metric.closedBall (0 : Domain3) R)] g₁)
    (hv : (v : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[(volume : Measure Domain3).restrict (Metric.closedBall (0 : Domain3) R)] g₂)
    (hbound : ∀ x ∈ Metric.closedBall (0 : Domain3) R, ‖g₁ x - g₂ x‖ ≤ c) :
    dist (restrictToBall R u) (restrictToBall R v) ≤ ballMassSqrt R * c := by
  set μ : Measure Domain3 := (volume : Measure Domain3).restrict
    (Metric.closedBall (0 : Domain3) R) with hμ
  rw [dist_eq_norm]
  -- coeFn of the difference of restrictions agrees a.e. with `g₁ - g₂` on `μ`.
  have hru : (restrictToBall R u : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[μ] u :=
    MemLp.coeFn_toLp _
  have hrv : (restrictToBall R v : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[μ] v :=
    MemLp.coeFn_toLp _
  have hsub := Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v)
  have haediff : ((restrictToBall R u - restrictToBall R v : L2ballR3 R) :
        Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[μ] fun x => g₁ x - g₂ x := by
    filter_upwards [hsub, hru, hrv, hu, hv] with x hxs hxu hxv hxg1 hxg2
    simp only [hxs, Pi.sub_apply, hxu, hxv, hxg1, hxg2]
  -- a.e. norm bound `≤ c` on `μ` (`μ` lives on `B_R`).
  have haebd : ∀ᵐ x ∂μ,
      ‖((restrictToBall R u - restrictToBall R v : L2ballR3 R) :
        Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ ≤ c := by
    have hmem : ∀ᵐ x ∂μ, x ∈ Metric.closedBall (0 : Domain3) R := by
      rw [hμ]
      exact ae_restrict_mem measurableSet_closedBall
    filter_upwards [haediff, hmem] with x hx hxmem
    rw [hx]
    exact hbound x hxmem
  -- `Lp.norm_le_of_ae_bound` (finite measure) gives the bound with `measureUnivNNReal^{1/2}`.
  have hb := Lp.norm_le_of_ae_bound (μ := μ) (p := 2)
    (f := (restrictToBall R u - restrictToBall R v : L2ballR3 R)) hc haebd
  simpa [ballMassSqrt, hμ, ENNReal.toReal_ofNat] using hb

/-! ### FK step 2 — Arzelà–Ascoli ⇒ total boundedness in L²(ball) -/

/-- **Textbook step (sup→L² tolerance).**  For a mass factor `V ≥ 0` and a target `ε > 0`,

  `V · (ε / (2 (V + 1))) < ε`.

It is applied by fixing the mass `V` first and only then choosing the sup-level tolerance
`ε' = ε / (2 (V + 1))`, so that multiplying by `V` still cannot eat the target.  Note that `ε'`
genuinely depends on `V`, so it can only be chosen once the ball mass has been bounded.

The `+1` in the denominator does two things: it keeps the denominator from degenerating at
`V = 0`, and it makes the mass factor bounded by the denominator, `V ≤ V + 1`.  The proof uses
exactly that non-strict step to reach

  `V · (ε / (2 (V + 1))) ≤ ε / 2`,

and then concludes `< ε`.  The sharper strict bound `< ε / 2` is also true, since
`V / (V + 1) < 1` for every `V ≥ 0`, but it is neither what the statement claims nor what the
proof establishes. -/
private theorem mul_div_two_mul_add_one_lt (V ε : ℝ) (hV : 0 ≤ V) (hε : 0 < ε) :
    V * (ε / (2 * (V + 1))) < ε := by
  have hVp1 : 0 < V + 1 := by positivity
  rw [div_eq_mul_inv, ← mul_assoc]
  calc V * ε * (2 * (V + 1))⁻¹ ≤ (V + 1) * ε * (2 * (V + 1))⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) hε.le
    _ = ε * ((V + 1) * (2 * (V + 1))⁻¹) := by ring
    _ = ε * (2⁻¹) := by
        rw [show (2 * (V + 1))⁻¹ = 2⁻¹ * (V + 1)⁻¹ by rw [mul_inv]]
        rw [show (V + 1) * (2⁻¹ * (V + 1)⁻¹) = 2⁻¹ * ((V + 1) * (V + 1)⁻¹) by ring,
          mul_inv_cancel₀ hVp1.ne', mul_one]
    _ < ε := by nlinarith [hε]

/-- **Textbook step (Arzelà–Ascoli net estimate).**  Two points that are each within `η` of their
respective anchors `p'`, `q'`, whose anchors are both within `γ` of a common net value `w`, are
within `η + 2γ + η` of each other.

This is the classification step of the Arzelà–Ascoli net construction, stated for its own sake:
`p = Φ f x`, `p' = Φ f c`, `q = Φ g x`, `q' = Φ g c` and `w` the shared value-net point at the
center `c`, so equicontinuity supplies the two `η`-bounds and membership in the same class
supplies the two `γ`-bounds. -/
private theorem norm_sub_lt_of_center_net {E : Type*} [NormedAddCommGroup E]
    {p p' q q' w : E} {η γ : ℝ}
    (hp : ‖p - p'‖ < η) (hq : ‖q' - q‖ < η)
    (hpw : dist p' w < γ) (hqw : dist q' w < γ) :
    ‖p - q‖ < η + 2 * γ + η := by
  have hmid : ‖p' - q'‖ < 2 * γ := by
    have h1 : dist p' q' ≤ dist p' w + dist w q' := dist_triangle _ _ _
    have hqw' : dist w q' < γ := by rw [dist_comm]; exact hqw
    have hlt : dist p' q' < 2 * γ := by
      have := lt_of_le_of_lt h1 (add_lt_add hpw hqw')
      linarith [this]
    rwa [dist_eq_norm] at hlt
  have htri : ‖p - q‖ ≤ ‖p - p'‖ + ‖p' - q'‖ + ‖q' - q‖ := by
    have e1 : p - q = (p - p') + (p' - q') + (q' - q) := by abel
    rw [e1]; exact norm_add₃_le
  exact lt_of_le_of_lt htri (add_lt_add (add_lt_add hp hmid) hq)

set_option maxHeartbeats 1600000 in
-- kept at the original 1600000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported only ~1629 heartbeats, but a real sequential build with the override removed
-- times out at `whnf` under the 200000 default — the isolated figure undercounts this
-- declaration's true cost, so no further reduction attempted here.
/-- **Abstract Arzelà–Ascoli + sup→L² transfer.**  Let `Φ f` be a representative function for the
L²(B_R)-class `restrictToBall R (ρf f)` (`hΦae`).  If the family `{Φ f : f ∈ S}` is uniformly
bounded (`hB`) and uniformly equicontinuous (`hequi`) on the compact ball `B_R`, then the image
`{restrictToBall R (ρf f) : f ∈ S}` is totally bounded in `L²(B_R)`.

The proof is the classical Arzelà–Ascoli net construction: a finite `δ`-net of centers in the
compact `B_R` (with `δ` from equicontinuity), a finite value-net of the bounded range, classify
each `f` by the tuple of nearest value-net points at the centers, choose one representative per
class; equicontinuity plus the value-net make functions in the same class uniformly close on
`B_R`, and `dist_restrictToBall_le_of_ae_bound` (finite-measure sup→L² bound) turns that into
L²(B_R)-closeness. -/
theorem totallyBounded_image_of_equicont_bdd (R : ℝ) (S : Set (L2ballR3 R))
    (ρf : L2ballR3 R → L2VF_R3)
    (Φ : L2ballR3 R → Domain3 → EuclideanSpace ℝ (Fin 3))
    (hΦae : ∀ f ∈ S, (ρf f : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume] Φ f)
    (B : ℝ)
    (hB : ∀ f ∈ S, ∀ x : Domain3, x ∈ Metric.closedBall (0 : Domain3) R → ‖Φ f x‖ ≤ B)
    (hequi : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ x y : Domain3,
      x ∈ Metric.closedBall (0 : Domain3) R → y ∈ Metric.closedBall (0 : Domain3) R →
      ‖x - y‖ < δ → ‖Φ f x - Φ f y‖ < ε) :
    TotallyBounded ((fun f => restrictToBall R (ρf f)) '' S) := by
  classical
  set ball₀ : Set Domain3 := Metric.closedBall (0 : Domain3) R with hball₀
  -- Mass factor for the sup→L² transfer.
  set V : ℝ := ballMassSqrt R with hV
  have hVnn : 0 ≤ V := ballMassSqrt_nonneg R
  rw [Metric.totallyBounded_iff]
  intro ε hε
  rcases S.eq_empty_or_nonempty with hSempty | hSne
  · exact ⟨∅, Set.finite_empty, by simp [hSempty]⟩
  haveI : Nonempty ↥S := hSne.to_subtype
  -- Sup-level tolerance `ε'` with `V · ε' < ε`.
  set ε' : ℝ := ε / (2 * (V + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hVε' : V * ε' < ε := by
    rw [hε']; exact mul_div_two_mul_add_one_lt V ε hVnn hε
  -- Per-point tolerances: equicontinuity `ηeq` + value-net `γ`, with `2ηeq + 2γ ≤ ε'`.
  set ηeq : ℝ := ε' / 8 with hηeq
  have hηpos : 0 < ηeq := by positivity
  obtain ⟨δ, hδpos, hδ⟩ := hequi ηeq hηpos
  -- Finite δ-net of the compact ball `B_R`, with centers IN `B_R`.
  obtain ⟨cs, hcs_sub, hcs_fin, hcs_cover⟩ :=
    (isCompact_closedBall (0 : Domain3) R).finite_cover_balls hδpos
  -- Finite γ-net of the value-ball `closedBall 0 B'` (`B' = max B 0 ≥ 0`).
  set B' : ℝ := max B 0 with hB'
  have hB'nn : 0 ≤ B' := le_max_right _ _
  set γ : ℝ := ε' / 8 with hγ
  have hγpos : 0 < γ := by positivity
  obtain ⟨vs, hvs_sub, hvs_fin, hvs_cover⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) B').finite_cover_balls hγpos
  set cF : Finset Domain3 := hcs_fin.toFinset with hcF
  set vF : Finset (EuclideanSpace ℝ (Fin 3)) := hvs_fin.toFinset with hvF
  have hval_near : ∀ f ∈ S, ∀ c ∈ cF, ∃ w ∈ vs, dist (Φ f c) w < γ := by
    intro f hf c hc
    have hc_mem : c ∈ ball₀ := hcs_sub (by simpa [hcF, hcs_fin.mem_toFinset] using hc)
    have hΦbd : ‖Φ f c‖ ≤ B := hB f hf c hc_mem
    have hmem : Φ f c ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) B' := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_trans hΦbd (le_max_left _ _)
    have := hvs_cover hmem
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  set classify : ↥S → (↥cF → ↥vF) := fun f c =>
    ⟨Classical.choose (hval_near f.1 f.2 c.1 c.2),
      (hvs_fin.mem_toFinset).2 (Classical.choose_spec (hval_near f.1 f.2 c.1 c.2)).1⟩
    with hclassify
  have hclassify_spec : ∀ (f : ↥S) (c : ↥cF),
      dist (Φ f.1 c.1) (classify f c : EuclideanSpace ℝ (Fin 3)) < γ := by
    intro f c
    exact (Classical.choose_spec (hval_near f.1 f.2 c.1 c.2)).2
  have hrep_exists : ∀ b : ↥(Set.range classify), ∃ f : ↥S, classify f = b.1 := by
    intro b; exact b.2
  set chooseRep : ↥(Set.range classify) → ↥S := fun b => Classical.choose (hrep_exists b)
    with hchooseRep
  have hchooseRep_spec : ∀ b : ↥(Set.range classify), classify (chooseRep b) = b.1 :=
    fun b => Classical.choose_spec (hrep_exists b)
  set T : Set (L2ballR3 R) :=
    (fun f : ↥S => restrictToBall R (ρf (f : L2ballR3 R))) '' (Set.range chooseRep)
    with hT
  refine ⟨T, ?_, ?_⟩
  · exact (Set.finite_range chooseRep).image _
  rintro _ ⟨f, hf, rfl⟩
  set fS : ↥S := ⟨f, hf⟩ with hfS
  set b : ↥cF → ↥vF := classify fS with hb
  have hb_mem : b ∈ Set.range classify := ⟨fS, rfl⟩
  set g : ↥S := chooseRep ⟨b, hb_mem⟩ with hg
  have hgclass : classify g = b := hchooseRep_spec ⟨b, hb_mem⟩
  refine Set.mem_iUnion.2 ⟨restrictToBall R (ρf (g : L2ballR3 R)), ?_⟩
  refine Set.mem_iUnion.2 ⟨?_, ?_⟩
  · exact ⟨g, ⟨⟨b, hb_mem⟩, rfl⟩, rfl⟩
  rw [Metric.mem_ball, dist_comm]
  have hptwise : ∀ x ∈ ball₀, ‖Φ (f) x - Φ (g : L2ballR3 R) x‖ ≤ ε' := by
    intro x hx
    have hxcov := hcs_cover hx
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hxcov
    obtain ⟨c, hc_cs, hxc⟩ := hxcov
    have hc_cF : c ∈ cF := by simpa [hcF, hcs_fin.mem_toFinset] using hc_cs
    have hc_ball : c ∈ ball₀ := hcs_sub hc_cs
    set cS : ↥cF := ⟨c, hc_cF⟩ with hcS
    have hxc' : ‖x - c‖ < δ := by
      simpa [dist_eq_norm] using hxc
    have heq_f : ‖Φ f x - Φ f c‖ < ηeq := hδ f hf x c hx hc_ball hxc'
    have heq_g : ‖Φ (g : L2ballR3 R) x - Φ (g : L2ballR3 R) c‖ < ηeq :=
      hδ (g : L2ballR3 R) g.2 x c hx hc_ball hxc'
    have hbf : dist (Φ f c) (b cS : EuclideanSpace ℝ (Fin 3)) < γ := by
      have := hclassify_spec fS cS; simpa [hb, hcS, hfS] using this
    have hbg : dist (Φ (g : L2ballR3 R) c) (b cS : EuclideanSpace ℝ (Fin 3)) < γ := by
      have hgc := hclassify_spec g cS
      rw [hgclass] at hgc
      simpa [hcS] using hgc
    have heq_g' : ‖Φ (g : L2ballR3 R) c - Φ (g : L2ballR3 R) x‖ < ηeq := by
      rw [show Φ (g : L2ballR3 R) c - Φ (g : L2ballR3 R) x
          = -(Φ (g : L2ballR3 R) x - Φ (g : L2ballR3 R) c) by abel, norm_neg]
      exact heq_g
    have hsum : ηeq + 2 * γ + ηeq ≤ ε' := by rw [hηeq, hγ]; linarith
    -- both `Φ f` and `Φ g` sit within `γ` of the SAME net value `b cS` at the center `c`.
    have hlt : ‖Φ f x - Φ (g : L2ballR3 R) x‖ < ηeq + 2 * γ + ηeq :=
      norm_sub_lt_of_center_net heq_f heq_g' hbf hbg
    linarith [hlt, hsum]
  have hdist : dist (restrictToBall R (ρf (g : L2ballR3 R))) (restrictToBall R (ρf f))
      ≤ V * ε' := by
    have hd := dist_restrictToBall_le_of_ae_bound R ε' hε'pos.le
      (ρf (g : L2ballR3 R)) (ρf f) (Φ (g : L2ballR3 R)) (Φ f)
      ((hΦae (g : L2ballR3 R) g.2).restrict) ((hΦae f hf).restrict)
      (fun x hx => by
        have hpx := hptwise x hx
        rw [show Φ (g : L2ballR3 R) x - Φ f x = -(Φ f x - Φ (g : L2ballR3 R) x) by abel, norm_neg]
        exact hpx)
    simpa [hV] using hd
  calc dist (restrictToBall R (ρf (g : L2ballR3 R))) (restrictToBall R (ρf f))
      ≤ V * ε' := hdist
    _ < ε := hVε'

/-- **FK step 2.**  Arzelà–Ascoli: a uniformly bounded, uniformly equicontinuous family of
continuous functions on the compact ball `B_R` is totally bounded in `C(B_R)`, hence (via the
continuous embedding `C(B_R) ↪ L²(B_R)` on a finite-measure ball) totally bounded in `L²(B_R)`.

Consumes `mollified_family_uniformly_bounded` (step 1a) and `mollified_family_equicontinuous`
(step 1b) for the CONCRETE kernel `K`; produces the total boundedness used by
`convolution_l2_tendsto_uniform`.  The L²-classes `ρf f` whose representative is
`mollifyRep K (rep f)` are supplied (with the a.e. agreement hypothesis `hρf`) so the result
lands in `L²(B_R)` rather than `C(B_R)`.

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  Both steps 1a/1b it consumes are
stated on `B_R` only and rest on the ENLARGED-BALL bound
`‖restrictToBall (R+K.supportRadius) (rep f)‖ ≤ C`, which the call site derives from
`FrechetKolmogorovInput`'s GLOBAL bound `hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity.
Arzelà–Ascoli runs on the COMPACT ball `B_R`, where
the ball-restriction `restrictToBall R (ρf f)` lives, so the enlarged-ball sup/equicontinuity bounds
on `B_R` are exactly enough.  This lemma threads the same enlarged-ball bound `hbdEnl`. -/
theorem mollified_family_totallyBounded_L2 (R C : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3) (K : MollifierKernel)
    (ρf : L2ballR3 R → L2VF_R3)
    (hρf : ∀ f ∈ S, (ρf f : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume] mollifyRep K (rep f))
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C) :
    TotallyBounded ((fun f => restrictToBall R (ρf f)) '' S) :=
  totallyBounded_image_of_equicont_bdd R S ρf (fun f => mollifyRep K (rep f))
    (fun f hf => hρf f hf)
    ((mollified_family_uniformly_bounded R C S rep K hbdEnl).choose)
    (fun f hf x hx =>
      (mollified_family_uniformly_bounded R C S rep K hbdEnl).choose_spec f hf x hx)
    (mollified_family_equicontinuous R C S rep K hbdEnl)

/-! ### FK step 3 (assembly) — uniform L²-mollification approximate identity

Placed AFTER steps 1–2 so that its derivation may delegate the total-boundedness conjunct to
`mollified_family_totallyBounded_L2`. -/

/-- **FK step 3.**  Uniform L²-approximation of a translation-equicontinuous family by its
mollifications, for the CONCRETE mollifier.

If a family `{rep f | f ∈ S}` of L²(ℝ³) fields has a uniform L²-translation modulus
(the second hypothesis of `FrechetKolmogorovInput`), then for every tolerance `ε > 0` there is
an admissible smooth compactly supported kernel `K` and a choice of L²-classes `ρf : S → L2VF_R3`
whose chosen pointwise representative is `mollifyRep K (rep f)`, such that every member is within
`ε` in L² of its mollification:

  `∀ f ∈ S, ‖f − restrictToBall R (ρf f)‖ < ε`,

with the rate controlled UNIFORMLY over the family by the translation modulus.  The derivation
routes through the two named analytic helpers `young_convolution_memLp_L2` (global Young, producing
the `L²`-class `ρf f`) and `convolution_sub_L2_le_translation_modulus` (vector Minkowski, producing
the rate), the kernel constructor `exists_normalized_mollifierKernel`, and FK step 2
`mollified_family_totallyBounded_L2` (total boundedness).  This is the genuinely-missing analytic
core (mathlib has only the *pointwise* `convolution_tendsto_right`).

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  The total-boundedness conjunct
delegates to `mollified_family_totallyBounded_L2` (steps 1+2), whose bounds need a ball-mass bound
on the kernel-support enlargement `B_{R+K.supportRadius}`.  The local hypothesis is an
ENLARGED-BALL bound at a fixed enlargement budget `r₀ ≥ 0`:
`hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + r₀) (rep f)‖ ≤ C`, which the caller obtains directly from
`FrechetKolmogorovInput`'s GLOBAL bound `‖rep f‖ ≤ C` by ball-mass monotonicity (a single-radius
ball bound `‖f‖ ≤ C` alone would not control annulus mass, but the strengthened criterion carries
the global bound, so the enlarged bound is immediate).  The kernel `K` produced has support
radius `K.supportRadius ≤ r₀`, so by monotonicity of ball mass in the radius the step-3 bound on
`B_{R + K.supportRadius}` follows from `hbdEnl`.  The ball restriction bound `‖f‖ ≤ C` is retained
as `hbd` only for the L²-approximation conjunct (which compares ball-restrictions); it does NOT
control the convolution. -/
theorem convolution_l2_tendsto_uniform (R C r₀ : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3)
    (hrep : ∀ f ∈ S, restrictToBall R (rep f) = f)
    (hr₀ : 0 < r₀)
    (_hbd : ∀ f ∈ S, ‖f‖ ≤ C)
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + r₀) (rep f)‖ ≤ C)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
        ‖translate_L2VF h (rep f) - rep f‖ < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : MollifierKernel) (ρf : L2ballR3 R → L2VF_R3),
      K.supportRadius ≤ r₀ ∧
      (∀ f ∈ S, (ρf f : Domain3 → EuclideanSpace ℝ (Fin 3))
          =ᵐ[volume] mollifyRep K (rep f)) ∧
      (∀ f ∈ S, ‖f - restrictToBall R (ρf f)‖ < ε) ∧
      TotallyBounded ((fun f => restrictToBall R (ρf f)) '' S) := by
  classical
  have hr0pos : 0 < r₀ := hr₀
  -- DERIVATION (routes through the named analytic helpers).
  -- Pick `δ` from the FK uniform translation modulus at tolerance `ε/2` (so the mass-one
  -- kernel-weighted average of the modulus is `≤ ε/2 < ε`, a strict bound).
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδpos, hδ⟩ := hmod (ε / 2) hε2
  -- A normalized mollifier `K` with support radius `≤ min r₀ (δ/2) < δ` and `≤ r₀`.
  set ρ : ℝ := min r₀ (δ / 2) with hρ
  have hρpos : 0 < ρ := by positivity
  obtain ⟨K, hKr⟩ := exists_normalized_mollifierKernel ρ hρpos
  have hKr₀ : K.supportRadius ≤ r₀ := le_trans hKr (min_le_left _ _)
  have hKδ : K.supportRadius < δ := lt_of_le_of_lt (le_trans hKr (min_le_right _ _)) (by linarith)
  -- The mollified L²-class of each representative, via the global Young helper.
  set ρf : L2ballR3 R → L2VF_R3 :=
    fun f => (young_convolution_memLp_L2 K (rep f)).choose.toLp with hρf_def
  -- a.e. agreement of `ρf f` with the concrete representative `mollifyRep K (rep f)`.
  have hρf_ae : ∀ f ∈ S, (ρf f : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume] mollifyRep K (rep f) := fun f _ =>
    (young_convolution_memLp_L2 K (rep f)).choose.coeFn_toLp
  -- enlarged-ball bound on the kernel-reach `B_{R + K.supportRadius}`, from `hbdEnl` (radius `r₀`)
  -- by ball-mass monotonicity (`K.supportRadius ≤ r₀`).
  have hbdEnlK : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C := by
    -- ball-mass monotonicity in the radius: `‖restrictToBall (R+K.supportRadius) g‖ ≤
    -- ‖restrictToBall (R+r₀) g‖ ≤ C` since `R + K.supportRadius ≤ R + r₀` (nested restricted
    -- measures, `eLpNorm_mono_measure`).
    intro f hf
    refine le_trans (norm_restrictToBall_mono (by linarith [hKr₀]) (rep f)) (hbdEnl f hf)
  refine ⟨K, ρf, hKr₀, hρf_ae, ?_, ?_⟩
  · -- L²-APPROXIMATION conjunct, routed through `convolution_sub_L2_le_translation_modulus`.
    intro f hf
    have hmem := (young_convolution_memLp_L2 K (rep f)).choose
    -- the Minkowski-form bound on the GLOBAL defect of the mollification.
    have hbound := convolution_sub_L2_le_translation_modulus K (rep f) hmem
    -- (i) the kernel-weighted modulus integral is `≤ ε/2`: on `supp K.η ⊆ B_{K.supportRadius}`
    -- (`‖h‖ < δ`) the FK modulus `hδ` gives `‖τ_h(rep f) − rep f‖ < ε/2`; off support `K.η h = 0`.
    have hI_modulus : Integrable
        (fun h : Domain3 => K.η h • ‖translate_L2VF h (rep f) - rep f‖) (volume : Measure Domain3) := by
      have hcont : Continuous
          (fun h : Domain3 => K.η h • ‖translate_L2VF h (rep f) - rep f‖) :=
        (K.smooth.continuous).smul
          (((continuous_translate_L2VF (rep f)).sub continuous_const).norm)
      refine hcont.integrable_of_hasCompactSupport ?_
      apply HasCompactSupport.intro (K.hasCompactSupport.isCompact) (fun h hh => ?_)
      have : K.η h = 0 := by
        by_contra hne; exact hh (subset_tsupport K.η (by simpa using hne))
      simp [this]
    have hI_const : Integrable (fun h : Domain3 => K.η h • (ε / 2)) (volume : Measure Domain3) := by
      have hηL1 : Integrable K.η (volume : Measure Domain3) :=
        memLp_one_iff_integrable.mp
          (K.smooth.continuous.memLp_of_hasCompactSupport (p := 1) (μ := volume) K.hasCompactSupport)
      simpa [smul_eq_mul] using hηL1.mul_const (ε / 2)
    have hmod_le : (∫ h : Domain3, K.η h • ‖translate_L2VF h (rep f) - rep f‖
        ∂(volume : Measure Domain3)) ≤ ε / 2 := by
      have hptwise : ∀ h : Domain3,
          K.η h • ‖translate_L2VF h (rep f) - rep f‖ ≤ K.η h • (ε / 2) := by
        intro h
        by_cases hzero : K.η h = 0
        · simp [hzero]
        · have hmemh : h ∈ tsupport K.η := subset_tsupport K.η (by simpa using hzero)
          have hball : h ∈ Metric.closedBall (0 : Domain3) K.supportRadius := K.tsupport_subset hmemh
          have hhδ : ‖h‖ < δ := by
            have : ‖h‖ ≤ K.supportRadius := by simpa [dist_eq_norm] using hball
            exact lt_of_le_of_lt this hKδ
          -- the modulus hypothesis `hmod` (hence `hδ`) is stated for `f ∈ S` on `rep f`.
          have := hδ f hf h hhδ
          exact smul_le_smul_of_nonneg_left this.le (K.nonneg h)
      calc (∫ h : Domain3, K.η h • ‖translate_L2VF h (rep f) - rep f‖ ∂(volume : Measure Domain3))
          ≤ ∫ h : Domain3, K.η h • (ε / 2) ∂(volume : Measure Domain3) :=
            integral_mono hI_modulus hI_const hptwise
        _ = ε / 2 := by rw [integral_smul_const, K.mass_one, one_smul]
    -- (ii) `restrictToBall R` is norm-nonincreasing and `restrictToBall R (rep f) = f` (`hrep`).
    have hf_eq : f = restrictToBall R (rep f) := (hrep f hf).symm
    have hstep : ‖f - restrictToBall R (ρf f)‖ ≤ ‖rep f - ρf f‖ := by
      -- rewrite ONLY the leading standalone `f` (the `f` inside `ρf f` must stay), then fold the
      -- difference of restrictions into a single restriction (`restrictToBall_sub`).
      have hsub_eq : f - restrictToBall R (ρf f)
          = restrictToBall R (rep f - ρf f) := by
        nth_rewrite 1 [hf_eq]
        rw [← restrictToBall_sub]
      rw [hsub_eq]
      exact norm_restrictToBall_le R (rep f - ρf f)
    have hρf_eq : ρf f = hmem.toLp := rfl
    calc ‖f - restrictToBall R (ρf f)‖
        ≤ ‖rep f - ρf f‖ := hstep
      _ = ‖hmem.toLp - rep f‖ := by rw [hρf_eq, norm_sub_rev]
      _ ≤ ∫ h : Domain3, K.η h • ‖translate_L2VF h (rep f) - rep f‖ ∂(volume : Measure Domain3) :=
          hbound
      _ ≤ ε / 2 := hmod_le
      _ < ε := by linarith
  · -- TOTAL-BOUNDEDNESS conjunct delegates to FK step 2.
    exact mollified_family_totallyBounded_L2 R C S rep K ρf hρf_ae hbdEnlK

/-! ### FK step 4 — total-boundedness transfer under uniform approximation -/

/-- **FK step 4.**  Total-boundedness transfer.  In a metric space, a set `S` that is uniformly
ε-approximable (for every `ε > 0`) by a totally bounded set is itself totally bounded.

This is the abstract glue between step 3 (uniform mollification approximation) and step 2
(total boundedness of the mollified family): an ε-net of the approximant, fattened by ε, is a
`2ε`-net of `S`. -/
theorem totallyBounded_of_uniform_approx {α : Type*} [PseudoMetricSpace α] (S : Set α)
    (happrox : ∀ ε > 0, ∃ T : Set α, TotallyBounded T ∧
      ∀ s ∈ S, ∃ t ∈ T, dist s t < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Approximate `S` within `ε/2` by a totally bounded `T`.
  obtain ⟨T, hT, hTapprox⟩ := happrox (ε / 2) (by linarith)
  -- A finite `ε/2`-net `t` of `T`.
  obtain ⟨t, ht_fin, ht_cover⟩ := (Metric.totallyBounded_iff.mp hT) (ε / 2) (by linarith)
  -- `t` is an `ε`-net of `S` by the triangle inequality.
  refine ⟨t, ht_fin, fun s hs => ?_⟩
  obtain ⟨τ, hτT, hsτ⟩ := hTapprox s hs
  have hτ_mem : τ ∈ ⋃ y ∈ t, Metric.ball y (ε / 2) := ht_cover hτT
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hτ_mem ⊢
  obtain ⟨y, hyt, hτy⟩ := hτ_mem
  refine ⟨y, hyt, ?_⟩
  calc dist s y ≤ dist s τ + dist τ y := dist_triangle s τ y
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ### DELIVERABLE — discharge of `FrechetKolmogorovInput` -/

/-- **DELIVERABLE.  Fréchet–Kolmogorov (Riesz) L²-precompactness criterion** — a genuine
discharge of `RellichBall.FrechetKolmogorovInput` (type copied verbatim, no weakening).

Assembles the standard mollification route: from the uniform L²-translation modulus
(`convolution_l2_tendsto_uniform`, step 3) each family member is uniformly ε-approximated by its
mollification, whose image is totally bounded by Arzelà–Ascoli
(`mollified_family_totallyBounded_L2`, step 2); the transfer lemma
(`totallyBounded_of_uniform_approx`, step 4) makes `S` totally bounded, and completeness of
`L2ballR3 R` upgrades total boundedness to precompactness
(`isCompact_iff_totallyBounded_isComplete`), giving the compact `K ⊇ S`.

**Enlarged-ball bound — RESOLVED via the criterion's global bound (Codex Gate round 3, high).**
The helper lemmas (steps 1–3) require, honestly, an ENLARGED-BALL bound
`hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + r₀) (rep f)‖ ≤ C` on the kernel-support enlargement
`B_{R+r₀}` (NOT just the single-radius ball bound `‖f‖ ≤ C`, which cannot prevent arbitrarily
large low-frequency mass on the annulus `B_{R+r₀} ∖ B_R`).

`FrechetKolmogorovInput`'s strengthened type hands the prover, beyond the in-ball bound `hbd` and
the translation modulus `hmod`, a uniform GLOBAL L²-norm bound on the representatives:
* `hbddGlobal : ∀ f ∈ S, ‖rep f‖ ≤ C`.

From `hbddGlobal` the enlarged-ball bound is IMMEDIATE for any `r₀ ≥ 0`, by monotonicity of ball
mass in the radius: `‖restrictToBall (R + r₀) (rep f)‖ ≤ ‖rep f‖ ≤ C` (the same
`restrict_le_self`/`eLpNorm_mono_measure` chain as `RellichBall.admissible_family_uniform_bound`).
This is the standard Riesz full-mass control of Fréchet–Kolmogorov; it carries no Sobolev/gradient
content.  The actual Navier–Stokes call site `localRellichInput_of_frechetKolmogorov` supplies it
from its admissible family's GLOBAL `‖w‖ ≤ M` bound.

**Assembly (pure proof-body fill, no upstream blocker).**  Derive `hbdEnl` from `hbddGlobal` by
ball-mass monotonicity; feed `hbdEnl`, `hbd`, `hrep`, `hmod` into `convolution_l2_tendsto_uniform`
(step 3) to get, for each `ε`, a totally bounded mollified image approximating `S` within `ε`;
`totallyBounded_of_uniform_approx` (step 4) makes `S` totally bounded; closure of the totally
bounded `S` is compact (`isCompact_iff_totallyBounded_isComplete`, `L2ballR3 R` complete); take
`K := closure S`. -/
theorem frechetKolmogorov_holds : FrechetKolmogorovInput := by
  refine ⟨fun R C S rep hrep hbd hbddGlobal hmod => ?_⟩
  -- Enlarged-ball bound at budget `r₀ = 1`, from the GLOBAL bound by ball-mass monotonicity.
  have hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + 1) (rep f)‖ ≤ C := fun f hf =>
    le_trans (norm_restrictToBall_le (R + 1) (rep f)) (hbddGlobal f hf)
  -- `S` is totally bounded: each `ε`-step delivers a totally bounded mollified image approximating
  -- `S` within `ε` (FK step 3), so the transfer lemma (FK step 4) applies.
  have hTB : TotallyBounded S := by
    refine totallyBounded_of_uniform_approx S (fun ε hε => ?_)
    obtain ⟨K, ρf, _hKr₀, _hρf_ae, happrox, hTBimg⟩ :=
      convolution_l2_tendsto_uniform R C 1 S rep hrep one_pos hbd hbdEnl hmod ε hε
    refine ⟨(fun f => restrictToBall R (ρf f)) '' S, hTBimg, fun s hs => ?_⟩
    exact ⟨restrictToBall R (ρf s), Set.mem_image_of_mem _ hs, by
      rw [dist_eq_norm]; exact happrox s hs⟩
  -- Closure of a totally bounded set in the complete space `L2ballR3 R` is compact.
  refine ⟨closure S, ?_, subset_closure⟩
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨hTB.closure, isClosed_closure.isComplete⟩

end LerayHopf
