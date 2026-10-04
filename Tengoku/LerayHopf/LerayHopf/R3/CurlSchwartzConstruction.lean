import Tengoku.LerayHopf.LerayHopf.R3.DivergenceFree
import Tengoku

namespace LerayHopf
open MeasureTheory SchwartzMap LineDeriv

/-!
# Curl-of-Schwartz-potential construction on ℝ³ (self-contained)

This file holds the self-contained "curl of a Schwartz vector potential" construction that
`SchwartzDivFreeBasis.lean` builds `Nonempty SchwartzGalerkinBasis` on top of: assembling
`L2VF_R3` from three scalar components (H1), the curl itself (A1), its `L2VF_R3` class (A2),
its round-trip component identity (A2'), and the isolated Helmholtz/Weyl density frontier
`CurlSchwartzDense` (a bare `Prop`, no witness bundled in).

Split out of `SchwartzDivFreeBasis.lean` (issue #113 PR-1) so that consumers needing only this
Schwartz/curl-level content — e.g. `CurlDensity.lean` — do not have to pull in
`GalerkinScheme.lean` (and its `SolutionInterfaces`/solution-package transitive closure), which
`SchwartzDivFreeBasis.lean` needs only for its later, `SchwartzGalerkinBasis`-producing tail
(`curlSchwartz_isSchwartz` onward). Fully-qualified names of all declarations here are unchanged
by the move (same `namespace LerayHopf`, same statements).

## Declarations (dependency order)

- `L2VF_ofComponents`                 : H1 — assemble `L2VF_R3` from three scalar `Lp` components
- `L2VF_projComponent_ofComponents`   : H1 — round-trip: project recovers the components
- `curlSchwartz`                      : A1 — curl of a Schwartz vector potential, as Schwartz fields
- `curlSchwartzL2`                    : A2 — its `L2VF_R3` class
- `CurlSchwartzDense`                 : the single isolated density frontier (a `Prop`)
- `curlSchwartzL2_projComponent`      : A2' — round-trip for `curlSchwartzL2`

## Assumptions

No `axiom`, `opaque`, `constant`, or `unsafe` in this file.
-/

/-! ### H1 — assembling `L2VF_R3` from three scalar components -/

/-- Assemble a vector field in `L2VF_R3 = L²(ℝ³; ℝ³)` from three scalar `Lp ℝ 2 volume`
components.  This is the inverse direction of `L2VF_projComponent_R3`.

Built as `∑ j, ι_j (u j)` where
`ι_j : Lp ℝ 2 volume →L[ℝ] L2VF_R3` lifts the embedding
`ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)`, `t ↦ t • EuclideanSpace.single j 1`, to the `Lp`
level via `ContinuousLinearMap.compLpL`. -/
noncomputable def L2VF_ofComponents (u : Fin 3 → Lp ℝ 2 (volume : Measure Domain3)) :
    L2VF_R3 :=
  ∑ j : Fin 3,
    (((1 : ℝ →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single j (1 : ℝ) : Domain3)).compLpL
      2 (volume : Measure Domain3)) (u j)

/-- Helper: composing two `compLpL` lifts equals the `compLpL` of the composition.
Proved by a.e. equality through `coeFn_compLpL`. -/
private theorem compLpL_comp_compLpL
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L₁ : E →L[ℝ] F) (L₂ : F →L[ℝ] G) (f : Lp E 2 (volume : Measure Domain3)) :
    L₂.compLpL 2 (volume : Measure Domain3)
        (L₁.compLpL 2 (volume : Measure Domain3) f)
      = (L₂ ∘L L₁).compLpL 2 (volume : Measure Domain3) f := by
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  refine Lp.ext ?_
  filter_upwards [L₂.coeFn_compLpL (L₁.compLpL 2 (volume : Measure Domain3) f),
    L₁.coeFn_compLpL f, (L₂ ∘L L₁).coeFn_compLpL f] with a h₂ h₁ h
  simp only [h₂, h₁, h, ContinuousLinearMap.comp_apply]

/-- Round-trip H1: projecting the assembled field onto its `i`-th component recovers
`u i`.  Mathematically `(EuclideanSpace.single j 1) i = δ_{ij}`, so the sum collapses
to the `i`-th summand. -/
theorem L2VF_projComponent_ofComponents
    (u : Fin 3 → Lp ℝ 2 (volume : Measure Domain3)) (i : Fin 3) :
    L2VF_projComponent_R3 i (L2VF_ofComponents u) = u i := by
  unfold L2VF_ofComponents L2VF_projComponent_R3
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · -- the `i = i` diagonal term collapses to `u i`
    rw [compLpL_comp_compLpL]
    have hscalar : (EuclideanSpace.proj i (𝕜 := ℝ)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (EuclideanSpace.single i (1 : ℝ) : Domain3))
        = (1 : ℝ →L[ℝ] ℝ) := by
      refine ContinuousLinearMap.ext fun t => ?_
      simp
    rw [hscalar]
    -- `(1 : ℝ →L ℝ).compLpL = id`
    have : ((1 : ℝ →L[ℝ] ℝ).compLpL 2 (volume : Measure Domain3)) (u i) = u i := by
      haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
      refine Lp.ext ?_
      filter_upwards [(1 : ℝ →L[ℝ] ℝ).coeFn_compLpL (u i)] with a ha
      simp [ha]
    exact this
  · -- off-diagonal terms vanish
    intro j _ hji
    rw [compLpL_comp_compLpL]
    have hscalar : (EuclideanSpace.proj i (𝕜 := ℝ)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (EuclideanSpace.single j (1 : ℝ) : Domain3))
        = (0 : ℝ →L[ℝ] ℝ) := by
      refine ContinuousLinearMap.ext fun t => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self, PiLp.proj_apply, zero_apply]
      rw [PiLp.smul_apply, PiLp.single_apply]
      simp [ite_eq_right (Ne.symm hji)]
    rw [hscalar]
    haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
    refine Lp.ext ?_
    filter_upwards [(0 : ℝ →L[ℝ] ℝ).coeFn_compLpL (u j), Lp.coeFn_zero
      (E := ℝ) (p := 2) (μ := (volume : Measure Domain3))] with a ha h0
    simp [ha]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ### Tier A — the constructed Schwartz div-free building block -/

/-- A1.  The curl of a Schwartz vector potential `ψ : Fin 3 → 𝓢(ℝ³, ℝ)`, returned as a
genuine triple of Schwartz functions:

  `(curlSchwartz ψ) i = ∂_{i+1} (ψ (i+2)) − ∂_{i+2} (ψ (i+1))`

with the cyclic triple `(i, i+1, i+2)` in `Fin 3` and each partial derivative produced
by `lineDerivOpCLM ℝ 𝓢 (EuclideanSpace.single _ 1) : 𝓢 →L[ℝ] 𝓢`.

CRITICAL (no-smuggle, Codex point C-A): every component is a `lineDerivOpCLM`
combination of Schwartz fields, hence a HONEST `SchwartzMap`.  This is NOT a Leray
projection of a Schwartz field (the Leray projection is a Fourier multiplier singular
at ξ=0 and need not preserve Schwartz, which would smuggle a non-Schwartz field). -/
noncomputable def curlSchwartz (ψ : Fin 3 → SchwartzMap Domain3 ℝ) :
    Fin 3 → SchwartzMap Domain3 ℝ :=
  fun i =>
    lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single (i + 1) (1 : ℝ) : Domain3) (ψ (i + 2))
      - lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single (i + 2) (1 : ℝ) : Domain3) (ψ (i + 1))

/-- A2.  The `L2VF_R3` class of the curl of a Schwartz vector potential: the vector
field whose `j`-th component is `(curlSchwartz ψ j).toLp 2 volume`.

Assembled from the three scalar `Lp` components via `L2VF_ofComponents` (H1).  Each
component is the L²-class of a genuine Schwartz function, so this lands in `L2VF_R3`. -/
noncomputable def curlSchwartzL2 (ψ : Fin 3 → SchwartzMap Domain3 ℝ) : L2VF_R3 :=
  L2VF_ofComponents
    (fun j => (curlSchwartz ψ j).toLp 2 (volume : Measure Domain3))

/-! ### The isolated density frontier (SDF-1, no-smuggle) -/

/-- **The single classical input** (Helmholtz/Weyl density), isolated as a `Prop`.

The L²-closure of the span of curls of Schwartz vector potentials contains the whole
weakly-divergence-free subspace `L2Sigma_R3 = L²_σ(ℝ³)`.

This is the analogue of P5's `SchwartzGalerkinBasis.dense_span`, but STRICTLY THINNER:

* it removes the externally-supplied basis family — the generating set is the
  CONSTRUCTED `Set.range curlSchwartzL2`, a family this file builds and proves to be
  Schwartz (A3) and divergence-free (A4); and
* it carries NO Schwartz or div-free witness — those are PROVED, not bundled in.

So this `Prop` smuggles nothing beyond the bare density: a single `Submodule`
inequality.  It is NOT in mathlib (no Helmholtz/Leray decomposition; no curl-density
theorem) and is the one irreducible frontier of this milestone. -/
def CurlSchwartzDense : Prop :=
  (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
    (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure

/-- A2'.  Round-trip for `curlSchwartzL2`: the `j`-th component of `curlSchwartzL2 ψ`
is exactly the L²-class of the `j`-th curl component. -/
theorem curlSchwartzL2_projComponent
    (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (j : Fin 3) :
    L2VF_projComponent_R3 j (curlSchwartzL2 ψ)
      = (curlSchwartz ψ j).toLp 2 (volume : Measure Domain3) := by
  unfold curlSchwartzL2
  exact L2VF_projComponent_ofComponents
    (fun k => (curlSchwartz ψ k).toLp 2 (volume : Measure Domain3)) j

end LerayHopf
