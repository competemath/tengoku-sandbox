import Tengoku.LerayHopf.LerayHopf.R3.GalerkinScheme
import Tengoku.LerayHopf.LerayHopf.R3.CurlSchwartzConstruction
  -- CurlSchwartzDense, curlSchwartzL2_projComponent (issue #113 PR-1: split out, self-contained)
import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Basic
import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Deriv
import Tengoku.Seed.MeasureTheory.Measure.SeparableMeasure
import Tengoku.Seed.Topology.Bases
-- A4 (`div (curl ψ) = 0`) needs symmetry of mixed second partials of Schwartz functions
-- (Clairaut), supplied by `ContDiffAt.isSymmSndFDerivAt`.  This import is REQUIRED for the
-- must-prove deliverables A4/C1 to be genuinely sorry-free (DoD: `#print axioms` of C1 must
-- not contain `sorryAx`).  Flagged for lean-coder/Codex: import addition outside the prover's
-- usual edit boundary, but unavoidable for the sorry-free div-of-curl=0 proof.
import Tengoku.Seed.Analysis.Calculus.FDeriv.Symmetric

namespace LerayHopf
open MeasureTheory SchwartzMap LineDeriv TopologicalSpace
open scoped Topology

/-!
# Pillar D — `Nonempty SchwartzGalerkinBasis` from a single isolated density frontier

**Milestone:** `helmholtz-density`

This file CONSTRUCTS the Schwartz, divergence-free basis interface
`SchwartzGalerkinBasis` (`LerayHopf/R3/GalerkinScheme.lean`) from one — and only one —
classical analytic input, isolated as the `Prop`-valued definition `CurlSchwartzDense`.

## Honest scope (what is and is NOT done here)

PROVED here, axiom-free and (once `lean-prover` fills the bodies) sorry-free:

* the curl of a Schwartz vector potential is again a genuine `SchwartzMap` (Tier A,
  via `lineDerivOpCLM` — Schwartz derivatives stay Schwartz; this is NOT a Leray
  projection, which would not preserve Schwartz, see the no-smuggle note below);
* that curl field is weakly divergence-free, `curlSchwartzL2 ψ ∈ L2Sigma_R3` (A4,
  by Clairaut + Schwartz integration-by-parts: `div (curl ψ) = 0`);
* `L2VF_R3` is a `SeparableSpace` (B1), so countability of any basis is free;
* the conditional deliverable `schwartzGalerkinBasis_of_curlDense` (C1):
  `CurlSchwartzDense → Nonempty SchwartzGalerkinBasis`.

The single remaining frontier — the density itself, `CurlSchwartzDense` (that the
L²-closure of the span of curls of Schwartz vector potentials contains the whole
weakly-divergence-free subspace `L2Sigma_R3`, the Helmholtz/Weyl density fact, **not in
mathlib**) — is carried as the one marked `axiom curlSchwartzDense_holds` (issue #21,
owner-approved 2026-06-21).  C1 (`schwartzGalerkinBasis_of_curlDense`) remains the genuine
axiom-free-modulo-hypothesis deliverable; C2 (`nonempty_schwartzGalerkinBasis`) applies C1 to
that axiom.

**Axiom SWAP, not increase (issue #21).**  This file ADDS the thin density axiom
`curlSchwartzDense_holds : CurlSchwartzDense` and, through the witness chain, DISCHARGES the
former fat `r3GalerkinScheme_exists` axiom (a 6-field structure existential, previously in
`SolutionInterfaces.lean`) — now a proved `theorem` here.  Net R3 project-axiom count is
UNCHANGED at 5; the frontier is strictly thinner (one `Submodule` density inequality vs. a
6-field structure).  Because the discharge needs P5 (`nonempty_r3GalerkinScheme_of_basis`,
downstream of `SolutionInterfaces`), `r3GalerkinScheme_exists` is relocated to THIS file (the
shallowest acyclic point that sees both the `R3GalerkinScheme` structure and its witness).
The capstone `exists_lerayHopf_r3` was relocated FURTHER downstream to
`GalerkinODECapstone.lean` (issue #10), below the axiom-free ODE chain it now routes through.

## DAG position
```
DivergenceFree.lean   (L2VF_R3, L2Sigma_R3, L2VF_projComponent_R3, divTestFunctional)
  └── CurlSchwartzConstruction.lean   (curlSchwartz, curlSchwartzL2, CurlSchwartzDense, …)
        └── … ── SolutionInterfaces.lean
                    └── GalerkinScheme.lean        (SchwartzGalerkinBasis)
                            └── SchwartzDivFreeBasis.lean   [THIS FILE]
```

## Declarations (dependency order)

`CurlSchwartzDense`, `L2VF_ofComponents`, `L2VF_projComponent_ofComponents`, `curlSchwartz`,
`curlSchwartzL2`, `curlSchwartzL2_projComponent` (H1/A1/A2/A2', the isolated density frontier)
now live in `CurlSchwartzConstruction.lean` (issue #113 PR-1: split out, self-contained on
`DivergenceFree.lean`, no `GalerkinScheme` dependency); this file imports them and picks up from:

- `curlSchwartz_isSchwartz`           : A3 — the `e_schwartz`-shape witness
- `curlSchwartzL2_mem_sigma`          : A4 — `curlSchwartzL2 ψ ∈ L2Sigma_R3` (div-free, PROVED)
- `instSeparableSpace_L2VF_R3`        : B1 — `SeparableSpace L2VF_R3`
- `exists_denseSeq_curlSchwartz`      : B2 — ℕ-enumeration with dense prefix spans (from frontier)
- `schwartzGalerkinBasis_of_curlDense`: C1 — DELIVERABLE: density → `Nonempty SchwartzGalerkinBasis`
  (the capstone `exists_lerayHopf_r3` is now in `GalerkinODECapstone.lean`, issue #10;
   `curlSchwartzDense_holds`, `nonempty_schwartzGalerkinBasis`, `r3GalerkinScheme_exists`
   are now in `CurlDensityCapstone.lean`, issue #3 / #21)

## Assumptions

No `axiom`, `opaque`, `constant`, or `unsafe` in this file (issue #3 / #21).

`curlSchwartzDense_holds` was previously an `axiom` here (issue #21, owner-approved
2026-06-21), but the Helmholtz/Weyl curl-density is now PROVED sorry-free in
`CurlDensity.lean` (`curlSchwartzDense_provedRoute`).  The axiom and its downstream
consumers (`nonempty_schwartzGalerkinBasis`, `r3GalerkinScheme_exists`) have been
relocated to `CurlDensityCapstone.lean`, where `curlSchwartzDense_holds` is a proved
`theorem` (not an `axiom`).

C1 (`schwartzGalerkinBasis_of_curlDense`) stays here — it is the genuine proved
conditional deliverable, axiom-free modulo its `CurlSchwartzDense` hypothesis.
-/

/-- A3.  The `e_schwartz`-shape witness for `curlSchwartzL2 ψ`: its components have
Schwartz representatives.  This is what feeds `SchwartzGalerkinBasis.e_schwartz`. -/
theorem curlSchwartz_isSchwartz (ψ : Fin 3 → SchwartzMap Domain3 ℝ) :
    ∃ φ : Fin 3 → SchwartzMap Domain3 ℝ, ∀ j : Fin 3,
      L2VF_projComponent_R3 j (curlSchwartzL2 ψ)
        = (φ j).toLp 2 (volume : Measure Domain3) := by
  exact ⟨curlSchwartz ψ, fun j => curlSchwartzL2_projComponent ψ j⟩

/-- Clairaut for Schwartz functions: mixed second line derivatives commute pointwise.
`(∂_u ∂_v f) x = (∂_v ∂_u f) x`.  Proved by reducing the Schwartz line derivative to
`fderiv` (`lineDerivOp_apply_eq_fderiv`), pushing the inner evaluation through `fderiv`
(`fderiv_clm_apply`), and invoking symmetry of the second Fréchet derivative of the smooth
function `f` (`ContDiffAt.isSymmSndFDerivAt`). -/
private theorem schwartz_lineDerivOp_comm
    (f : SchwartzMap Domain3 ℝ) (u v : Domain3) (x : Domain3) :
    (∂_{u} (∂_{v} f)) x = (∂_{v} (∂_{u} f)) x := by
  have hsmooth : ContDiff ℝ 2 (f : Domain3 → ℝ) := f.smooth 2
  have key : ∀ a b : Domain3, (∂_{a} (∂_{b} f)) x
      = fderiv ℝ (fderiv ℝ (f : Domain3 → ℝ)) x a b := by
    intro a b
    rw [lineDerivOp_apply_eq_fderiv]
    have hfun : ((∂_{b} f : SchwartzMap Domain3 ℝ) : Domain3 → ℝ)
        = fun y => (fderiv ℝ (f : Domain3 → ℝ) y) b := by
      funext y; rw [lineDerivOp_apply_eq_fderiv]
    rw [hfun]
    have hdiff : DifferentiableAt ℝ (fderiv ℝ (f : Domain3 → ℝ)) x :=
      ((hsmooth.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
    rw [fderiv_clm_apply hdiff (differentiableAt_const _)]
    simp
  rw [key u v, key v u]
  exact (hsmooth.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)).eq u v

/-- The real `Lp ℝ 2`-inner product of the L²-classes of two Schwartz functions equals the
integral of their pointwise product. -/
private theorem inner_toLp_eq_integral (g h : SchwartzMap Domain3 ℝ) :
    (inner ℝ (g.toLp 2 (volume : Measure Domain3)) (h.toLp 2 (volume : Measure Domain3)) : ℝ)
      = ∫ x, (g x) * (h x) ∂(volume : Measure Domain3) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [g.coeFn_toLp 2 (volume : Measure Domain3),
    h.coeFn_toLp 2 (volume : Measure Domain3)] with x hg hh
  rw [hg, hh, RCLike.inner_apply', conj_trivial]

/-- Pointwise vanishing of the divergence of the curl:
`∑ i, ∂_i (curl ψ)_i x = 0`.  By the cyclic structure of `curlSchwartz` (A1) every term
cancels with another after applying Clairaut (`schwartz_lineDerivOp_comm`). -/
private theorem div_curlSchwartz_eq_zero (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (x : Domain3) :
    ∑ i : Fin 3,
      (∂_{(EuclideanSpace.single i (1:ℝ) : Domain3)} (curlSchwartz ψ i)) x = 0 := by
  have hterm : ∀ i : Fin 3,
      (∂_{(EuclideanSpace.single i (1:ℝ) : Domain3)} (curlSchwartz ψ i)) x
        = (∂_{(EuclideanSpace.single i (1:ℝ) : Domain3)}
            (∂_{(EuclideanSpace.single (i+1) (1:ℝ) : Domain3)} (ψ (i+2)))) x
          - (∂_{(EuclideanSpace.single i (1:ℝ) : Domain3)}
            (∂_{(EuclideanSpace.single (i+2) (1:ℝ) : Domain3)} (ψ (i+1)))) x := by
    intro i
    unfold curlSchwartz
    rw [← lineDerivOpCLM_apply (R := ℝ) (E := SchwartzMap Domain3 ℝ), map_sub]
    simp only [lineDerivOpCLM_apply, sub_apply]
  rw [Fin.sum_univ_three, hterm 0, hterm 1, hterm 2]
  have e11 : (1 : Fin 3) + 1 = 2 := by decide
  have e12 : (1 : Fin 3) + 2 = 0 := by decide
  have e21 : (2 : Fin 3) + 1 = 0 := by decide
  have e22 : (2 : Fin 3) + 2 = 1 := by decide
  have e01 : (0 : Fin 3) + 1 = 1 := by decide
  have e02 : (0 : Fin 3) + 2 = 2 := by decide
  rw [e01, e02, e11, e12, e21, e22]
  rw [schwartz_lineDerivOp_comm (ψ 1) (EuclideanSpace.single (0:Fin 3) (1:ℝ) : Domain3)
        (EuclideanSpace.single (2:Fin 3) (1:ℝ) : Domain3) x,
      schwartz_lineDerivOp_comm (ψ 2) (EuclideanSpace.single (1:Fin 3) (1:ℝ) : Domain3)
        (EuclideanSpace.single (0:Fin 3) (1:ℝ) : Domain3) x,
      schwartz_lineDerivOp_comm (ψ 0) (EuclideanSpace.single (2:Fin 3) (1:ℝ) : Domain3)
        (EuclideanSpace.single (1:Fin 3) (1:ℝ) : Domain3) x]
  ring

/-- A4.  The curl field is weakly divergence-free: `curlSchwartzL2 ψ ∈ L2Sigma_R3`.
PROVED, not assumed (Codex point C-B).

Mathematically this is `div (curl ψ) = 0`: for every Schwartz test `φ`,
`∑ j ∫ (curl ψ)_j · ∂_j φ = − ∫ φ · div (curl ψ) = 0`, by Schwartz integration-by-parts
and Clairaut (mixed partials of Schwartz functions commute). -/
theorem curlSchwartzL2_mem_sigma (ψ : Fin 3 → SchwartzMap Domain3 ℝ) :
    curlSchwartzL2 ψ ∈ L2Sigma_R3 := by
  rw [L2Sigma_R3, Submodule.mem_iInf]
  intro φ
  rw [LinearMap.mem_ker]
  show divTestFunctional φ (curlSchwartzL2 ψ) = 0
  rw [divTestFunctional, sum_apply]
  -- Each summand: ⟪(∂_j φ).toLp, (curl ψ)_j.toLp⟫ = −∫ ∂_j (curl ψ)_j · φ  (Schwartz IBP).
  have hterm : ∀ j : Fin 3,
      ((innerSL ℝ ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp
          2 (volume : Measure Domain3))).comp
        (L2VF_projComponent_R3 j)) (curlSchwartzL2 ψ)
        = -(∫ x, (∂_{(EuclideanSpace.single j (1:ℝ) : Domain3)} (curlSchwartz ψ j)) x
            * (φ x) ∂(volume : Measure Domain3)) := by
    intro j
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, curlSchwartzL2_projComponent,
      inner_toLp_eq_integral]
    simp only [lineDerivOpCLM_apply]
    have hibp := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume)
      φ (curlSchwartz ψ j) (EuclideanSpace.single j (1 : ℝ) : Domain3)
    have hcomm : (∫ x, φ x * (∂_{(EuclideanSpace.single j (1:ℝ) : Domain3)} (curlSchwartz ψ j)) x
            ∂(volume : Measure Domain3))
        = ∫ x, (∂_{(EuclideanSpace.single j (1:ℝ) : Domain3)} (curlSchwartz ψ j)) x * φ x
            ∂(volume : Measure Domain3) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [hcomm] at hibp
    linarith [hibp]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · -- ∑_j ∫ ∂_j (curl ψ)_j · φ = ∫ (∑_j ∂_j (curl ψ)_j) · φ = ∫ 0 = 0
    have hzero : (∫ x, ∑ j : Fin 3,
          (∂_{(EuclideanSpace.single j (1:ℝ) : Domain3)} (curlSchwartz ψ j)) x * (φ x)
            ∂(volume : Measure Domain3)) = 0 := by
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [← Finset.sum_mul, div_curlSchwartz_eq_zero, zero_mul, Pi.zero_apply]
    rw [hzero, neg_zero]
  · -- integrability of each ∂_j (curl ψ)_j · φ (product of Schwartz functions)
    intro j _
    exact (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) φ.hasTemperateGrowth
      (∂_{(EuclideanSpace.single j (1:ℝ) : Domain3)} (curlSchwartz ψ j))).integrable

/-! ### Tier B — countability via separability -/

/-- B1.  `L2VF_R3 = L²(ℝ³; ℝ³)` is a `SeparableSpace`.

`volume` on `Domain3` is a separable measure and `EuclideanSpace ℝ (Fin 3)` is
second-countable, so `Lp.SecondCountableTopology` makes `L2VF_R3` second-countable,
hence separable. -/
instance instSeparableSpace_L2VF_R3 : SeparableSpace L2VF_R3 :=
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SecondCountableTopology L2VF_R3 := Lp.SecondCountableTopology
  SecondCountableTopology.to_separableSpace

/-- Helper: the supremum of finite prefix spans of an enumeration `e` equals the span of
its entire range. -/
theorem iSup_prefixSpan_eq_span_range (e : ℕ → L2VF_R3) :
    (⨆ n : ℕ, Submodule.span ℝ (Set.range (fun k : Fin n => e (k : ℕ))))
      = Submodule.span ℝ (Set.range e) := by
  apply le_antisymm
  · refine iSup_le fun n => Submodule.span_mono ?_
    rintro x ⟨k, rfl⟩
    exact ⟨(k : ℕ), rfl⟩
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    refine Submodule.mem_iSup_of_mem (k+1) ?_
    exact Submodule.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩

/-- B2.  From the density frontier `CurlSchwartzDense` and separability (B1), extract a
SINGLE ℕ-enumeration `e : ℕ → L2VF_R3` of curl fields whose finite prefix spans are
dense in `L2Sigma_R3`.

This is the separability-thinning of the (uncountable) curl family
`Set.range curlSchwartzL2` to one countable prefix-span enumeration; it is bookkeeping,
not analysis (Codex point C-D). -/
theorem exists_denseSeq_curlSchwartz (h : CurlSchwartzDense) :
    ∃ e : ℕ → L2VF_R3,
      (∀ k : ℕ, ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ, e k = curlSchwartzL2 ψ) ∧
      (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
        (⨆ n : ℕ,
          Submodule.span ℝ (Set.range (fun k : Fin n => e (k : ℕ)))).topologicalClosure := by
  set S : Set L2VF_R3 := Set.range curlSchwartzL2 with hS
  -- `S` is separable as a subset of the separable space `L2VF_R3` (B1).
  have hSsep : IsSeparable S :=
    (isSeparable_univ_iff.2 inferInstance).mono (Set.subset_univ S)
  -- a countable subset `t ⊆ S` with `S ⊆ closure t`.
  obtain ⟨t, hts, htc, hst⟩ := hSsep.exists_countable_dense_subset
  have hSne : S.Nonempty := Set.range_nonempty _
  have htne : t.Nonempty := by
    rcases hSne with ⟨x, hx⟩
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    subst hempty
    simp only [closure_empty, Set.subset_empty_iff] at hst
    rw [hst] at hx
    exact absurd hx (by simp)
  -- enumerate `t = range e`.
  obtain ⟨e, rfl⟩ := htc.exists_eq_range htne
  refine ⟨e, ?_, ?_⟩
  · intro k
    obtain ⟨ψ, hψ⟩ := hts ⟨k, rfl⟩
    exact ⟨ψ, hψ.symm⟩
  · rw [iSup_prefixSpan_eq_span_range]
    refine le_trans h ?_
    -- `closure(span S) ≤ closure(span (range e))` since `S ⊆ closure(range e)`.
    refine Submodule.topologicalClosure_minimal _ ?_
      (Submodule.isClosed_topologicalClosure _)
    rw [Submodule.span_le]
    intro x hx
    have hxcl : x ∈ closure (Set.range e) := hst hx
    rw [Submodule.topologicalClosure_coe]
    exact closure_mono Submodule.subset_span hxcl

/-! ### Tier C — the deliverable -/

/-- **C1 (deliverable).**  Given the isolated density frontier `CurlSchwartzDense`, the
Schwartz divergence-free basis interface is inhabited.

This is the genuine, axiom-free-MODULO-`h` headline: it assembles
`SchwartzGalerkinBasis` from the constructed curl family —
`e` from B2, `e_schwartz` from A3, `e_mem_sigma` from A4, `dense_span` from B2 + `h`. -/
theorem schwartzGalerkinBasis_of_curlDense (h : CurlSchwartzDense) :
    Nonempty SchwartzGalerkinBasis := by
  obtain ⟨e, he_curl, he_dense⟩ := exists_denseSeq_curlSchwartz h
  exact ⟨{
    e := e
    e_schwartz := fun k => by
      obtain ⟨ψ, hψ⟩ := he_curl k
      rw [hψ]; exact curlSchwartz_isSchwartz ψ
    e_mem_sigma := fun k => by
      obtain ⟨ψ, hψ⟩ := he_curl k
      rw [hψ]; exact curlSchwartzL2_mem_sigma ψ
    dense_span := he_dense }⟩

/-! **Axiom `curlSchwartzDense_holds` and consumers RELOCATED (issue #3 / #21).**

`curlSchwartzDense_holds` (formerly an `axiom` here), `nonempty_schwartzGalerkinBasis` (C2),
and `r3GalerkinScheme_exists` are now in `LerayHopf/R3/CurlDensityCapstone.lean`.

The relocation is forced by the acyclic DAG constraint: `CurlDensity.lean` (which
proves `curlSchwartzDense_provedRoute : CurlSchwartzDense`) imports THIS file, so
this file cannot import `CurlDensity.lean` to consume the proved theorem.
`CurlDensityCapstone.lean` sits downstream of both, imports `CurlDensity.lean` and
this file, and provides `curlSchwartzDense_holds` as a proved `theorem`
(`curlSchwartzDense_provedRoute`) instead of an `axiom`.

The `schwartzGalerkinBasis_of_curlDense` conditional deliverable (C1) stays here —
it is axiom-free modulo its hypothesis and is a genuine proved content item.

`exists_lerayHopf_r3` lives in `LerayHopf/R3/GalerkinODECapstone.lean`
(issue #10), re-exported by `LerayHopf/R3Capstone.lean`. -/

end LerayHopf
