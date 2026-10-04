import Tengoku.LerayHopf.LerayHopf.EvolutionTriple
import Tengoku.LerayHopf.LerayHopf.Galerkin.Domain
import Tengoku.LerayHopf.LerayHopf.Galerkin.SolutionBundles
import Tengoku.LerayHopf.LerayHopf.R3.Regularity
import Tengoku.LerayHopf.LerayHopf.R3.FrechetKolmogorov
import Tengoku.LerayHopf.LerayHopf.R3.RellichBall
import Tengoku.LerayHopf.LerayHopf.R3.SpatialCompactness
import Tengoku.LerayHopf.LerayHopf.R3.WeightedFourierCommute
import Tengoku.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Topology LineDeriv

/-!
# Solution interfaces of Leray–Hopf existence on ℝ³

**Milestone R3-c — ℝ³ solution interfaces.**

Port of the Codex-approved T³ `LerayHopf/Torus/SolutionInterfaces.lean` to the whole-space
setting, reusing `DissipativeEvolution`, `WeakFormNS`, and `Time` verbatim.
The T³ 8-round audit lessons are baked in preemptively.

## Architecture

**ALL axioms are DISCHARGED — R3 capstone is KERNEL-ONLY (0 project axioms).**
SIX former project axioms are now removed: AX-SC (`spatial_compactness_R3`, THEOREM via the
Fréchet–Kolmogorov chain, issue #2), AX-G (`r3GalerkinScheme_exists`, THEOREM, issue #21),
AX-1 (`galerkin_ode_solution_R3`, discharged via the axiom-free `galerkinSolutionData_unconditional`
over `schemeOfBasis B`, issue #10), AX-4 (`r3ConvectionGapOp_exists`, PROVED sorry-free as
`r3ConvectionGapOp_holds`, issue #56), AX-2 (`aubin_lions_R3`, built axiom-free in
`AubinLionsAssembly.lean`, issue #4 PR-6), and AX-3 (`galerkin_limit_passage_R3`, PROVED as a
theorem in `LimitPassage.lean`, issue #4 PR-6).  The single extra (vs. T³) that T³ PROVED but
ℝ³ cannot supply concretely was isolated to the thin density `curlSchwartzDense_holds`
(discharged by the Fourier curl-density route, issue #3 / #21):

- **AX-G `r3GalerkinScheme_exists`** — the approximation-projection family
  (replaces T³'s proved `velocityProjection_n`); DISCHARGED (issue #21) — now a `theorem` in
  `SchwartzDivFreeBasis.lean` via `curlSchwartzDense_holds`, which is itself DISCHARGED
  (issue #3/#21, Fourier curl-density route in `CurlDensityCapstone.lean`) — no project axiom
  remains here.

The former AX-SC `spatial_compactness_R3` (local Rellich H¹(B_R)↪↪L²(B_R); replaces T³'s
proved `rellich_L2Sigma`; Rellich FAILS globally on ℝ³ but LOCAL convergence on every ball
is TRUE without tightness) is now PROVED here, not assumed.

ALL six former axioms are now discharged (AX-1 issue #10; AX-4 issue #56; AX-2 + AX-3 issue #4 PR-6):

- **AX-4 `r3_NSForms_exist` / `r3ConvectionGapOp_exists`** — PROVED (issue #56).  The named
  declaration `r3_NSForms_exist` was replaced (issue #48) by the operator-core declaration
  `r3ConvectionGapOp_exists`.  That declaration is now PROVED sorry-free as the theorem
  `r3ConvectionGapOp_holds` in `ConvectionExtension.lean` (C11, determined-form construction);
  the `r3_NSForms_exists` theorem is also moved there (rerouted from the old declaration to
  the proved theorem).  No project axiom remains for the convection operator.  `R3NSForms`
  itself is still the target type (defined below).  Mirrors torus #22 / #48.
- **AX-1 `galerkin_ode_solution_R3`** — Galerkin ODE global solution; DISCHARGED (issue #10),
  no longer an axiom — see `LerayHopf/R3/GalerkinODECapstone.lean`.
- **AX-2 `aubin_lions_R3`** — Aubin–Lions time compactness; DISCHARGED (issue #4 PR-6),
  built axiom-free in `AubinLionsAssembly.lean` via `build_galerkin_package_R3_of_galSeq`.
- **AX-3 `galerkin_limit_passage_R3`** — limit passage to weak NS solution; DISCHARGED (issue #4
  PR-6), PROVED as a theorem in `LerayHopf/R3/LimitPassage.lean` — ∀t energy inequality + weak NS
  equation + initial trace + energy class, sorry-free.

`𝔊 : R3GalerkinScheme` is threaded as a parameter throughout (cleaner than
`.some` noise).

**Formula pin (issue #56; scope note issue #153):** Preserved via `r3ConvectionGapOp_holds`
(same pin as the former axiom).  The field `b_extends` + `convFormSchwartz_eq_witness` force
`b = convIntegralSchwartz` on Schwartz triples — `b` is pinned to the canonical convection
formula.  The pin is inherited by `R3NSForms_of_gap` through its `b_galerkin` field derivation
(`b_galerkin ← b_extends + convFormSchwartz_eq_witness`), so `r3_NSForms_exists` inherits the
same pin.  Non-triviality (`b ≠ 0`) is **not** separately formalized: no concrete witness
theorem (e.g. `convIntegralSchwartz ≠ 0` on a specific Schwartz triple) is proved in this
repository.  This is a statement about the scope of the formal guarantee, not about
mathematical soundness.

**v4 de-axiomatization lesson applied:** The viscous (Stokes) form is the concrete
`stokesTestPairing_R3` — NOT axiomatized — for all `u : L2VF_R3`.

## Main definitions and theorems

- `R3GalerkinScheme`                 : structure bundling the approximation-projection family
- `r3GalerkinScheme_exists`          : THEOREM (issue #21) — existence of `R3GalerkinScheme`; discharged in `SchwartzDivFreeBasis.lean` via `curlSchwartzDense_holds` (relocated for acyclicity)
- `IsGalerkinTest_R3`                : test-function predicate for ℝ³
- `convIntegralSchwartz`             : genuine `∑_{i,a} ∫ u_a (∂_a v_i) w_i` convection integral on Schwartz fields (defined in `DivergenceFree.lean`)
- `R3NSForms`                        : structure bundling the ℝ³ NS convection form
- `r3_NSForms_exist`                 : REPLACED (issue #48) then PROVED (issue #56) — the named axiom is DEAD (no code consumers);
                                       `r3ConvectionGapOp_exists` (operator core) is PROVED as `r3ConvectionGapOp_holds` in `ConvectionExtension.lean`; proved theorem `r3_NSForms_exists` also moved there
- `R3NSForms.b_self_zero`            : proved lemma — `b u u u = 0` from antisymmetry
- `r3Evolution`                      : `DissipativeEvolution` built from `R3GalerkinScheme` + `R3NSForms`
- `GalerkinSolutionData_R3`          : structure for the n-th Galerkin ODE solution on ℝ³
- `galerkin_ode_solution_R3`         : DISCHARGED (issue #10) — was the AX-1 ODE-existence axiom; now removed, replaced by the axiom-free `galerkinSolutionData_unconditional` over `schemeOfBasis B` (`GalerkinODECapstone.lean`)
- `spatial_compactness_R3`           : THEOREM (issue #2) — ℝ³ spatial compactness LOCAL (ball-restricted, no tightness); proved via the FK chain, no axiom
- `AubinLionsPackage_R3`             : structure carrying the compactness subsequence
- `aubin_lions_R3`                   : NO LONGER AN AXIOM — Aubin–Lions discharged (issue #4, PR-6): AubinLionsPackage_R3 now built axiom-free via `AubinLionsAssembly.lean`; the old axiom name is gone from the codebase
- `galerkin_limit_passage_R3`        : NO LONGER AN AXIOM — PROVED THEOREM (issue #4, PR-6, `LimitPassage.lean`): ∀t energy inequality + weak NS solution + initial trace + energy class; project R3 axiom count = 0
- `LerayHopfSolutionFull_R3`         : proof-carrying Leray–Hopf solution structure
- `GalerkinCompactnessPackageFull_R3`: proof-carrying Galerkin compactness package
- `build_galerkin_package_R3_of_galSeq` : assembly (axiom-free core) — chains AX-2 (spatial_compactness_R3) → AX-3 from an explicit Galerkin sequence
- `exists_lerayHopf_from_package_full_R3` : lifts a package to `Nonempty (LerayHopfSolutionFull_R3 …)`
- `exists_lerayHopf_r3`    : main existence theorem — RELOCATED (issue #10) to `GalerkinODECapstone.lean`

## Assumptions

**ALL axioms discharged — R3 capstone is KERNEL-ONLY (0 project axioms).**
`#print axioms exists_lerayHopf_r3` = `[propext, Classical.choice, Quot.sound]`.
SIX former axioms are now DISCHARGED: AX-SC `spatial_compactness_R3` (issue #2, FK chain — item 4
below), AX-G `r3GalerkinScheme_exists` (issue #21 — item 1 below), AX-1
`galerkin_ode_solution_R3` (issue #10 — item 3 below; discharged downstream in
`GalerkinODECapstone.lean`), AX-4 `r3ConvectionGapOp_exists` (issue #56 — item 2 below;
proved sorry-free as `r3ConvectionGapOp_holds` in `ConvectionExtension.lean`), AX-2
`aubin_lions_R3` (issue #4, PR-6 — item 5 below; built axiom-free in `AubinLionsAssembly.lean`),
and AX-3 `galerkin_limit_passage_R3` (issue #4, PR-6 — item 6 below; proved as a theorem in
`LimitPassage.lean`).  The former fourth project axiom counted in place of AX-G is
`curlSchwartzDense_holds` (in `SchwartzDivFreeBasis.lean`), the thin density that AX-G was
swapped for; it is NOT assumed here.

1. `r3GalerkinScheme_exists` — NO LONGER AN AXIOM (DISCHARGED, issue #21). Existence of a
   Galerkin approximation-projection family on `L²_σ(ℝ³)` with smooth (Schwartz) range.  The
   `range_schwartz` field requires every element of `range (P n)` to have Schwartz component
   representatives, which is the formal content that makes `b_bound` and `reg_mem` non-vacuous
   (every Galerkin test field is Schwartz).  Since `L²(ℝ³) ⊄ 𝒮(ℝ³)` mathematically, `range_schwartz`
   entails `P n ≠ id`, but that entailment is not itself formalized as a standalone Lean fact
   here — `range_schwartz` is the field that is actually stated and used downstream.  The
   `tendsto_id` field is
   RESTRICTED to `u ∈ L2Sigma_R3` (a divergence-free Galerkin scheme is total only in
   `L²_σ(ℝ³)`; an unrestricted `∀ u : L2VF_R3` form was a latent over-strength, removed).
   Now PROVED as the `theorem` `r3GalerkinScheme_exists` in `SchwartzDivFreeBasis.lean`,
   assembled from P5 `nonempty_r3GalerkinScheme_of_basis` (`GalerkinScheme.lean`) and the
   single marked density axiom `curlSchwartzDense_holds` — the SWAP that replaced this 6-field
   structure axiom with a thin `Submodule` density `Prop` (net project-axiom count unchanged).
   Lemarié-Rieusset §2.

2. `r3_NSForms_exist` / `r3ConvectionGapOp_exists` — NO LONGER AXIOMS (PROVED, issue #56).
   The reorganization in issue #48 replaced `r3_NSForms_exist` with the operator-core axiom
   `r3ConvectionGapOp_exists` (five fields).  Issue #56 proved all five fields sorry-free via
   the determined-form construction (`ConvectionExtension.lean`, C11 `r3ConvectionGapOp_holds`):
   the BLT extension on the submodule `D = (𝒮 ⊗ L²_σ) + (L²_σ ⊗ 𝒮)` supplies `b_cont_fixedTest`
   genuinely (not as an axiom), because slot-3 Schwartz inputs land in the determined domain.
   The proved theorem `r3_NSForms_exists` (same conclusion `Nonempty (R3NSForms 𝔊)`, no
   statement weakening) is now in `ConvectionExtension.lean`.  Net: the convection operator
   contributes ZERO project axioms to the capstone.  Temam II.§1; Lemarié-Rieusset §5.

3. `galerkin_ode_solution_R3` — NO LONGER AN AXIOM (DISCHARGED, issue #10).  Picard–Lindelöf
   on the finite-dimensional approximation subspace + uniform energy and regularity bounds.
   Now PROVED unconditionally over the concrete scheme `schemeOfBasis B` via
   `galerkinSolutionData_unconditional` (`LerayHopf/R3/GalerkinODESolve.lean`), which rests on
   the proved finite-dim ODE solver `finDimGlobalODE_exists`; the capstone is rerouted through
   that data in `LerayHopf/R3/GalerkinODECapstone.lean`.  Temam III.3, Theorem 3.1.

4. `spatial_compactness_R3` — NO LONGER AN AXIOM (DISCHARGED, issue #2). ℝ³ LOCAL spatial
   compactness = local Rellich H¹(B_R)↪↪L²(B_R). Concludes convergence on every ball B_R
   (NOT global strong L²(ℝ³)); no tightness premise required. Now PROVED via
   `localCompactness_R3_of_ballCompact ∘ localRellichInput_of_frechetKolmogorov ∘
   frechetKolmogorov_holds` (the sorry-free Fréchet–Kolmogorov chain; `#print axioms`
   shows kernel axioms only). Leray 1934; Lemarié-Rieusset §6.

5. `aubin_lions_R3` — NO LONGER AN AXIOM (DISCHARGED, issue #4, PR-6). Aubin–Lions time
   compactness; spatial half supplied as the LOCAL `spatial_compactness_R3` hypothesis
   (ball-restricted convergence, no tightness).  The time-compactness half is now built
   axiom-free in `AubinLionsAssembly.lean` via `build_galerkin_package_R3_of_galSeq` (threaded
   `htest : R3TestApproxH1 𝔊`).  Temam III.2.1.

6. `galerkin_limit_passage_R3` — NO LONGER AN AXIOM (PROVED THEOREM, issue #4, PR-6).
   Limit passage from the strong-L²(0,T) subsequence to a weak NS solution with energy
   inequality, initial trace, and energy class.  Proved sorry-free in
   `LerayHopf/R3/LimitPassage.lean`: Fatou + liminf superadditivity → ∀t energy ineq;
   `weakFormNS_limit_passage` + `ae_restrict_iff'` + `intervalIntegral.integral_congr_ae`
   → weak NS equation; `strong_trace_of_props_R3` → initial trace.  Temam III.3.
-/

namespace LerayHopf

/-! ### AX-G: Galerkin approximation-projection scheme on L²_σ(ℝ³) -/

/-- The Galerkin approximation-projection family on `L²(ℝ³; ℝ³)`.

Bundles the `n`-indexed family of continuous projectors `P n : L2VF_R3 →L[ℝ] L2VF_R3`
with the five key properties needed for the Galerkin construction:

- `preserves_sigma`: each `P n` maps `L2Sigma_R3` into itself (the approximation respects
  the divergence-free constraint; follows for frequency-ball truncation or mollification);
- `tendsto_id`: `P n u → u` in `L²` as `n → ∞` **for every `u ∈ L2Sigma_R3`** (strong
  convergence of the approximation on the divergence-free subspace; Paley–Wiener
  approximation theory).  The convergence is RESTRICTED to `L2Sigma_R3`: a divergence-free
  Galerkin scheme is total only in `L²_σ(ℝ³)`, never in all of `L²(ℝ³; ℝ³)` (its prefix-span
  projections land in the closed div-free subspace, so an unrestricted `∀ u : L2VF_R3` form
  would force every `u` to be divergence-free — a latent over-strength).
  Every consumer applies `P n` only to div-free data, so the Σ-restriction is exactly what
  the Leray–Hopf assembly needs;
- `norm_le`: `‖P n u‖ ≤ ‖u‖` (non-expansiveness; follows e.g. from the fact that `P n` is
  the L² projection onto a subspace);
- `idem`: `P n ∘ P n = P n` (idempotence; `P n` is a projection);
- `range_schwartz`: every element of the range of `P n` has Schwartz component
  representatives (mathematically this entails `P n ≠ id`, since `L²(ℝ³) ⊄ Schwartz(ℝ³)`,
  though that entailment is not separately formalized here; `range_schwartz` itself ensures
  every `IsGalerkinTest_R3` field is Schwartz so `b_bound` and `reg_mem`/H¹ apply). -/
structure R3GalerkinScheme where
  /-- The n-th approximation projector. -/
  P : ℕ → (L2VF_R3 →L[ℝ] L2VF_R3)
  /-- P n preserves the divergence-free subspace. -/
  preserves_sigma : ∀ (n : ℕ) (u : L2VF_R3), u ∈ L2Sigma_R3 → P n u ∈ L2Sigma_R3
  /-- Strong convergence on the divergence-free subspace: `P n u → u` in `L²` for every
  `u ∈ L2Sigma_R3`.  The Σ-restriction is mathematically necessary — a div-free Galerkin
  scheme is total only in `L²_σ(ℝ³)`, not in all of `L²(ℝ³; ℝ³)` — and is exactly the
  range used by every consumer (`P n` is only ever applied to div-free data). -/
  tendsto_id : ∀ (u : L2VF_R3), u ∈ L2Sigma_R3 →
    Filter.Tendsto (fun n => P n u) Filter.atTop (nhds u)
  /-- Non-expansiveness: ‖P n u‖ ≤ ‖u‖. -/
  norm_le : ∀ (n : ℕ) (u : L2VF_R3), ‖P n u‖ ≤ ‖u‖
  /-- Idempotence: P n (P n u) = P n u. -/
  idem : ∀ (n : ℕ) (u : L2VF_R3), P n (P n u) = P n u
  /-- **Range regularity (Schwartz):** every element in the range of `P n` has component-wise
  Schwartz representatives.  Concretely: for every `n` and `u : L2VF_R3`, there exist
  Schwartz functions `ψ : Fin 3 → 𝓢(Domain3, ℝ)` such that the `j`-th component of
  `P n u` equals `(ψ j).toLp 2 volume`.

  Mathematically this entails `P n ≠ id` (since L²(ℝ³) ⊄ Schwartz(ℝ³)), though that entailment
  is not separately formalized as a standalone Lean fact here — `range_schwartz` is the field
  that is actually stated and used downstream: every `IsGalerkinTest_R3 𝔊 w` field is
  component-wise Schwartz, making `b_bound` (smooth-test bound) and `reg_mem` (H¹ regularity)
  non-vacuous.  Smooth/Hermite Galerkin bases satisfy this. -/
  range_schwartz : ∀ (n : ℕ) (u : L2VF_R3),
    ∃ (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
    ∀ j : Fin 3,
      L2VF_projComponent_R3 j (P n u) =
        (ψ j).toLp 2 (volume : Measure Domain3)
  /-- **Subspace nesting / eventual test-fixing.** If `w` is fixed by an earlier projector
  `P m` (i.e. `w ∈ range (P m)`), it stays fixed by all later projectors `P n`, `n ≥ m`.
  For the concrete witness (`galerkinP B n = orthogonal projection onto the nested prefix span
  `galerkinSpan B n`), this holds by `galerkinSpan_mono` + orthogonal-projection-fixes-its-subspace.
  Required for the uniform-in-`n` per-test time-derivative bound in the initial-trace route. -/
  mono_range : ∀ (m n : ℕ), m ≤ n → ∀ (w : L2VF_R3), P m w = w → P n w = w

/-! **Former axiom AX-G — now DISCHARGED (issue #21).** A Galerkin approximation-projection
family on `L²_σ(ℝ³)` exists.  No longer an axiom: it is proved as the `theorem`
`r3GalerkinScheme_exists` in `LerayHopf/R3/SchwartzDivFreeBasis.lean`, assembled from the
constructive witness P5 (`nonempty_r3GalerkinScheme_of_basis`) and the single marked density
input `curlSchwartzDense_holds`.  The proof lives downstream (it needs the witness chain,
which imports this file), so the structure `R3GalerkinScheme` stays here while its
inhabitation moves one level down the import DAG.  The capstone `exists_lerayHopf_r3`
is relocated further downstream to `LerayHopf/R3/GalerkinODECapstone.lean` (issue #10), below
both `SchwartzDivFreeBasis` and the axiom-free ODE chain it now routes through. -/

/-! ### Galerkin test predicate for ℝ³ -/

/-- A vector `w ∈ L²_σ(ℝ³)` is a **Galerkin test function** (relative to scheme `𝔊`) if
it is a fixed point of some approximation projector:
  `IsGalerkinTest_R3 𝔊 w ↔ ∃ n, 𝔊.P n (w : L2VF_R3) = (w : L2VF_R3)`.

Mirrors `IsGalerkinTest` on T³.  Every element of the range of `𝔊.P n` satisfies this.
The class is dense in `L²_σ(ℝ³)` (by `𝔊.tendsto_id`, the Σ-restricted strong convergence)
and is the standard Faedo–Galerkin
test class used in the weak NS formulation. -/
def IsGalerkinTest_R3 (𝔊 : R3GalerkinScheme) (w : L2Sigma_R3) : Prop :=
  ∃ n : ℕ, 𝔊.P n (w : L2VF_R3) = (w : L2VF_R3)

/-- The H¹(graph-norm) test-approximation property for an `R3GalerkinScheme`.

Every canonical Schwartz divergence-free test `w` is approximable, in the combined
`L² + viscousFormSq` graph seminorm, by Galerkin test fields of the scheme `𝔊`.
This is the hypothesis threaded into `galerkin_limit_passage_R3` (issue #4 PR-3/PR-4)
to bridge the `WeakFormNS` test extension step (W2): `𝔊.tendsto_id` is L²-only and
does not control `viscousFormSq_R3(P_N w − w)`.

The predicate lives here — upstream of `AubinLionsLimitPassage` and the capstone chain —
so it can be imported by both without introducing a cycle.  It is NOT a structure field
of `R3GalerkinScheme` (route decision R2 in the architect plan, issue #93). -/
def R3TestApproxH1 (𝔊 : R3GalerkinScheme) : Prop :=
  ∀ w : L2Sigma_R3, IsSchwartzDivFree_R3 w →
    ∀ ε : ℝ, 0 < ε →
      ∃ v : L2Sigma_R3, IsGalerkinTest_R3 𝔊 v ∧ IsSchwartzDivFree_R3 v ∧
        ‖(v : L2VF_R3) - (w : L2VF_R3)‖ < ε ∧
        viscousFormSq_R3 1 ((v : L2VF_R3) - (w : L2VF_R3)) < ε

/-! ### AX-4: ℝ³ Navier–Stokes forms structure -/

/-- The bundle of ℝ³ Navier–Stokes forms: only the trilinear convection form `b`
(the viscous form is the concrete `stokesTestPairing_R3`, NOT axiomatized).

Mirrors `Torus3NSForms` with `L2Sigma_R3` in place of `L2Sigma`.  The `𝔊 : R3GalerkinScheme`
parameter is threaded so that the evolution `r3Evolution 𝔊 F` can reference the Galerkin
projection `𝔊.P n`.  The pin `b_galerkin` uses Schwartz component witnesses
(`L2VF_projComponent_R3 j`) directly — independent of `𝔊` — to pin `b` to
`convIntegralSchwartz` on Schwartz div-free fields.

**Formula pin (scope note, issue #153):** `b_galerkin` pins `b` to `convIntegralSchwartz`
(the canonical `∑_{i,a} ∫ u_a (∂_a v_i) w_i` convection integral) on Schwartz div-free
fields.  Non-triviality (`b ≠ 0`) is **not** separately formalized: no concrete witness
theorem (e.g. `convIntegralSchwartz ≠ 0` on a specific Schwartz triple) is proved in this
repository.

**Antisymmetry convention:** `b u v w = -b u w v` (skew in the last two slots).

**Smooth-test convection bound:** For a **canonical Schwartz divergence-free** test `w`
(`IsSchwartzDivFree_R3 w`), `|b(u,v,w)| ≤ C(w)·‖u‖·‖v‖`.  This uses the full
(scheme-independent) test class, matching the weak NS formulation in `r3Evolution`. -/
structure R3NSForms (𝔊 : R3GalerkinScheme) where
  /-- The trilinear convection form `b : L²_σ(ℝ³) × L²_σ(ℝ³) × L²_σ(ℝ³) → ℝ`. -/
  b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
  /-- Antisymmetry in the last two slots: `b u v w = -b u w v`. -/
  b_antisymm : ∀ (u v w : L2Sigma_R3), b u v w = - b u w v
  /-- Additivity in the first slot. -/
  b_add_1 : ∀ (u u' v w : L2Sigma_R3), b (u + u') v w = b u v w + b u' v w
  /-- Additivity in the second slot. -/
  b_add_2 : ∀ (u v v' w : L2Sigma_R3), b u (v + v') w = b u v w + b u v' w
  /-- Additivity in the third slot. -/
  b_add_3 : ∀ (u v w w' : L2Sigma_R3), b u v (w + w') = b u v w + b u v w'
  /-- ℝ-homogeneity in the first slot. -/
  b_smul_1 : ∀ (c : ℝ) (u v w : L2Sigma_R3), b (c • u) v w = c * b u v w
  /-- ℝ-homogeneity in the second slot. -/
  b_smul_2 : ∀ (c : ℝ) (u v w : L2Sigma_R3), b u (c • v) w = c * b u v w
  /-- ℝ-homogeneity in the third slot. -/
  b_smul_3 : ∀ (c : ℝ) (u v w : L2Sigma_R3), b u v (c • w) = c * b u v w
  /-- **Smooth-test convection bound:** For a Schwartz divergence-free test `w`, the
  convection form is L²-bounded in the first two slots:
  `|b(u,v,w)| ≤ C(w) · ‖u‖_{L²} · ‖v‖_{L²}`.
  TRUE: `b(u,v,w) = -∫(u·∇)w·v`, so `|b| ≤ ‖∇w‖_∞ ‖u‖_{L²} ‖v‖_{L²}` with
  `‖∇w‖_∞ < ∞` for `IsSchwartzDivFree_R3 w` (Schwartz functions have all derivatives
  bounded).  Correct shape for strong-L²(0,T) convergence in the nonlinear limit passage.
  This covers the CANONICAL test class used in the weak NS formulation. -/
  b_bound : ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
    ∃ C : ℝ, ∀ (u v : L2Sigma_R3),
      |b u v w| ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖
  /-- **Formula pin:** `b` agrees with `convIntegralSchwartz` on L²_σ fields
  that are component-wise represented by Schwartz witnesses (via `L2VF_projComponent_R3`).

  Concretely: given `ψu ψv ψw : Fin 3 → 𝓢(Domain3, ℝ)` such that each component projection
  `L2VF_projComponent_R3 j (u : L2VF_R3) = (ψu j).toLp 2 volume` (and similarly for `v`, `w`),
  we require `b u v w = convIntegralSchwartz ψu ψv ψw`.

  This is the **faithful** formula pin: `convIntegralSchwartz` is the canonical
  `∑_{i,a} ∫ u_a (∂_a v_i) w_i` convection integral, not a calibration constant.
  Non-triviality (`b ≠ 0`, i.e. that the convection form does not vanish on all Schwartz
  triples) is **not** separately formalized here — that is a statement about the scope of
  this formal guarantee, not about mathematical soundness.  The Schwartz div-free set is
  dense in `L²_σ(ℝ³)`, so the pin constrains `b` on a dense subset. -/
  b_galerkin : ∀ (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (u v w : L2Sigma_R3),
    (∀ j : Fin 3,
      L2VF_projComponent_R3 j (u : L2VF_R3) =
        (ψu j).toLp 2 (volume : Measure Domain3)) →
    (∀ j : Fin 3,
      L2VF_projComponent_R3 j (v : L2VF_R3) =
        (ψv j).toLp 2 (volume : Measure Domain3)) →
    (∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) =
        (ψw j).toLp 2 (volume : Measure Domain3)) →
    b u v w = convIntegralSchwartz ψu ψv ψw

/-! ### AX-4 PROVED (issue #56) — `r3ConvectionGapOp_exists` proved as `r3ConvectionGapOp_holds`

The operator-core axiom `r3ConvectionGapOp_exists` (which replaced `r3_NSForms_exist` in
issue #48) is NOW PROVED sorry-free as the theorem `r3ConvectionGapOp_holds` in
`LerayHopf/R3/ConvectionExtension.lean` (C11, determined-form construction).  It is NO
LONGER an axiom anywhere in the codebase.

- The five `ConvectionGapOp` fields are all proved: `b` = `convFormL2_def` (C6),
  `b_extends` (C9), `b_multilinear` (C7), `b_antisymm_gap` (C8), `b_cont_fixedTest` (C10).
- `b_cont_fixedTest` is now genuinely PROVED (not assumed): for Schwartz `w`, the tensor
  `v ⊗ₜ w` lands in the determined domain `D`, so the value is the BLT-controlled quantity,
  not a Hamel value — the determined-form payoff.
- The proved theorem `r3_NSForms_exists` (same conclusion `Nonempty (R3NSForms 𝔊)`, no
  statement weakening) is also now in `ConvectionExtension.lean`.
- `R3NSForms` (the structure) remains intact — it is still the target type.
- Net project axioms for the R3 capstone: **0** — `exists_lerayHopf_r3` is KERNEL-ONLY
  (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/

/-! ### Proved lemma: b u u u = 0 -/

/-- **b(u, u, u) = 0** follows purely from antisymmetry.

Proof: `b(u, u, u) = -b(u, u, u)` by `b_antisymm u u u`, so `b(u, u, u) = 0`. -/
theorem R3NSForms.b_self_zero {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊) (u : L2Sigma_R3) :
    F.b u u u = 0 := by
  have h := F.b_antisymm u u u
  linarith

/-- The convection trilinear form vanishes when its last two arguments coincide —
the energy-estimate workhorse.

Proof: `b(u, v, v) = -b(u, v, v)` by `b_antisymm u v v`, so `b(u, v, v) = 0`. -/
theorem R3NSForms.b_self_zero_right {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊) (u v : L2Sigma_R3) :
    F.b u v v = 0 := by
  have h := F.b_antisymm u v v
  linarith

/-! ### Generic Galerkin domain instance + dissipative evolution (issue #112 PR-C) -/

/-- The ℝ³ Galerkin domain (parameterized by the scheme `𝔊`): ambient `L2VF_R3`,
divergence-free subspace `L2Sigma_R3`, projector family `𝔊.P`, and the concrete ℝ³ domain
functionals (`memH1VF_R3`, `stokesTestPairing_R3`, `viscousFormSq_R3`, test predicate
`IsSchwartzDivFree_R3`).  The reg-bound integrand is `viscousFormSq_R3 ν` (ν carried in the
functional) with RHS `½‖u₀‖²`. -/
@[reducible] noncomputable def r3Domain (𝔊 : R3GalerkinScheme) : Galerkin.Domain where
  X := L2VF_R3
  σ := L2Sigma_R3
  σ_complete := inferInstance
  P := 𝔊.P
  P_preserves_σ := 𝔊.preserves_sigma
  regMem := memH1VF_R3
  stokes := stokesTestPairing_R3
  dissip := viscousFormSq_R3
  evoReg := fun u => viscousFormSq_R3 1 u
  evoReg_nonneg := fun u => viscousFormSq_R3_nonneg zero_le_one u
  regIntegrand := viscousFormSq_R3
  regBoundRHS := fun _ _ r => (1 / 2 : ℝ) * r ^ 2
  isTest := IsSchwartzDivFree_R3

/-- The domain-neutral convection core of an `R3NSForms` (the `b_galerkin` formula pin
stays on `R3NSForms`; this is a projection onto the `NSFormCore` fields). -/
def R3NSForms.core {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊) :
    Galerkin.NSFormCore (r3Domain 𝔊) where
  b := F.b
  b_antisymm := F.b_antisymm
  b_add_1 := F.b_add_1
  b_add_2 := F.b_add_2
  b_add_3 := F.b_add_3
  b_smul_1 := F.b_smul_1
  b_smul_2 := F.b_smul_2
  b_smul_3 := F.b_smul_3
  b_bound := F.b_bound

/-! ### Domain-projection reduction lemmas (issue #112 PR-C, §6.2)

`rfl`-lemmas normalizing `r3Domain 𝔊` / `R3NSForms.core` projections back to the concrete
ℝ³ functionals, so downstream `rw`/`linarith` sites that pattern-match the concrete forms
keep working after the abbrev/extends rewiring.  (Not `@[simp]`-tagged.) -/

/-- The `DissipativeEvolution` on `L2Sigma_R3` built from an `R3GalerkinScheme` and an
`R3NSForms`, as `(r3Domain 𝔊).evolution F.core`.

`H := L2Sigma_R3`; the regularity functional is `viscousFormSq_R3 1 ∘ (↑)`, the viscous form
is the concrete `stokesTestPairing_R3`, the convection form is `F.b`, and the test predicate
is the canonical `IsSchwartzDivFree_R3` (Schwartz divergence-free class — scheme-independent),
which is the correct formulation for the whole-space Leray–Hopf weak equation.  Sorry-free:
`DissipativeEvolution` carries no Galerkin or compactness fields. -/
@[reducible] noncomputable def r3Evolution (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) :
    DissipativeEvolution :=
  (r3Domain 𝔊).evolution F.core

/-! ### AX-1: Galerkin ODE solution data on ℝ³ -/

/-- Data produced by the `n`-th Galerkin ODE on the approximation subspace of `L²_σ(ℝ³)`.

Mirrors `GalerkinSolutionData` with `𝔊.P n` for `velocityProjection_n n`, and with
`stokesTestPairing_R3`, `viscousFormSq_R3 ν`, and `memH1VF_R3`.

The `u_initial` field uses the fact that `𝔊.preserves_sigma` ensures `𝔊.P n u₀ ∈ L2Sigma_R3`.

Every field is used in the Aubin–Lions assembly or the limit passage. -/
structure GalerkinSolutionData_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    extends Galerkin.SolutionData (r3Domain 𝔊) F.core ν u₀ n where
  /-- **Weighted-Fourier continuity (finite-dim-derived enrichment).** Each weighted-Fourier
  component `s ↦ √W • 𝓕(projⱼ (u s))` (`W = (2π)²‖ξ‖²`, the `H¹`/Dirichlet-energy graph
  norm) is continuous on forward time `Ici 0`, into `L²`.

  This is NOT a new analytic assumption: on the finite-dimensional Galerkin subspace
  `Vₙ = range (𝔊.P n)` all norms are equivalent, so the `L²`-continuous Galerkin curve is also
  continuous in the (stronger) weighted/H¹ norm.  It is supplied because the abstract
  `R3GalerkinScheme` interface does not expose `Vₙ`'s finite-dimensionality; the concrete producer
  discharges it from `galerkinSpan B n` being finite-dimensional.  Consumed by the viscous/H¹
  Steklov–Jensen bound (the `n`-uniform time regularity of the Steklov averages).

  This field is R3-specific (finite-dim-derived), so `GalerkinSolutionData_R3` `extends` the
  generic `Galerkin.SolutionData` and adds it (a torus counterpart would be a vacuous invention;
  ruling (a), issue #112). -/
  viscous_curve_continuous : ∀ j : Fin 3,
    ContinuousOn (fun s => weightedFourierComponent (u s : L2VF_R3) (reg_mem s) j) (Set.Ici 0)

/-! ### AX-1 (DISCHARGED, issue #10): Galerkin ODE existence on ℝ³ — now a THEOREM

The former `axiom galerkin_ode_solution_R3` is REMOVED.  The `n`-th finite-dimensional
Galerkin ODE has a global solution unconditionally over the concrete scheme `schemeOfBasis B`
via `galerkinSolutionData_unconditional` (`LerayHopf/R3/GalerkinODESolve.lean`), which rests on
the proved finite-dim ODE solver `finDimGlobalODE_exists` (Picard–Lindelöf on the
finite-dimensional approximation subspace + the energy estimate
`‖uₙ(t)‖ ≤ ‖𝔊.P n u₀‖ ≤ ‖u₀‖`).  The capstone `exists_lerayHopf_r3` is rerouted
through that concrete data in `LerayHopf/R3/GalerkinODECapstone.lean`, so it no longer depends
on any per-scheme ODE axiom.  Temam III.3, Theorem 3.1. -/

/-! ### AX-SC: Spatial compactness on ℝ³ (LOCAL — no tightness) — now a THEOREM -/

/-! ### AX-2: Aubin–Lions compactness package on ℝ³ -/

/-- Package produced by the Aubin–Lions theorem on ℝ³.

Parameterized by `galSeq` (a Galerkin sequence from AX-1), enforcing chain faithfulness
(A1 → A2 → A3 all operate on the same sequence).  Carries: the extracted subsequence `φ`,
its strict monotonicity, a limit curve `u`, and LOCAL space-time convergence.

**LOCAL convergence:** `strong_convergence` asserts convergence in L²(0,T; L²(B_R)) for
every ball radius R — this is the form supported by the local `spatial_compactness_R3`
(no tightness needed).  The Schwartz test functions in `b_bound` have rapid decay, so
the tail outside B_R is controlled uniformly under the H¹ bound.

The spatial compactness half is NOT in this package — it is supplied as an explicit
hypothesis to `aubin_lions_R3` (the type matches `spatial_compactness_R3` exactly). -/
structure AubinLionsPackage_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ) where
  /-- The strictly monotone extraction index. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  φ_mono : StrictMono φ
  /-- The limit curve. -/
  u : Time → L2Sigma_R3
  /-- **Time-measurability of the limit curve:** `t ↦ (u t : L2VF_R3)` is
  `AEStronglyMeasurable` with respect to the Lebesgue measure restricted to `[0, T]`.

  This is the minimal time-regularity field: it asserts ONLY that the map `t ↦ u t`
  (coerced to `L2VF_R3`) is almost-everywhere strongly measurable in time — NOT
  continuity, NOT a Bochner-time-derivative, NOT a weak trace, NOT membership in an
  energy class (those belong to the good-representative layer above this package).
  It enables the a.e.-in-`t` norm-lsc transfer in `kineticEnergy_lsc_bound` (E1):
  measurability of `t ↦ ‖(u t : L2VF_R3)‖` makes `g_n(t) = ∫_{B_R} ‖uₙ t − u t‖²`
  measurable in `t`, which `TendstoInMeasure.exists_seq_tendsto_ae` needs. -/
  u_aestronglyMeasurable :
    AEStronglyMeasurable (fun t => (u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))
  /-- **LOCAL space-time convergence** of the subsequence to the limit: for every ball
  radius `R`, the ball-restricted difference `uₙ − u` converges to `0` in
  `L²(0,T; L²(B_R))`, i.e. its time-`eLpNorm` (exponent `2`, over `volume` restricted to
  `[0,T]`) tends to `0` along the subsequence `φ`.

  **eLpNorm-form (issue #31, owner-approved 2026-06-21).** This is the FAITHFUL encoding of
  L²(0,T; L²(B_R)) convergence. The earlier Bochner interval-integral form
  `∫₀ᵀ ∫_{B_R} ‖uₙ − u‖² → 0` was vacuous-shaped: Lean's `integral_undef` makes the inner
  Bochner integral `0` for non-integrable integrands, so that form was satisfiable with junk-`0`
  per-`n` integrals — it could NOT certify `MemLp (fun t => restrictToBall R (u t)) 2 …`, which
  blocks E1 (`kineticEnergy_lsc_bound`). The `eLpNorm` form has no junk-`0` collapse and carries
  exactly the intended content; it strengthens the field's *statement* (the axiom's type) without
  adding any axiom.

  This is the LOCAL form (ball-restricted via `restrictToBall`), supported by the local
  `spatial_compactness_R3` (no tightness).  Sufficient for the nonlinear limit passage since
  `b_bound` test fields are Schwartz (rapid decay controls the tail). -/
  strong_convergence : ∀ R : ℝ,
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => restrictToBall R ((galSeq (κ (φ n))).u t) - restrictToBall R (u t))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0)
  /-- **A.e.-in-t per-ball convergence** of the subsequence to the limit: for every ball
  radius `R`, for almost every `t ∈ [0,T]`, the ball-restricted Galerkin iterates
  `restrictToBall R (uₙ t)` converge to `restrictToBall R (u t)` in `L²(B_R)`.

  This is the pointwise-in-time LOCAL form, carrying the a.e.-t content directly
  (as opposed to `strong_convergence`'s integrated `eLpNorm` form).  It is used by
  the C-route lsc wall to extract pointwise weak convergence at a.e. `t`. -/
  strong_convergence_ae : ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
    Filter.Tendsto (fun n => restrictToBall R ((galSeq (κ (φ n))).u t))
      Filter.atTop (nhds (restrictToBall R (u t)))

/-! ### AX-2: Aubin–Lions on ℝ³ — former axiom `aubin_lions_R3` REMOVED (issue #15)

The former `axiom aubin_lions_R3` is GONE.  Its spatial half is genuinely PROVED axiom-free
(the `steklovAvg_spatial_extraction` chain, fed by P3), and its time half is isolated as the
strictly-thinner `galerkinSpaceTimeExtraction_R3` (the LOCAL Bochner-time compactness extraction —
per-ball a.e.-in-time L² convergence, not global; mathlib lacks the Bochner-valued
Fréchet–Kolmogorov / Aubin–Lions theorem in `L²(0,T;X)`).
The `AubinLionsPackage_R3` is now produced by `aubinLionsPackage_R3_of_timeCompactness`
(`LerayHopf/R3/AubinLionsLimitPassage.lean`), which is DOWNSTREAM of this file, so the package
assembly (`build_galerkin_package_R3_of_galSeq`) is RELOCATED to the downstream
`LerayHopf/R3/AubinLionsAssembly.lean` to stay acyclic (mirroring the #10/#24 capstone
relocation pattern).  The package structure `AubinLionsPackage_R3` itself stays defined above. -/

/-! ### AX-3 removed — `galerkin_limit_passage_R3` is now a THEOREM

The former axiom `galerkin_limit_passage_R3` (AX-3) has been **proved** and
relocated to `LerayHopf/R3/LimitPassage.lean` (issue #4 PR-6).  It now carries
the extra hypothesis `htest : R3TestApproxH1 𝔊` (the H¹-graph test-approximation
property discharged via `nonempty_schwartzGalerkinBasis_H1`).

After PR-6, `exists_lerayHopf_r3` has **zero project axioms**. -/

/-! ### Proof-carrying solution structures -/

/-- The **full Leray–Hopf solution** structure on ℝ³, carrying genuine proof fields.

All fields are typed propositions (not `Prop` placeholders):
- `weak_eq`: the curve satisfies the weak NS identity against separated-variable tests
  `ψ(t)w(x)` with `w` ranging over `IsSchwartzDivFree_R3` (the standard space-time test
  formulation is not derived from this; see `WeakFormNS`'s docstring),
- `energy_ineq`: the Leray–Hopf energy inequality on `[0, T]`,
- `initial_trace`: the initial datum is attained in the strong L² sense as `t → 0⁺` (a
  one-sided trace at the initial time only, **not** weak continuity `C_w([0,T]; L²_σ)`
  on the whole interval, which is not a field of this structure),
- `energy_class`: a.e. `memH1VF_R3` on `[0, T]` and interval-integrable viscous
  dissipation (prevents `viscousFormSq_R3 ν` collapsing off H¹, making `energy_ineq`
  non-vacuous). This is a.e.-in-time H¹ membership plus integrable dissipation, **not**
  literal Bochner membership `u ∈ L²(0,T;H¹_σ(ℝ³))`, since `u_aestronglyMeasurable` is
  strong measurability into the ambient `L2VF_R3`, not into `H¹` as a Banach space. -/
abbrev LerayHopfSolutionFull_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) :=
  Galerkin.LerayHopfSolution (r3Domain 𝔊) F.core ν T u₀

/-- The **full Galerkin compactness package** on ℝ³, carrying genuine proof fields.

Produced by `build_galerkin_package_R3_of_galSeq` (AX-2 with `spatial_compactness_R3` → AX-3,
from an explicit Galerkin sequence; the capstone supplies that sequence axiom-free over
`schemeOfBasis B` in `GalerkinODECapstone.lean`).

`energy_class_limit` proof-carries that the limit curve lies in the Leray–Hopf energy
class: a.e. `memH1VF_R3` + integrable viscous dissipation (non-vacuity of the
energy inequality). -/
abbrev GalerkinCompactnessPackageFull_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) :=
  Galerkin.CompactnessPackage (r3Domain 𝔊) F.core ν T u₀

/-! ### Assembly theorems

The package builder `build_galerkin_package_R3_of_galSeq` (which produces a
`GalerkinCompactnessPackageFull_R3` by chaining the Aubin–Lions package → AX-3 limit passage)
is RELOCATED to `LerayHopf/R3/AubinLionsAssembly.lean` (issue #15): it now consumes the proved
`aubinLionsPackage_R3_of_timeCompactness` (in `AubinLionsLimitPassage.lean`, DOWNSTREAM of this
file) instead of the removed `aubin_lions_R3` axiom, so it must sit below this file in the DAG to
stay acyclic.  `GalerkinCompactnessPackageFull_R3`, `galerkin_limit_passage_R3` (AX-3), and
`exists_lerayHopf_from_package_full_R3` remain defined here and are visible downstream. -/

/-! **Main existence theorem on ℝ³ (capstone) — RELOCATED (issue #10).**

`exists_lerayHopf_r3` now lives in `LerayHopf/R3/GalerkinODECapstone.lean`,
downstream of this file.  The relocation is forced by the issue-#10 discharge of
`galerkin_ode_solution_R3`: the capstone sources its per-`n` Galerkin sequence from the
axiom-free `galerkinSolutionData_unconditional` (`GalerkinODESolve.lean`) over the concrete
scheme `schemeOfBasis B` (with `B` from `nonempty_schwartzGalerkinBasis`).  That ODE chain
imports this file, so the capstone must sit below it in the DAG to stay acyclic.  The building
blocks it uses (`r3_NSForms_exists` — now a THEOREM in `ConvectionForm.lean` via the
thin-swap (issue #48), `build_galerkin_package_R3_of_galSeq`,
`exists_lerayHopf_from_package_full_R3`) remain defined here or in upstream imports and are
visible downstream through the import.  See `LerayHopf/Core.lean` for the axiom-free layer; `LerayHopf/R3Capstone.lean`
re-exports the relocated capstone. -/

end LerayHopf
