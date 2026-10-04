import Tengoku.LerayHopf.LerayHopf.R3.SolutionInterfaces
import Tengoku

namespace LerayHopf
open MeasureTheory SchwartzMap
open scoped Topology

/-!
# Galerkin scheme: axiom-free constructive content (P5)

**Milestone:** `p5-galerkin-scheme`

This file substantiates — axiom-free and (once `lean-prover` fills the bodies)
sorry-free — the analytic content of the `r3GalerkinScheme_exists` axiom in
`SolutionInterfaces.lean`.  It *constructs* a Galerkin approximation-projection
family from a single honest density hypothesis: the orthogonal projections onto
the finite prefix spans of a countable Schwartz, divergence-free basis.

## Architecture

This file **imports** `SolutionInterfaces.lean` (the original standalone constraint has
been lifted) so that the deliverable can directly *witness* the structure: it produces
`Nonempty R3GalerkinScheme` (`nonempty_r3GalerkinScheme_of_basis`), not merely the
field-by-field conjunction.  The connection to the axiom is now **structural**, not just
semantic.  There is NO import cycle: `SolutionInterfaces.lean` does NOT import this file
(the dependency is one-directional, SolutionInterfaces → GalerkinScheme).

The G2 over-strength previously flagged by this file (the `tendsto_id` field quantified
over all `u : L2VF_R3`, too strong for a divergence-free basis) has been **RESOLVED**, not
merely surfaced: `R3GalerkinScheme.tendsto_id` has been weakened to the honest Σ-restricted
form `∀ u, u ∈ L2Sigma_R3 → …` (a soundness fix in `SolutionInterfaces.lean`).  D5
(`galerkinP_tendsto_id`) now matches that field shape exactly.

DAG position:
```
Domain.lean
    └── DivergenceFree.lean   (L2VF_R3, L2Sigma_R3, L2VF_projComponent_R3, Domain3)
            └── … ── SolutionInterfaces.lean   (R3GalerkinScheme structure)
                    └── GalerkinScheme.lean   [THIS FILE]
                            (imports SolutionInterfaces; NOT imported by it — no cycle)
```

## Declarations (dependency order)

- `SchwartzGalerkinBasis`              : S0 — bundled honest interface (the one classical input)
- `galerkinSpan`                       : S1 — prefix span `span{e 0, …, e (n-1)}`
- `galerkinSpan_finiteDimensional`     : S2 — each prefix span is finite-dimensional
- `galerkinSpan_mono`                  : S3 — prefix spans are monotone in `n`
- `galerkinP`                          : S4 — the n-th Galerkin projector (orthogonal projection)
- `galerkinP_norm_le`                  : D1 — non-expansiveness → field `norm_le`
- `galerkinP_idem`                     : D2 — idempotence → field `idem`
- `galerkinP_mem_span`                 : D3 — range lies in the span (helper)
- `galerkinP_preserves_sigma`          : D4 — preserves `L2Sigma_R3` → field `preserves_sigma`
- `galerkinP_tendsto_id`               : D5 — strong convergence on `L2Sigma_R3` → field `tendsto_id`
- `galerkinP_range_schwartz`           : D6 — component-wise Schwartz range → field `range_schwartz`
- `galerkinScheme_properties_of_basis` : D7 — supporting lemma: conjunction of the six field properties
- `nonempty_r3GalerkinScheme_of_basis` : D7' — DELIVERABLE: `Nonempty R3GalerkinScheme` from a basis

## Statement-level note (gating note G2 — RESOLVED)

Originally the `R3GalerkinScheme.tendsto_id` field quantified over **all**
`u : L2VF_R3`, which is mathematically *too strong* for a divergence-free Galerkin
basis: such a basis is total only in `L2Sigma_R3`, not in all of `L²(ℝ³; ℝ³)`
(the Galerkin space is genuinely not dense in the full L²; its prefix-span projections
land in the closed div-free subspace, so the unrestricted form would force every `u` to
be divergence-free).  This was a latent over-strength.

It has been **RESOLVED** by a soundness fix in `SolutionInterfaces.lean`: the
`R3GalerkinScheme.tendsto_id` field is now `∀ u, u ∈ L2Sigma_R3 → …`.  D5
(`galerkinP_tendsto_id`) proves exactly that honest Σ-restricted statement, so it matches
the weakened field shape directly, and the deliverable D7' witnesses `Nonempty
R3GalerkinScheme` outright.  Verified before the fix: `tendsto_id` is never mechanically
consumed in the closure (only in prose), and every application of `𝔊.P` is on div-free
data, so the Σ-restriction is exactly what the Leray–Hopf assembly needs.

## Assumptions

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.**  The single classical input
(density of smooth/Schwartz divergence-free fields in weakly-divergence-free
`L²_σ(ℝ³)` — a Helmholtz/Weyl-lemma fact) is carried as the hypothesis field
`SchwartzGalerkinBasis.dense_span`, supplied by the caller.  It is a `Submodule`
inequality, not an assumption baked into the environment.
-/

/-! ### S0 — the bundled honest interface -/

/-- A countable Schwartz, divergence-free basis family for `L²_σ(ℝ³)` whose finite
spans exhaust `L²_σ(ℝ³)`.  This bundles the single classical input to the Galerkin
construction (existence + density of smooth div-free fields, a Helmholtz/Weyl fact)
WITHOUT proving it: it is a hypothesis, supplied by the caller. -/
structure SchwartzGalerkinBasis where
  /-- The basis vectors, as L² vector fields. -/
  e : ℕ → L2VF_R3
  /-- Each basis vector has Schwartz component representatives. -/
  e_schwartz : ∀ k : ℕ, ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ∀ j : Fin 3,
        L2VF_projComponent_R3 j (e k) = (ψ j).toLp 2 (volume : Measure Domain3)
  /-- Each basis vector is (weakly) divergence-free. -/
  e_mem_sigma : ∀ k : ℕ, e k ∈ L2Sigma_R3
  /-- The closure of the union of finite spans is all of `L²_σ(ℝ³)`:
      the basis is total in the divergence-free subspace.  This is the ONE classical
      input (density of smooth div-free fields in weakly-div-free L²_σ). -/
  dense_span :
      (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
        (⨆ n : ℕ, Submodule.span ℝ (Set.range (fun k : Fin n => e (k : ℕ)))).topologicalClosure

/-! ### S1 — prefix spans -/

/-- Prefix span `span{e 0, …, e (n-1)}` of the basis. -/
noncomputable def galerkinSpan (B : SchwartzGalerkinBasis) (n : ℕ) :
    Submodule ℝ L2VF_R3 :=
  Submodule.span ℝ (Set.range (fun k : Fin n => B.e (k : ℕ)))

/-! ### S2 — finite dimensionality -/

-- Proof sketch: `FiniteDimensional.span_of_finite (Set.finite_range _)`.
/-- The prefix span `galerkinSpan B n`, being spanned by a finite generating set, is
finite-dimensional (S2). -/
instance galerkinSpan_finiteDimensional (B : SchwartzGalerkinBasis) (n : ℕ) :
    FiniteDimensional ℝ (galerkinSpan B n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- A finite-dimensional subspace is complete, hence has an orthogonal projection (Gating
note G1). This explicit instance guarantees `galerkinP` (S4) typechecks even if the
`HasOrthogonalProjection` instance does not synthesize transitively from S2. -/
instance galerkinSpan_hasOrthogonalProjection (B : SchwartzGalerkinBasis) (n : ℕ) :
    (galerkinSpan B n).HasOrthogonalProjection :=
  inferInstance

/-! ### S3 — monotonicity -/

-- Proof sketch: span is monotone in the generating set; the `Fin n` range is contained
-- in the `Fin m` range for `n ≤ m`, so `Submodule.span_mono`.
/-- The prefix spans `galerkinSpan B` are monotone in `n` (S3): more generators only grow
the span. -/
theorem galerkinSpan_mono (B : SchwartzGalerkinBasis) : Monotone (galerkinSpan B) := by
  intro n m hnm
  refine Submodule.span_mono ?_
  rintro x ⟨k, rfl⟩
  exact ⟨⟨(k : ℕ), lt_of_lt_of_le k.isLt hnm⟩, rfl⟩

/-! ### S4 — the projector family -/

/-- The n-th Galerkin projector: orthogonal projection onto `galerkinSpan B n`. -/
noncomputable def galerkinP (B : SchwartzGalerkinBasis) (n : ℕ) :
    L2VF_R3 →L[ℝ] L2VF_R3 :=
  (galerkinSpan B n).starProjection

/-! ### D1 — non-expansiveness (field `norm_le`) -/

-- Proof sketch: exact `Submodule.norm_starProjection_apply_le`.
/-- The Galerkin projector `galerkinP B n` is non-expansive (D1, field `norm_le`): it never
increases the `L²` norm. -/
theorem galerkinP_norm_le (B : SchwartzGalerkinBasis) (n : ℕ) (u : L2VF_R3) :
    ‖galerkinP B n u‖ ≤ ‖u‖ :=
  Submodule.norm_starProjection_apply_le _ u

/-! ### D2 — idempotence (field `idem`) -/

-- Proof sketch: from `Submodule.isIdempotentElem_starProjection`
-- (`IsIdempotentElem f` ↔ `f ∘ f = f`); apply at `u`.
/-- The Galerkin projector `galerkinP B n` is idempotent (D2, field `idem`). -/
theorem galerkinP_idem (B : SchwartzGalerkinBasis) (n : ℕ) (u : L2VF_R3) :
    galerkinP B n (galerkinP B n u) = galerkinP B n u := by
  have h := (galerkinSpan B n).isIdempotentElem_starProjection
  exact congrFun (congrArg DFunLike.coe h) u

/-! ### D3 — range lies in the span (helper for D4 and D6) -/

-- Proof sketch: `Submodule.starProjection_apply_mem`.
/-- The Galerkin projector `galerkinP B n` lands in the prefix span `galerkinSpan B n` (D3,
used to derive D4 and D6). -/
theorem galerkinP_mem_span (B : SchwartzGalerkinBasis) (n : ℕ) (u : L2VF_R3) :
    galerkinP B n u ∈ galerkinSpan B n :=
  Submodule.starProjection_apply_mem _ u

/-! ### D4 — preserves the divergence-free subspace (field `preserves_sigma`) -/

-- Proof sketch: `galerkinP B n u ∈ galerkinSpan B n` (D3); and
-- `galerkinSpan B n ≤ L2Sigma_R3` because all generators `B.e k ∈ L2Sigma_R3`
-- (`B.e_mem_sigma`) and `L2Sigma_R3` is a submodule, so `Submodule.span_le.mpr`.
-- The hypothesis `_hu` is not actually needed (range ⊆ span ⊆ Σ regardless), but it
-- is part of the `R3GalerkinScheme.preserves_sigma` field signature, so keep it for the
-- assembly statement (underscore-named since the proof discards it).
/-- The Galerkin projector `galerkinP B n` preserves the divergence-free subspace `L2Sigma_R3`
(D4, field `preserves_sigma`). -/
theorem galerkinP_preserves_sigma (B : SchwartzGalerkinBasis) (n : ℕ) (u : L2VF_R3)
    (_hu : u ∈ L2Sigma_R3) : galerkinP B n u ∈ L2Sigma_R3 := by
  have hspan : galerkinSpan B n ≤ L2Sigma_R3 := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨k, rfl⟩
    exact B.e_mem_sigma _
  exact hspan (galerkinP_mem_span B n u)

/-! ### D5 — strong convergence on `L2Sigma_R3` (field `tendsto_id`, honest form) -/

-- Proof sketch: `Submodule.starProjection_tendsto_closure_iSup (galerkinSpan B)
-- (galerkinSpan_mono B) u` gives convergence to the closure-projection of `u`; since
-- `u ∈ L2Sigma_R3 ≤ closure(⨆ galerkinSpan B n)` (`B.dense_span`), `u` is fixed by the
-- closure projection (`starProjection_eq_self_iff`), so the limit is `u`.
-- See gating note G2 in the header: the restricted `hu : u ∈ L2Sigma_R3` form is the
-- honest statement; the unrestricted `∀ u : L2VF_R3` field is too strong for a div-free
-- basis and is intentionally NOT claimed here.
/-- The Galerkin projectors converge strongly to the identity on `L2Sigma_R3` (D5, field
`tendsto_id`, honest restricted form — see gating note G2: the unrestricted `∀ u : L2VF_R3`
statement is too strong for a divergence-free basis and is intentionally not claimed). -/
theorem galerkinP_tendsto_id (B : SchwartzGalerkinBasis) (u : L2VF_R3)
    (hu : u ∈ L2Sigma_R3) :
    Filter.Tendsto (fun n => galerkinP B n u) Filter.atTop (𝓝 u) := by
  -- `u` lies in the closure of `⨆ n, galerkinSpan B n` via `B.dense_span`.
  have huc : u ∈ (⨆ n : ℕ, galerkinSpan B n).topologicalClosure := B.dense_span hu
  -- Closure of a submodule of the complete space `L2VF_R3` is complete, hence has an
  -- orthogonal projection.
  haveI : (⨆ n : ℕ, galerkinSpan B n).topologicalClosure.HasOrthogonalProjection := by
    have hclosed : IsClosed
        ((⨆ n : ℕ, galerkinSpan B n).topologicalClosure : Set L2VF_R3) :=
      (⨆ n : ℕ, galerkinSpan B n).isClosed_topologicalClosure
    haveI : CompleteSpace
        ((⨆ n : ℕ, galerkinSpan B n).topologicalClosure) :=
      hclosed.completeSpace_coe
    infer_instance
  have hlim := Submodule.starProjection_tendsto_closure_iSup
    (galerkinSpan B) (galerkinSpan_mono B) u
  -- The closure-projection fixes `u`, since `u` is in the closure.
  have hfix : (⨆ n : ℕ, galerkinSpan B n).topologicalClosure.starProjection u = u :=
    Submodule.starProjection_eq_self_iff.mpr huc
  rw [hfix] at hlim
  exact hlim

/-! ### D6 — component-wise Schwartz range (field `range_schwartz`) -/

/-- The predicate "the L² vector field `v` has Schwartz component representatives".
This is the motive propagated through `Submodule.span_induction` in D6. -/
private def HasSchwartzComponents (v : L2VF_R3) : Prop :=
  ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
    ∀ j : Fin 3, L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)

-- Proof sketch: components are `0 = (0 : 𝓢).toLp` via `map_zero` of
-- `L2VF_projComponent_R3 j` and of `toLpCLM`.
private theorem hasSchwartzComponents_zero : HasSchwartzComponents 0 := by
  refine ⟨fun _ => 0, fun j => ?_⟩
  rw [map_zero]
  rw [show ((0 : SchwartzMap Domain3 ℝ).toLp 2 (volume : Measure Domain3))
        = SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3) 0 from rfl, map_zero]

-- Proof sketch: components add; `(ψ j).toLp + (ψ' j).toLp = (ψ j + ψ' j).toLp` by
-- `map_add (toLpCLM ℝ ℝ 2 volume)`; Schwartz closed under `+`; push through the CLM
-- `L2VF_projComponent_R3 j` via `map_add`.
private theorem hasSchwartzComponents_add {v w : L2VF_R3}
    (hv : HasSchwartzComponents v) (hw : HasSchwartzComponents w) :
    HasSchwartzComponents (v + w) := by
  obtain ⟨ψ, hψ⟩ := hv
  obtain ⟨ψ', hψ'⟩ := hw
  refine ⟨fun j => ψ j + ψ' j, fun j => ?_⟩
  rw [map_add, hψ j, hψ' j]
  rw [show ((ψ j).toLp 2 (volume : Measure Domain3))
        = SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3) (ψ j) from rfl,
      show ((ψ' j).toLp 2 (volume : Measure Domain3))
        = SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3) (ψ' j) from rfl,
      show ((ψ j + ψ' j).toLp 2 (volume : Measure Domain3))
        = SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3) (ψ j + ψ' j) from rfl,
      map_add]

-- Proof sketch: `c • (ψ j).toLp = (c • ψ j).toLp` by `map_smul (toLpCLM ℝ ℝ 2 volume)`;
-- Schwartz is an ℝ-module; push through the CLM `L2VF_projComponent_R3 j` via `map_smul`.
-- Gating note G3: supply the `𝕜 = ℝ` slot to `toLpCLM`/`map_smul` if needed.
private theorem hasSchwartzComponents_smul (c : ℝ) {v : L2VF_R3}
    (hv : HasSchwartzComponents v) : HasSchwartzComponents (c • v) := by
  obtain ⟨ψ, hψ⟩ := hv
  refine ⟨fun j => c • ψ j, fun j => ?_⟩
  rw [map_smul, hψ j]
  rw [show ((ψ j).toLp 2 (volume : Measure Domain3))
        = SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3) (ψ j) from rfl,
      show ((c • ψ j).toLp 2 (volume : Measure Domain3))
        = SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3) (c • ψ j) from rfl,
      map_smul]

-- Proof sketch: exactly `B.e_schwartz k`.
private theorem hasSchwartzComponents_of_basis (B : SchwartzGalerkinBasis) (k : ℕ) :
    HasSchwartzComponents (B.e k) :=
  B.e_schwartz k

-- Proof sketch:
-- 1. `galerkinP B n u ∈ galerkinSpan B n` (D3).
-- 2. `Submodule.span_induction` over that membership with motive `HasSchwartzComponents`,
--    using `hasSchwartzComponents_of_basis` (generators), `hasSchwartzComponents_zero`,
--    `hasSchwartzComponents_add`, `hasSchwartzComponents_smul`.
-- No vector-valued Schwartz construction is needed: the proof stays at the
-- `L2VF_projComponent_R3 j (·) = (·).toLp` level throughout.
/-- The image of the Galerkin projector `galerkinP B n` has Schwartz component representatives
in every coordinate (D6, field `range_schwartz`) — inherited from the basis vectors via
`Submodule.span_induction`. -/
theorem galerkinP_range_schwartz (B : SchwartzGalerkinBasis) (n : ℕ) (u : L2VF_R3) :
    ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ∀ j : Fin 3,
        L2VF_projComponent_R3 j (galerkinP B n u) =
          (ψ j).toLp 2 (volume : Measure Domain3) := by
  have hmem : galerkinP B n u ∈ galerkinSpan B n := galerkinP_mem_span B n u
  have key : HasSchwartzComponents (galerkinP B n u) := by
    refine Submodule.span_induction
      (p := fun v _ => HasSchwartzComponents v)
      ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨k, rfl⟩
      exact hasSchwartzComponents_of_basis B (k : ℕ)
    · exact hasSchwartzComponents_zero
    · intro x y _ _ hx hy
      exact hasSchwartzComponents_add hx hy
    · intro a x _ hx
      exact hasSchwartzComponents_smul a hx
  exact key

/-! ### D6b — subspace nesting for the concrete projector (field `mono_range`) -/

/-- **Nesting for the concrete projector.** A point fixed by `galerkinP B m` stays fixed by
`galerkinP B n` for `n ≥ m` (its subspace `galerkinSpan B m ⊆ galerkinSpan B n` and the
orthogonal projection fixes points of its subspace). Discharges `R3GalerkinScheme.mono_range`. -/
theorem galerkinP_mono_range (B : SchwartzGalerkinBasis) :
    ∀ (m n : ℕ), m ≤ n → ∀ (w : L2VF_R3), galerkinP B m w = w → galerkinP B n w = w := by
  intro m n hmn w hw
  -- `galerkinP B m w ∈ galerkinSpan B m`; rewrite by `hw` to get `w ∈ galerkinSpan B m`
  have hw_mem_m : w ∈ galerkinSpan B m := hw ▸ galerkinP_mem_span B m w
  -- prefix spans are nested: `galerkinSpan B m ≤ galerkinSpan B n`
  have hw_mem_n : w ∈ galerkinSpan B n := galerkinSpan_mono B hmn hw_mem_m
  -- orthogonal projection fixes points of its subspace
  exact Submodule.starProjection_eq_self_iff.mpr hw_mem_n

/-! ### D7 — supporting lemma (six field properties) -/

/-- **Supporting lemma (P5).** From a total Schwartz divergence-free basis, the orthogonal
projections onto its finite prefix spans form a Galerkin approximation scheme on
`L²_σ(ℝ³)`: they are non-expansive, idempotent, preserve the divergence-free subspace,
have component-wise Schwartz range, and converge strongly to the identity on
`L²_σ(ℝ³)`.  This is the axiom-free constructive content of `r3GalerkinScheme_exists`
(modulo the bundled density hypothesis `B.dense_span`), packaged field-by-field; the
headline deliverable `nonempty_r3GalerkinScheme_of_basis` (D7') assembles these into an
actual `R3GalerkinScheme`.

The `tendsto_id` conjunct is the Σ-restricted form, which (after the soundness fix in
`SolutionInterfaces.lean`) now matches the `R3GalerkinScheme.tendsto_id` field exactly: a
divergence-free basis is total only in `L2Sigma_R3`, so convergence is claimed precisely
where it is true. -/
theorem galerkinScheme_properties_of_basis (B : SchwartzGalerkinBasis) :
    (∀ n u, u ∈ L2Sigma_R3 → galerkinP B n u ∈ L2Sigma_R3)            -- preserves_sigma
  ∧ (∀ u, u ∈ L2Sigma_R3 →
        Filter.Tendsto (fun n => galerkinP B n u) Filter.atTop (𝓝 u)) -- tendsto_id (honest, on Σ)
  ∧ (∀ n u, ‖galerkinP B n u‖ ≤ ‖u‖)                                  -- norm_le
  ∧ (∀ n u, galerkinP B n (galerkinP B n u) = galerkinP B n u)        -- idem
  ∧ (∀ n u, ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ, ∀ j,
        L2VF_projComponent_R3 j (galerkinP B n u) =
          (ψ j).toLp 2 (volume : Measure Domain3)) :=
  ⟨galerkinP_preserves_sigma B,
   fun u hu => galerkinP_tendsto_id B u hu,
   galerkinP_norm_le B,
   galerkinP_idem B,
   galerkinP_range_schwartz B⟩

/-! ### D7' — DELIVERABLE: witness `Nonempty R3GalerkinScheme` -/

/-- **Deliverable (P5).** From a total Schwartz divergence-free basis `B`, the orthogonal
projections onto its finite prefix spans assemble into an actual `R3GalerkinScheme`.  This
is the axiom-free constructive witness of the `r3GalerkinScheme_exists` axiom: the only
input is the bundled density hypothesis `B.dense_span` (a Helmholtz/Weyl-lemma fact carried
as a hypothesis, not axiomatized).

D5 (`galerkinP_tendsto_id`) now matches the weakened `R3GalerkinScheme.tendsto_id` field
shape `∀ u, u ∈ L2Sigma_R3 → Tendsto …` exactly, so the assembly is direct. -/
theorem nonempty_r3GalerkinScheme_of_basis (B : SchwartzGalerkinBasis) :
    Nonempty R3GalerkinScheme := by
  -- Proof sketch: assemble
  --   ⟨{ P               := galerkinP B,
  --      preserves_sigma := galerkinP_preserves_sigma B,        -- (D4)
  --      tendsto_id      := galerkinP_tendsto_id B,             -- (D5, now matches the weakened field)
  --      norm_le         := galerkinP_norm_le B,                -- (D1)
  --      idem            := galerkinP_idem B,                   -- (D2)
  --      range_schwartz  := galerkinP_range_schwartz B          -- (D6)
  --      mono_range      := galerkinP_mono_range B }⟩           -- (D6b)
  exact ⟨{
    P               := galerkinP B
    preserves_sigma := galerkinP_preserves_sigma B
    tendsto_id      := fun u hu => galerkinP_tendsto_id B u hu
    norm_le         := galerkinP_norm_le B
    idem            := galerkinP_idem B
    range_schwartz  := galerkinP_range_schwartz B
    mono_range      := galerkinP_mono_range B }⟩

end LerayHopf
