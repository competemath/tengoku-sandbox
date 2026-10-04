/-
# LerayHopf.Bochner.GelfandTriple — abstract Gelfand triple

Abstract Bochner–Sobolev-in-time / Gelfand triple foundation. `GelfandTriple.ofDissipativeEvolution`
is sorry-free (see "Scaffold ledger" below).

This is a domain-neutral foundation: it depends only on `LerayHopf.EvolutionTriple`
(the 0-axiom abstract layer) and mathlib. Both `torus3Evolution` and `r3Evolution` are
instances of `DissipativeEvolution`, so the abstract triple built here serves T³ and ℝ³
without duplication and without import cycles into either domain closure.

## Main definitions

- `GelfandTriple` — abstract Gelfand triple `V ↪ H ≅ H' ↪ V'`: two real Hilbert spaces
  `V`, `H` with a continuous, dense, injective embedding `ι : V →L[ℝ] H`. (The dual side
  `H ↪ V'` is the transpose of `ι`; we keep the structure minimal, carrying only the
  primal embedding data that Aubin–Lions and the energy law actually consume.)
- `GelfandTriple.IsOfDissipativeEvolution` — the *faithfulness contract* relating a built
  `GelfandTriple GT` to a `DissipativeEvolution E`: it pins `GT.H = E.H` (with the carried
  Hilbert instances agreeing), forces `GT.ι` to be exactly the set inclusion of the chosen
  regularity subspace `Vsub ⊆ E.H`, and ties the `V`-norm to `q`/`E.reg` via
  `‖v‖² = E.reg (ι v)`. A `GelfandTriple` for an *unrelated* space cannot satisfy it.
- `GelfandTriple.ofDissipativeEvolution` — the bridge: from a `DissipativeEvolution E`
  whose regularity functional `E.reg` is a genuine squared seminorm, carve the regularity
  space `V` (with `‖·‖² = E.reg`) sitting densely inside `H := E.H`, packaged together with
  a proof of `IsOfDissipativeEvolution` (a `Σ'`), so the returned triple is provably the
  one carved from `E` — not an arbitrary dense Hilbert embedding.

## Assumptions

No new `axiom`/`opaque`/`constant`. The genuinely-missing analytic inputs (a real **Hilbert**
regularity space `V` whose squared norm is `E.reg`, a continuous-linear embedding into `E.H`,
and density of its range) are isolated as explicit HYPOTHESIS/DATA arguments to
`ofDissipativeEvolution`, never as axioms — matching the established no-smuggle pattern (P3
`LocalRellichInput`, P2 `TimeCompactnessInput`). The Hilbert structure is taken as an explicit
`NormedAddCommGroup`/`InnerProductSpace`/`CompleteSpace` on an abstract `V` rather than
reconstructed from a seminorm: a dominated seminorm with `E.reg = q²` does not force an
inner-product/Hilbert structure, so deriving one would overclaim from insufficient inputs
(statement-gate fix). The embedding is supplied as a genuine `ContinuousLinearMap`
`ι : V →L[ℝ] E.H`, so its linearity and continuity are part of the input contract (not an
unprovable obligation against free additive/scalar instances).

## Scaffold ledger

- `GelfandTriple` — structure definition (scaffold; no proof obligation).
- `GelfandTriple.IsOfDissipativeEvolution` — `def` of the faithfulness contract (a `Prop`,
  no proof obligation; pure statement).
- `GelfandTriple.ofDissipativeEvolution` — must-prove construction returning
  `Σ' GT : GelfandTriple, GT.IsOfDissipativeEvolution …`, now **sorry-free**. The embedding is
  supplied directly as a `ContinuousLinearMap` `ι : V →L[ℝ] E.H` over an abstract Hilbert
  space `V` (the interface fix authorized by Issue #1 item 1), so `ι_linear` / `ι_continuous`
  are the CLM's own `map_add`/`map_smul`/`cont` — no reconstruction from an opaque
  `Subtype.val` against free `normV`/`ipsV` instances, which was the source of the two former
  `ALLOW_SORRY`. The regularity subspace `Vsub` is then the *derived* range
  `LinearMap.range ι` (not a free input), and the `IsOfDissipativeEvolution` faithfulness proof
  (`hH := rfl`, HEq instances, range `= Vsub` by `LinearMap.coe_range`, `‖v‖² = E.reg (ι v)`
  from `hnorm`) is fully discharged. 0 `sorry` / 0 `ALLOW_SORRY`.
-/

import Tengoku.LerayHopf.LerayHopf.EvolutionTriple
import Tengoku

namespace LerayHopf.Bochner

open scoped InnerProductSpace

/-! ### Abstract Gelfand triple `V ↪ H ≅ H' ↪ V'` -/

/-- An abstract **Gelfand triple** (also "evolution triple") `V ↪ H ≅ H' ↪ V'`.

Carries the minimal primal data consumed by the abstract Bochner-time / Aubin–Lions
library:

- a real Hilbert "regularity" space `V` (the role of `H¹_σ`; its squared norm is the
  regularity functional),
- a real Hilbert "pivot" space `H` (the role of `L²_σ`; identified with its own dual),
- a bundled continuous linear embedding `ι : V →L[ℝ] H` (linearity and continuity are part
  of the type, not separate `Prop` fields),
- **injectivity** of `ι` (so `V` is genuinely a subspace of `H`),
- **dense range** of `ι` (so `H ↪ V'` is injective on the dual side — the defining
  property that makes `(V, H, V')` a Gelfand triple rather than an arbitrary pair).

The dual space `V'` and the embedding `H ↪ V'` are NOT stored: `V'` is recovered as the
continuous dual of `V`, and `H ↪ V'` is the transpose of `ι` post-composed with the Riesz
identification `H ≅ H'`. Keeping the structure to the primal embedding avoids carrying
redundant data while leaving the full triple recoverable. No NS-specific structure
(divergence-free, convection) is encoded here (No-overclaim). -/
structure GelfandTriple where
  /-- The regularity space `V` (e.g. `H¹_σ`). -/
  V : Type*
  /-- The pivot space `H` (e.g. `L²_σ`), identified with its own dual. -/
  H : Type*
  /-- `NormedAddCommGroup` instance on `V`. -/
  instNACG_V : NormedAddCommGroup V
  /-- Real inner-product-space instance on `V`. -/
  instIPS_V : InnerProductSpace ℝ V
  /-- Completeness of `V`. -/
  instCS_V : CompleteSpace V
  /-- `NormedAddCommGroup` instance on `H`. -/
  instNACG_H : NormedAddCommGroup H
  /-- Real inner-product-space instance on `H`. -/
  instIPS_H : InnerProductSpace ℝ H
  /-- Completeness of `H`. -/
  instCS_H : CompleteSpace H
  /-- The continuous linear embedding `V →L[ℝ] H`. Linearity and continuity are bundled in the
  `ContinuousLinearMap` type, eliminating the former `ι_linear` / `ι_continuous` Prop fields. -/
  ι :
    letI := instNACG_V; letI := instIPS_V; letI := instNACG_H; letI := instIPS_H;
    V →L[ℝ] H
  /-- The embedding is injective: `V` is a genuine subspace of `H`. -/
  ι_injective :
    letI := instNACG_V; letI := instIPS_V; letI := instNACG_H; letI := instIPS_H;
    Function.Injective (ι : V → H)
  /-- The embedding has dense range: `V` is dense in `H` (equivalently, `H ↪ V'` is
  injective — the Gelfand-triple defining property). -/
  ι_denseRange :
    letI := instNACG_V; letI := instIPS_V; letI := instNACG_H; letI := instIPS_H;
    DenseRange (ι : V → H)

/-! ### Bridge: `DissipativeEvolution → GelfandTriple` -/

/-- **Faithfulness contract** tying a `GelfandTriple GT` to the data carved from a
`DissipativeEvolution E` and a regularity subspace `Vsub ⊆ E.H` with `V`-norm `q`.

A bare `GelfandTriple` carries an *anonymous* pair of Hilbert spaces with a dense
embedding; on its own it could be ANY such embedding, unrelated to `E`. This predicate is
the contract that pins it down to the triple genuinely built from `E`:

- `hH : GT.H = E.H` — the pivot space is *the same type* as `E.H` …
- `hH_inst` / `hH_ips` — … carrying `E`'s own Hilbert instances (the equality is not just
  of carriers but of the normed/inner-product structure, transported along `hH`);
- `hrange : Set.range (fun v => cast hH (GT.ι v)) = (Vsub : Set E.H)` — the embedding's
  range, viewed in `E.H`, is *exactly* the chosen regularity subspace `Vsub`. Together with
  the structural `GT.ι_injective`, this forces `GT.ι` to be the inclusion of `Vsub` (up to
  the linear iso `GT.V ≃ Vsub` that injectivity onto `Vsub` provides);
- `hnorm : ∀ v, ‖v‖ ^ 2 = E.reg (cast hH (GT.ι v))` — the `V`-norm squared *is* `E.reg`
  pulled back along the embedding, i.e. `‖v‖²_V = E.reg (ι v) = q (ι v)²`. This is the
  norm ↔ `reg` identification, made part of the *result* contract rather than only an input
  hypothesis.

No NS-specific data (divergence-free, convection) appears: the contract speaks only about
`E.H`, `E.reg`, `Vsub`, the carried inner-product structure, and the embedding. -/
def GelfandTriple.IsOfDissipativeEvolution
    (E : DissipativeEvolution)
    (Vsub : letI := E.instNACG; letI := E.instIPS; Submodule ℝ E.H)
    (GT : GelfandTriple) : Prop :=
  letI := E.instNACG; letI := E.instIPS
  letI := GT.instNACG_H; letI := GT.instIPS_H
  ∃ hH : GT.H = E.H,
    -- the carried Hilbert structure on `GT.H` is exactly `E`'s, transported along `hH`
    (HEq GT.instNACG_H E.instNACG) ∧ (HEq GT.instIPS_H E.instIPS) ∧
    -- the embedding's range is exactly the regularity subspace `Vsub` ⊆ `E.H`
    (Set.range (fun v => cast hH (GT.ι v)) = (Vsub : Set E.H)) ∧
    -- the `V`-norm squared is `E.reg` pulled back along the embedding (norm ↔ reg)
    (letI := GT.instNACG_V; ∀ v : GT.V, ‖v‖ ^ 2 = E.reg (cast hH (GT.ι v)))

/-- **Bridge construction.** From a `DissipativeEvolution E` whose regularity functional
`E.reg` is a genuine squared seminorm, build the Gelfand triple with pivot `H := E.H` and
regularity space `V` carved from the finite-regularity vectors (`‖v‖²_V = E.reg v`), sitting
densely inside `H`.

The result is a **dependent package** `Σ' GT : GelfandTriple, GT.IsOfDissipativeEvolution E Vsub`:
returning a bare `GelfandTriple` would let a proof hand back *any* dense Hilbert embedding,
so the second component is essential — it certifies that the produced triple really is the
one carved from `E` (`GT.H = E.H`, `GT.ι` is the inclusion of `Vsub`, `‖·‖²_V = E.reg ∘ ι`).

The analytic facts that mathlib does not hand us — that the regularity subspace carries a
genuine real **Hilbert** structure whose squared norm is `E.reg`, and that this subspace is
dense in `E.H` — are isolated as explicit hypotheses below, NOT as axioms (no-smuggle: each
speaks only about the given `E`/`Vsub`, asserting no downstream compactness/limit content).

**Honest Hilbert input (statement-gate fix).** A mere dominated seminorm `q` with
`E.reg = q²` does NOT force a Hilbert structure (an ℓ¹-type norm on a dense
finite-dimensional subspace satisfies nonnegativity/triangle/smul/domination yet is not the
norm of any inner-product space). We therefore take the regularity space `V` and its Hilbert
structure as **explicit input** — a real `NormedAddCommGroup`/`InnerProductSpace`/
`CompleteSpace` on an abstract type `V` — and the embedding into `E.H` as a genuine
`ContinuousLinearMap` `ι : V →L[ℝ] E.H` whose induced squared norm equals `E.reg ∘ ι`
(`hnorm`). Positive definiteness, the parallelogram law, inner-product compatibility,
linearity, and continuity are then *consequences* of the provided instances and the CLM, not
unsupported claims. (This is the interface fix authorized by Issue #1 item 1: the former
`Subtype.val`-against-free-`normV` formulation left `ι_linear`/`ι_continuous` underivable; a
`ContinuousLinearMap` input carries exactly that data.) The regularity subspace `Vsub` is the
*derived* range `LinearMap.range ι`, not a free input, so it is automatically the genuine
image of the embedding.

This is the construction that makes the whole Stream-D library apply to `torus3Evolution`
and `r3Evolution` at once.

The body — the `Σ'` package and the full faithfulness proof — is discharged (no `sorry`). -/
noncomputable def GelfandTriple.ofDissipativeEvolution
    (E : DissipativeEvolution)
    -- The abstract regularity space `V` and its EXPLICIT Hilbert structure (the honest input
    -- that a dominated seminorm cannot provide): a real normed group, a compatible real
    -- inner-product space, and completeness. These are passed as data so the constructed
    -- `GelfandTriple.V := V` genuinely IS a Hilbert space — positive definiteness, the
    -- parallelogram law, and inner-product compatibility follow from these instances rather
    -- than being conjured from `E.reg`.
    (V : Type*)
    [instNACG_V : NormedAddCommGroup V]
    [instIPS_V : InnerProductSpace ℝ V]
    [instCS_V : CompleteSpace V]
    -- The embedding `V ↪ H` supplied as a genuine `ContinuousLinearMap`: its linearity and
    -- continuity (the regularity embedding being bounded) are thus part of the input contract,
    -- not an obligation to be reconstructed from `Subtype.val` against free additive instances.
    (ι : letI := E.instNACG; letI := E.instIPS; V →L[ℝ] E.H)
    -- The embedding is injective: `V` is a genuine subspace of `H`.
    (hinj : letI := E.instNACG; Function.Injective ι)
    -- The embedding has dense range (the Gelfand-triple density property).
    (hdense : letI := E.instNACG; DenseRange ι)
    -- The Hilbert V-norm squared is exactly `E.reg` pulled back along the embedding.
    (hnorm : letI := E.instNACG; letI := E.instIPS;
      ∀ v : V, ‖v‖ ^ 2 = E.reg (ι v)) :
    letI := E.instNACG; letI := E.instIPS;
    Σ' GT : GelfandTriple, GT.IsOfDissipativeEvolution E (LinearMap.range (ι : V →ₗ[ℝ] E.H)) := by
  letI := E.instNACG; letI := E.instIPS; letI := E.instCS
  -- Build the `GelfandTriple` with `V`, `H := E.H`, embedding the CLM `ι` directly.
  refine ⟨{
      V := V
      H := E.H
      instNACG_V := instNACG_V
      instIPS_V := instIPS_V
      instCS_V := instCS_V
      instNACG_H := E.instNACG
      instIPS_H := E.instIPS
      instCS_H := E.instCS
      ι := ι
      ι_injective := hinj
      ι_denseRange := hdense }, ?_⟩
  · -- the `IsOfDissipativeEvolution` faithfulness contract.
    refine ⟨rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
    · -- range of `cast rfl ∘ ι` is exactly `Vsub := LinearMap.range ι` (by `coe_range`).
      simpa using (LinearMap.coe_range (ι : V →ₗ[ℝ] E.H)).symm
    · -- norm² = E.reg ∘ ι, by `hnorm`.
      intro v
      simpa using hnorm v

end LerayHopf.Bochner
