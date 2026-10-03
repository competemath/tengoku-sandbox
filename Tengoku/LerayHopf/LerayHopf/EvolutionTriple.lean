import Tengoku.LerayHopf.LerayHopf.Torus.Basic
import Tengoku.LerayHopf.LerayHopf.EnergyEstimate
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

open MeasureTheory Filter Topology

/-!
# Abstract dissipative evolution structure and weak NS formulation

**M6 — Commit 1 (foundational layer, zero axioms).**

This file defines the abstract `DissipativeEvolution` bundle — a lightweight real
Hilbert space equipped with regularity, viscous, and convection forms — and the
`WeakFormNS` predicate expressing the weak Navier–Stokes equation.

## Main definitions

- `DissipativeEvolution`  : abstract bundle `(H, reg, viscousForm, convForm)`
- `WeakFormNS ν T E u`    : the weak NS identity for a curve `u : Time → E.H`

## Main theorems

- `DissipativeEvolution.convForm_self_zero` : `E.convForm u u u = 0` (from antisymmetry)

## Assumptions

None beyond mathlib axioms; zero `axiom`/`opaque`/`unsafe` declarations.
-/

namespace LerayHopf

/-! ### Abstract dissipative evolution bundle -/

/-- An abstract **dissipative evolution** on a real Hilbert space.

Carries only what `WeakFormNS` and the energy law need:
- a complete real inner product space `H`,
- a nonneg regularity functional `reg : H → ℝ` (playing the role of ‖·‖²_{H¹}),
- a bilinear viscous form `viscousForm : H → H → ℝ`,
- a trilinear convection form `convForm : H → H → H → ℝ` satisfying antisymmetry.

Galerkin projection, compactness, and concrete T³ constructions are NOT in this
bundle (they belong in the assembly `SolutionInterfaces.lean`, Commit 2). -/
structure DissipativeEvolution where
  /-- The real Hilbert space of velocity fields. -/
  H : Type*
  /-- NormedAddCommGroup instance on `H`. -/
  instNACG : NormedAddCommGroup H
  /-- Real inner product space instance on `H`. -/
  instIPS : InnerProductSpace ℝ H
  /-- Completeness of `H`. -/
  instCS : CompleteSpace H
  /-- Regularity functional (e.g. H¹-norm squared); plays the role of ‖·‖²_{V}. -/
  reg : H → ℝ
  /-- Nonnegativity of the regularity functional. -/
  reg_nonneg : ∀ u, 0 ≤ reg u
  /-- Viscous bilinear form (e.g. ν times the H¹ inner product). -/
  viscousForm : H → H → ℝ
  /-- Convection trilinear form. -/
  convForm : H → H → H → ℝ
  /-- Antisymmetry of the convection form in the last two arguments:
  `b(u, v, w) = -b(u, w, v)`. -/
  convForm_antisymm : ∀ u v w, convForm u v w = - convForm u w v
  /-- Predicate selecting the admissible spatial test vectors for the weak NS equation.
  Typical instance: `IsGalerkinTest w` (finite Fourier support ⇒ smooth div-free). -/
  isTest : H → Prop

/-! ### Derived lemma: convForm_self_zero -/

/-- **b(u, u, u) = 0** follows purely from antisymmetry.

Proof: `b(u, u, u) = -b(u, u, u)` by `convForm_antisymm u u u`, so `2 * b(u, u, u) = 0`,
hence `b(u, u, u) = 0`. -/
theorem DissipativeEvolution.convForm_self_zero
    (E : DissipativeEvolution) (u : E.H) :
    E.convForm u u u = 0 := by
  have h := E.convForm_antisymm u u u
  linarith

/-- The convection trilinear form vanishes when its last two arguments coincide —
the energy-estimate workhorse.

Proof: `b(u, v, v) = -b(u, v, v)` by `convForm_antisymm u v v`, so `2 * b(u, v, v) = 0`,
hence `b(u, v, v) = 0`. -/
theorem DissipativeEvolution.convForm_self_zero_right
    (E : DissipativeEvolution) (u v : E.H) :
    E.convForm u v v = 0 := by
  have h := E.convForm_antisymm u v v
  linarith

/-! ### Weak formulation of the Navier–Stokes equations -/

/-- The **weak Navier–Stokes equation** for a curve `u : Time → E.H`.

A curve `u` satisfies the weak NS equation on `(0, T)` with viscosity `ν` iff
for every test function `ψ : Time → ℝ` that is `C¹`, has compact support contained
in the open interval `(0, T)` (so boundary terms vanish), and for every spatial
test vector `w : E.H` satisfying `E.isTest w` (e.g. a smooth/Galerkin test function),
the following integral identity holds:

  `∫ t in 0..T, (-(⟪u t, w⟫_ℝ) * ψ'(t) + ψ(t) * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0`

The `tsupport ψ ⊆ Set.Ioo 0 T` condition ensures the test function vanishes at the
endpoints, so the integration-by-parts boundary terms are zero (fixing defect 2).

The `E.isTest w` condition restricts spatial tests to the admissible class
(e.g. smooth/Galerkin div-free vectors), matching the Faedo–Galerkin limit-passage
argument (Fix 3 of the Codex axiom audit).

**Side-condition design note (issue #64).** `WeakFormNS` is the distributional identity
only. It deliberately does not bundle interval-integrability or measurability side conditions
for the displayed integrand, because the current capstones package those obligations in the
domain-specific full solution structures (`LerayHopfSolutionFull` and
`LerayHopfSolutionFull_R3`) through their `energy_class` fields and in the limit-passage
layer that produces the good representative (proved theorems on both domains; no live
project axiom remains here). Public statements should therefore cite the full solution
structures, not bare `WeakFormNS`, as the weak-solution contract.

**Test-function scope note (issue #146).** The test functions here are **separated-variable**
`ψ(t) · w(x)` (a scalar temporal factor times a fixed spatial test vector), not a general
space-time test function `φ(t, x)` ranging over, e.g., `C_c^∞((0,T) × Ω)`. Whether/how this
identity relates to the standard space-time test formulation of the weak Navier–Stokes
equation is **out of scope**: this repository neither proves nor assumes an equivalence
between the two; it states and uses only the separated-variable identity above. -/
def WeakFormNS (ν T : ℝ) (E : DissipativeEvolution) (u : Time → E.H) : Prop :=
  letI := E.instNACG
  letI := E.instIPS
  ∀ (ψ : Time → ℝ), HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T →
    ContDiff ℝ 1 ψ →
  ∀ (w : E.H), E.isTest w →
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) (u t) w) * deriv ψ t +
        ψ t * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0

end LerayHopf
