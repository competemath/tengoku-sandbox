import Tengoku.LerayHopf.LerayHopf.EvolutionTriple
import Tengoku

open MeasureTheory Filter Topology

/-!
# Generic Galerkin domain (issue #112, PR-C)

**Domain-neutral parameterization of the Leray–Hopf Galerkin construction.**

This file introduces the `Galerkin.Domain` bundle — the ambient `L²` Hilbert space of
vector fields, the closed divergence-free subspace, the Galerkin projector family, and the
domain functionals (regularity predicate, Stokes pairing, viscous dissipation, energy
integrands and bounds, test predicate) that parameterize the solution bundles in
`LerayHopf/Galerkin/SolutionBundles.lean`.  Both concrete geometries instantiate it:
`torusDomain` (𝕋³, `LerayHopf/Torus/SolutionInterfaces.lean`) and `r3Domain 𝔊` (ℝ³,
`LerayHopf/R3/SolutionInterfaces.lean`).

`NSFormCore` is the domain-neutral projection of the NS convection form; the per-lane
formula pins (`b_galerkin`) stay on `Torus3NSForms` / `R3NSForms` (non-triviality of the
pinned formula is not separately formalized, see issue #153).  `Domain.evolution`
assembles a `DissipativeEvolution` from a `Domain` and an `NSFormCore`.

## Main definitions

- `Galerkin.Domain`      : the ambient/subspace/projector/functional bundle
- `Galerkin.NSFormCore`  : domain-neutral trilinear convection form + algebra + smooth bound
- `Galerkin.Domain.evolution` : the `DissipativeEvolution` built from `Domain` + `NSFormCore`

## Assumptions

None beyond mathlib axioms; zero `axiom`/`opaque`/`unsafe` declarations.  The structure
field `Domain.σ_complete` carries `CompleteSpace ↥σ` (see the note on that field).
-/

namespace LerayHopf.Galerkin

/-- A Galerkin approximation domain: ambient L² Hilbert space of vector fields, closed
divergence-free subspace, projector family, and the domain functionals that
parameterize the solution bundles.  Instances: 𝕋³ (`torusDomain`) and ℝ³ (`r3Domain 𝔊`).

**`σ_complete` field (issue #112 coder note).** The `DissipativeEvolution` built by
`Domain.evolution` has carrier `↥σ`, so it needs `CompleteSpace ↥σ`.  Completeness of an
abstract submodule is NOT derivable from `CompleteSpace X` (a submodule is complete iff it
is closed), so it is carried as a structure field.  Both concrete instances discharge it
from the closed-subspace completeness instances already in the codebase
(`CompleteSpace L2Sigma` at `Torus/Leray.lean`; `CompleteSpace L2Sigma_R3` at
`R3/DivergenceFree.lean`).  This addition was anticipated by the campaign plan §3.4. -/
structure Domain where
  /-- Ambient real Hilbert space of vector fields. -/
  X : Type
  /-- NormedAddCommGroup instance on `X`. -/
  [instNACG : NormedAddCommGroup X]
  /-- Real inner product space instance on `X`. -/
  [instIPS : InnerProductSpace ℝ X]
  /-- Completeness of `X`. -/
  [instCS : CompleteSpace X]
  /-- The closed divergence-free subspace. -/
  σ : Submodule ℝ X
  /-- Completeness of the divergence-free subspace (it is closed; carried as data since it
  is not inferable from `CompleteSpace X` for an abstract submodule). -/
  σ_complete : CompleteSpace ↥σ
  /-- The Galerkin projector family. -/
  P : ℕ → X →L[ℝ] X
  /-- Each projector preserves the divergence-free subspace. -/
  P_preserves_σ : ∀ (n : ℕ) (x : X), x ∈ σ → P n x ∈ σ
  /-- Regularity predicate on ambient fields (H¹ membership). -/
  regMem : X → Prop
  /-- Stokes test-slot pairing. -/
  stokes : X → X → ℝ
  /-- ν-indexed viscous dissipation functional. -/
  dissip : ℝ → X → ℝ
  /-- The `DissipativeEvolution.reg` functional. -/
  evoReg : X → ℝ
  /-- Nonnegativity of `evoReg`. -/
  evoReg_nonneg : ∀ x, 0 ≤ evoReg x
  /-- ν-indexed integrand of the uniform regularity bound. -/
  regIntegrand : ℝ → X → ℝ
  /-- Right-hand side of the uniform regularity bound: `ν T ‖u₀‖ ↦ RHS`. -/
  regBoundRHS : ℝ → ℝ → ℝ → ℝ
  /-- Admissible spatial test predicate on the subspace. -/
  isTest : ↥σ → Prop

attribute [instance] Domain.instNACG Domain.instIPS Domain.instCS Domain.σ_complete

/-- The domain-neutral core of the NS convection form (the lane pins `b_galerkin`
stay in `Torus3NSForms`/`R3NSForms`; this is a PROJECTION, not a replacement). -/
structure NSFormCore (D : Domain) where
  /-- The trilinear convection form on the subspace. -/
  b : ↥D.σ → ↥D.σ → ↥D.σ → ℝ
  /-- Antisymmetry in the last two slots. -/
  b_antisymm : ∀ u v w, b u v w = - b u w v
  /-- Additivity in the first slot. -/
  b_add_1 : ∀ u u' v w, b (u + u') v w = b u v w + b u' v w
  /-- Additivity in the second slot. -/
  b_add_2 : ∀ u v v' w, b u (v + v') w = b u v w + b u v' w
  /-- Additivity in the third slot. -/
  b_add_3 : ∀ u v w w', b u v (w + w') = b u v w + b u v w'
  /-- ℝ-homogeneity in the first slot. -/
  b_smul_1 : ∀ (a : ℝ) u v w, b (a • u) v w = a * b u v w
  /-- ℝ-homogeneity in the second slot. -/
  b_smul_2 : ∀ (a : ℝ) u v w, b u (a • v) w = a * b u v w
  /-- ℝ-homogeneity in the third slot. -/
  b_smul_3 : ∀ (a : ℝ) u v w, b u v (a • w) = a * b u v w
  /-- Smooth-test convection bound: for an admissible test `w`, the form is L²-bounded in
  the first two slots. -/
  b_bound : ∀ w, D.isTest w → ∃ C, ∀ u v, |b u v w| ≤ C * ‖(u : D.X)‖ * ‖(v : D.X)‖

/-- The `DissipativeEvolution` on `↥D.σ` built from a `Domain` and an `NSFormCore`.

`@[reducible]` (issue #112 PR-C): the per-lane `torus3Evolution`/`r3Evolution` were reducible
direct `DissipativeEvolution` literals before this refactor; routing them through
`Domain.evolution` must keep the whole chain on the reducible fast path, otherwise
`WeakFormNS (r3Evolution …)` unfolding in the limit-passage proofs incurs a heavy
mixed-transparency whnf blowup. -/
@[reducible] noncomputable def Domain.evolution (D : Domain) (C : NSFormCore D) :
    DissipativeEvolution where
  H := ↥D.σ
  instNACG := inferInstance
  instIPS := inferInstance
  instCS := inferInstance
  reg := fun u => D.evoReg ↑u
  reg_nonneg := fun u => D.evoReg_nonneg ↑u
  viscousForm := fun u w => D.stokes ↑u ↑w
  convForm := C.b
  convForm_antisymm := C.b_antisymm
  isTest := D.isTest

end LerayHopf.Galerkin
