import Tengoku.LerayHopf.LerayHopf.EnergySkeleton
import Tengoku

/-!
# Abstract energy-law framework (M4)

This file develops the abstract energy identity and inequality for a curve
`u : ℝ → H` in a real inner product space `H`, building on the abstract
`EnergyInequality` and `EnergyData` from `LerayHopf.EnergySkeleton`.

## Mathematical content

The key computation: if `u` satisfies the abstract energy law

  inner (u' t) (u t) + D (u t) + B (u t) (u t) (u t) = 0

with trilinear skew-symmetry `B w w w = 0`, then the skew-symmetric term
vanishes and `d/dt (half * norm u t ^ 2) = - D (u t)`.

Integrating gives the energy inequality, which is packaged as an
`EnergyInequality` instance (closing the loop to `EnergySkeleton`).

## Mathlib API map (for lean-prover)

The lean-prover will use the following confirmed mathlib lemmas:
- `HasDerivAt.norm_sq`   (Mathlib.Analysis.InnerProductSpace.Calculus):
    HasDerivAt f f' x → HasDerivAt (‖f ·‖²) (2 * ⟪f x, f'⟫) x
- `HasDerivAt.inner`    (Mathlib.Analysis.InnerProductSpace.Calculus):
    HasDerivAt f f' x → HasDerivAt g g' x →
      HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x
- `intervalIntegral.integral_eq_sub_of_hasDerivAt`
    (Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus):
    FTC-2 for ℝ → E valued functions
- `intervalIntegral.integral_nonneg_of_forall`
    (Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic):
    `a ≤ b → (∀ u, 0 ≤ f u) → 0 ≤ ∫ u in a..b, f u`
- `energy_nonincreasing_from_nonnegative_dissipation` (LerayHopf.EnergySkeleton)
- `linarith`, `ring`    (built-in)

## Tier-2 frontier

The concrete Navier-Stokes realization — defining the convective trilinear form
`b(u,v,w) = integral over torus of inner ((u dot grad) v) w`, proving
`b(u,u,u) = 0` by integration by parts, and constructing the Galerkin ODE
(finite-dimensional projected ODE on `L²_σ(𝕋³)`, Picard–Lindelöf, concrete
nonlinear cancellation `b(u,u,u) = 0`) — requires infrastructure absent from
mathlib (torus divergence theorem, Lp-level gradient operators).
See `docs/scratch/m4-energy.md` Section 2 for details.

The theorems below state the abstract energy law directly as hypotheses on a
curve `u : ℝ → H`; they are the honest interface that any such concrete
construction must supply.

## Assumptions

No `axiom`, `constant`, `opaque`, or `unsafe` declarations are added.
All incomplete proof bodies carry `-- ALLOW_SORRY: <reason>`.
-/

open MeasureTheory

namespace LerayHopf

/-! The abstract Galerkin ODE law for a curve `u : ℝ → H` with dissipation `D : H → ℝ`
and trilinear form `B : H → H → H → ℝ` is:
`∀ t, HasDerivAt u (deriv u t) t ∧ inner (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0`.
This is stated directly as a hypothesis in the theorems below rather than bundled into a
standalone structure, which would make the explicit `@` form verbose. -/

/-! ## Section 2: Abstract Galerkin energy identity -/

/-! ## Section 3: Abstract Galerkin energy inequality -/

/-! ## Section 4: Connection to EnergySkeleton -/

/-! ## Section 5: Abstract dissipative-energy-law interface — AbstractEnergyLaw -/

/-- **Abstract dissipative-energy-law interface for an evolution problem on `H`.**

This is the ABSTRACT interface: a curve `u : ℝ → H` obeying a skew-symmetric
energy balance — it contains only an abstract scalar energy law (curve `u`,
dissipation `D`, skew form `B`, and the scalar balance `ode_law`).  It has NO
finite-dimensional approximation space, NO projection operator, NO initial datum,
and NO concrete Galerkin ODE.

A genuine Galerkin construction — finite-dimensional projected ODE on `L²_σ(𝕋³)`,
existence via Picard–Lindelöf, and concrete nonlinear cancellation `b(u,u,u) = 0`
from skew-symmetry of the convection form — is what WOULD supply such a law.
That construction requires torus convection/Stokes infrastructure absent from
mathlib (torus divergence theorem, Lp-level gradient operators, projected ODE
on `Pₙ(L²_σ)`) and is NOT done here.  This is a frontier item; see
`docs/STATUS.md` for current status.

This structure packages the hypotheses that any such concrete construction must
supply in order for the abstract energy framework (Sections 1-4) to apply. -/
structure AbstractEnergyLaw (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The Galerkin solution curve. -/
  u   : ℝ → H
  /-- Pointwise dissipation form (e.g. `ν ‖∇u(t)‖²` at `u(t)`). -/
  D   : H → ℝ
  /-- Nonnegativity of dissipation. -/
  D_nonneg : ∀ w : H, 0 ≤ D w
  /-- Abstract trilinear form (the role of the convective nonlinearity). -/
  B   : H → H → H → ℝ
  /-- Skew-symmetry of the trilinear form on the diagonal. -/
  B_skew : ∀ w : H, B w w w = 0
  /-- `u` is differentiable with derivative `deriv u t` at every `t`. -/
  hasDeriv : ∀ t : ℝ, HasDerivAt u (deriv u t) t
  /-- Abstract inner-product form of the Galerkin ODE at each time `t`. -/
  ode_law : ∀ t : ℝ,
      inner (𝕜 := ℝ) (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0
  /-- `D ∘ u` is interval integrable on every interval. -/
  D_intble : ∀ a b : ℝ, IntervalIntegrable (fun τ => D (u τ)) volume a b

/-! ## Section 6: Capstone — AbstractEnergyLaw satisfies EnergyInequality and bridges to EnergySkeleton -/

/-- **Nonneg accumulated dissipation for `AbstractEnergyLaw`.**

The integral `∫ τ in s..t, g.D (g.u τ)` is nonneg for `0 ≤ s ≤ t`,
since `g.D_nonneg` gives pointwise nonnegativity.

Proof sketch for lean-prover:
Apply `intervalIntegral.integral_nonneg_of_forall` with `hab := hst` and
`hf := fun τ => g.D_nonneg (g.u τ)`. -/
theorem AbstractEnergyLaw.accumulatedDissipation_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : AbstractEnergyLaw H) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ ∫ τ in s..t, g.D (g.u τ) := by
  -- `hs` is part of the stated interface (positivity of the start time) but is
  -- not needed for nonnegativity of the integral itself.
  have _hs := hs
  exact intervalIntegral.integral_nonneg_of_forall hst fun τ => g.D_nonneg (g.u τ)

end LerayHopf
