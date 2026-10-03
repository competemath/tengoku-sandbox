import Tengoku.LerayHopf.LerayHopf.R3.FourierL2
import Tengoku.LerayHopf.LerayHopf.Analysis.FourierParseval

namespace LerayHopf

open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped Topology RealInnerProductSpace FourierTransform

/-!
# Stokes/viscous pairing as a fixed-Schwartz-field weak-continuous form

Extracted from `CurlDensity.lean` (issue #113 PR-2), NS-specific (not a generic `Analysis/`
module): the viscous test pairing `stokesTestPairing_R3 u w`, rewritten via Plancherel from a
gradient-weighted Fourier integral into a finite sum of `L²`-inner products of `u`'s components
against the FIXED negative-Laplacian Schwartz fields `-Δ wⱼ`. This exhibits
`stokesTestPairing_R3 (·) w` as a weakly-continuous functional in `u` — the form the
nonlinear-free viscous limit passage `B(uₙ,w) → B(u,w)` needs (consumed by
`AubinLionsLimitPassage.lean` since issue #113 PR-1).

## Declarations

- `negLapSchwartz` — the scalar negative Laplacian of a real Schwartz map (`private`, as on
  `main`)
- `fourier_schwartzC_negLap_apply` — the second-order Fourier symbol of `negLapSchwartz`
  (`private`)
- `viscousComponent_eq_inner_negLap` — per-component viscous pairing as an `L²`-inner product
  (`private`)
- `stokesTestPairing_R3_eq_sum_inner_negLap` — **the deliverable**: `stokesTestPairing_R3` as a
  finite sum of fixed-field `L²`-inner products (public, preserved qualified name — consumed by
  `AubinLionsLimitPassage.lean`)

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-! ### Viscous Plancherel–Laplacian reformulation (conjunct-2 atom (a))

The viscous test pairing `stokesTestPairing_R3 u w` is the H¹/Dirichlet pairing
`∑ⱼ ∫ (2π)²‖ξ‖² Re[𝓕uⱼ·conj 𝓕wⱼ]`, which carries a gradient weight and is therefore NOT
L²-continuous in `u` as written.  Moving the weight `(2π)²‖ξ‖²` off `𝓕u` onto `𝓕w` (Plancherel)
turns it into an honest `L²`-inner pairing against the FIXED Schwartz field `-Δw`:
`stokesTestPairing_R3 u w = ∑ⱼ ⟪uⱼ, (-Δ wⱼ)⟫_{L²}`.  Since each `-Δ wⱼ` is a fixed `L²` element
(Schwartz), this exhibits `stokesTestPairing_R3 (·) w` as a finite sum of `L²`-WEAK-continuous
functionals — the form the limit passage `B(uₙ,w) → B(u,w)` needs (it passes against the fixed
`-Δ wⱼ` by weak convergence).  The Fourier symbol is the second-order analogue of
`fourier_schwartzC_lineDeriv_apply`, iterated along each coordinate axis. -/

/-- The scalar **negative Laplacian** of a real Schwartz map, `-Δ f = -∑ₐ ∂ₐ∂ₐ f`, as a Schwartz
map (so it carries a canonical `L²`-class `(negLapSchwartz f).toLp`). -/
private noncomputable def negLapSchwartz (f : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℝ :=
  - ∑ a : Fin 3, ∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)}
      (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f)

end LerayHopf
