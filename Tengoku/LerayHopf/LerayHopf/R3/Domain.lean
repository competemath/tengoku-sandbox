import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

open MeasureTheory

/-!
# ℝ³ spatial domain and L² function spaces

**R3-a — Domain.**

This file defines the spatial domain `Domain3 = EuclideanSpace ℝ (Fin 3)` and the
L² function spaces for the whole-space (ℝ³) Leray–Hopf theory, mirroring
`LerayHopf.Torus.Domain`, `LerayHopf.Torus.FunctionSpaces`, and the component-projection
part of `LerayHopf.Torus.DivergenceFree`, but using the Lebesgue `volume` measure on ℝ³.

## Main definitions

- `Domain3`              : ℝ³ as `EuclideanSpace ℝ (Fin 3)`
- `L2VF_R3`             : L²(ℝ³; ℝ³) — velocity fields
- `L2C_R3`              : L²(ℝ³; ℂ) — complex scalar space
- `L2VF_projComponent_R3 j`  : j-th real component projection L²(ℝ³;ℝ³) →L[ℝ] L²(ℝ³;ℝ)
- `L2VF_projComponentC_R3 j` : j-th component embedded into ℂ
-/

namespace LerayHopf

/-! ### Domain type -/

/-- The spatial domain for the whole-space theory: ℝ³ as a Euclidean space.

`EuclideanSpace ℝ (Fin 3) = PiLp 2 (fun _ : Fin 3 => ℝ)` carries
`NormedAddCommGroup`, `InnerProductSpace ℝ`, `FiniteDimensional ℝ`, and
`MeasureSpace` (Lebesgue measure via `measureSpaceOfInnerProductSpace`). -/
abbrev Domain3 := EuclideanSpace ℝ (Fin 3)

/-! ### L²(ℝ³; ℝ³) velocity fields -/

/-- L²(ℝ³; ℝ³) — Bochner L² space of ℝ³-valued velocity fields on ℝ³,
with respect to the canonical Lebesgue measure `volume`. -/
noncomputable abbrev L2VF_R3 := Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Domain3)

-- R3-a instance checks (must typecheck, not named theorems):
noncomputable example : NormedAddCommGroup L2VF_R3 := inferInstance
noncomputable example : InnerProductSpace ℝ L2VF_R3 := inferInstance
noncomputable example : CompleteSpace L2VF_R3 := inferInstance

/-! ### L²(ℝ³; ℂ) complex scalar space -/

/-- L²(ℝ³; ℂ) — complex scalar L² space with respect to `volume` on ℝ³.

Used as target for componentwise complex embedding; mirrors `L2C` in
`LerayHopf.Torus.FunctionSpaces`. -/
noncomputable abbrev L2C_R3 := Lp ℂ 2 (volume : Measure Domain3)

/-! ### Component projections -/

/-- Extract the `j`-th real component of a velocity field `u ∈ L²(ℝ³; ℝ³)` as an
element of `Lp ℝ 2 (volume : Measure Domain3)`.

Constructed by lifting the continuous projection
`EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ`
to the `Lp` level via `ContinuousLinearMap.compLpL`. -/
noncomputable def L2VF_projComponent_R3 (j : Fin 3) :
    L2VF_R3 →L[ℝ] Lp ℝ 2 (volume : Measure Domain3) :=
  (EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 (volume : Measure Domain3)

/-- Embed the `j`-th real component of a velocity field into the complex scalar space
`L2C_R3 = Lp ℂ 2 (volume : Measure Domain3)`.

Composed from the component projection and the real-to-complex embedding
`RCLike.ofRealCLM : ℝ →L[ℝ] ℂ`, both lifted to `Lp` via `compLpL`. -/
noncomputable def L2VF_projComponentC_R3 (j : Fin 3) : L2VF_R3 →L[ℝ] L2C_R3 :=
  (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) ∘L
    L2VF_projComponent_R3 j

end LerayHopf
