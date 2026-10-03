import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

open MeasureTheory

/-!
# Basic objects for the Leray–Hopf formalization

This file fixes the *types* the existence theory talks about — the spatial 3-torus
domain and the time axis. The torus carries the real product Haar (probability)
measure.

Interface authority (archived, historical): `docs/archive/leray_hopf_lean_mvp_plan.md`
(Milestone A/M2).
-/

namespace LerayHopf

/-- The time axis. -/
abbrev Time := ℝ

/-- The spatial 3-torus 𝕋³, realized as `UnitAddTorus (Fin 3)` = `Fin 3 → UnitAddCircle`,
with its product Haar (probability) measure.

`UnitAddCircle = AddCircle (1 : ℝ)` carries a `MeasureSpace` instance via
`AddCircle.measureSpace` (total mass 1), and the product measure on
`Fin 3 → UnitAddCircle` is provided by `MeasureTheory.MeasureSpace.pi`. -/
abbrev Torus3 := UnitAddTorus (Fin 3)

end LerayHopf
