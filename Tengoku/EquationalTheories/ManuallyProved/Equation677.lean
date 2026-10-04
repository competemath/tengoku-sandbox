-- Tengoku.EquationalTheories.ManuallyProved.Equation677: verified translations of equational_theories/ManuallyProved/Equation677.lean (2 theorems)
import Tengoku.EquationalTheories.Deps.Magma
import Lean
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

/-!
# Equation 677: Blueprint Lemmas

Formalizes lemmas from Chapter 13 of the ETP blueprint for the open
implication Equation 677 → Equation 255 on finite magmas.

* Lemma 13.1(i): Left multiplication is bijective (`eq677_leftMul_surj`, `eq677_leftMul_inj`)
* Lemma 13.1(ii): Fixer uniqueness (`eq677_fixer_unique`)
* Lemma 13.1(iii): Backward recurrence (`eq677_backward_recurrence`)
* Lemma 13.2(ii↔iii): Fixer existence ↔ E255 (`eq255_from_fixer_exists`)
* Lemma 13.2(iv): `R_x ∘ L_x` fixed-point form (`eq255_equiv_RxLx`)
* Lemma 13.2(v): `L_x ∘ R_x` fixed-point form (`eq255_equiv_LxRx`)
* Key identity (`eq677_key_identity`)
* Star equation (`eq677_star_eq`)
-/

namespace Eq677

variable {G : Type*} [Magma G]

theorem eq677_leftMul_surj (h : Equation677 G) (y : G) :
    Function.Surjective (fun x => y ◇ x)
:=
  fun x => ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

/-- The left-inverse formula: `y ◇ (x ◇ ((y ◇ x) ◇ y)) = x`.
Direct restatement of Equation 677. Blueprint Lemma 13.1(i). -/
theorem eq677_leftInv_formula (h : Equation677 G) (x y : G) :
    y ◇ (x ◇ ((y ◇ x) ◇ y)) = x :=
  (h x y).symm

theorem eq255_equiv_RxLx (h : Equation677 G) (x : G) :
    (∃ z, (x ◇ z) ◇ x = x) ↔ (∃ y, y ◇ x = x)
:= by
  constructor
  · rintro ⟨z, hz⟩; exact ⟨x ◇ z, hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ◇ ((x ◇ y) ◇ x), by rw [eq677_leftInv_formula h y x]; exact hy⟩

end Eq677

end EquationalTheories
