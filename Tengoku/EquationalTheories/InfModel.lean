-- Tengoku.EquationalTheories.InfModel: verified translations of equational_theories/InfModel.lean (3 theorems)
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
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Data.Nat.Bitwise
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.Tactic.ComputeDegree
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

namespace InfModel

theorem Finite.Equation3994_implies_Equation3588 (G : Type*) [Magma G] [Finite G] (h : Equation3994 G) :
    Equation3588 G
:= by
  intro x y z
  let S := {x | ∃ a b : G, a ◇ b = x}
  have m1 : S.MapsTo (z ◇ ·) S := by
    intro
    simp [S]
  have m2 : S.MapsTo (· ◇ z) S := by
    intro
    simp [S]
  have : S.LeftInvOn (· ◇ z) (z ◇ ·) := by
    intro x hx
    simp only [Set.mem_setOf_eq, S] at hx
    obtain ⟨a, b, rfl⟩ := hx
    simp [← h]
  have t2 := this.surjOn m1
  rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t2
  have hrio := Set.InjOn.rightInvOn_of_leftInvOn t2.injOn this m2 m1
  apply (hrio _).symm
  simp [S]

theorem Equation3994_not_implies_Equation3588 : ∃ (G : Type) (_ : Magma G), Equation3994 G ∧ ¬Equation3588 G
:= by
  let magN : Magma ℕ := ⟨fun x y ↦ if Even x ∧ Even y then x ^^^ y else if Even y then y + 2
    else if Even x then x - 2 else 0⟩
  use ℕ, magN
  have range : ∀ x y : ℕ, Even (x ◇ y : ℕ) := by
    intro x y
    unfold magN
    simp
    split_ifs
    · simp_all
    · simpa [Nat.even_add]
    · by_cases x < 2
      · rw [Nat.sub_eq_zero_of_le]
        simp
        omega
      rw [Nat.even_sub]
      · simp_all
      · omega
    · exact .zero
  constructor
  · intro x y z
    generalize h : x ◇ y = v
    have : Even v := by rw [← h]; apply range
    unfold magN
    by_cases hz : Even z
    · simp [this, hz, Nat.xor_comm]
    · simp [hz, this, Nat.even_add]
  simp only [not_forall]
  use 1, 1, 1
  unfold magN
  simp

theorem Finite.Equation206_implies_Equation1648 (G : Type*) [Magma G] [Finite G] (h : Equation206 G) : Equation1648 G
:= by
  intro x y
  let S : Set G := Set.univ
  have m1 : S.MapsTo (· ◇ y) S := by
    intro
    simp [S]
  have t : S.SurjOn (· ◇ y) S := by
    intro x _
    let z := x ◇ (x ◇ y)
    use z
    simp [S, z]
    apply Eq.symm (h x y)
  rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m1] at t
  apply t.injOn (by simp [S]) (by simp [S])
  simp
  apply h (x ◇ y)

end InfModel

end EquationalTheories
