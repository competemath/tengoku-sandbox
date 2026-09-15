-- Tengoku.EquationalTheories.Generated.FiniteImplicationSearch.theorems.InversesManual: verified translations of equational_theories/Generated/FiniteImplicationSearch/theorems/InversesManual.lean (3 theorems)
import Tengoku
import Tengoku.EquationalTheories.Deps.Magma
import Lean
import Tengoku.Data.FunLike.Basic
import Tengoku.Logic.Equiv.Basic
import Tengoku.Data.List.NodupEquivFin
import Tengoku.Data.Set.Defs
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.EquationalTheories.Deps.Superposition
import Tengoku.Data.Set.Finite.Basic
import Tengoku.Tactic.TypeStar
import Tengoku.Tactic.ByContra
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

universe uEq

set_option linter.unusedVariables false

theorem _root_.Finite.Equation1443_implies_Equation1630 (G : Type*) [Magma G] [Finite G] (h : Equation1443 G) : Equation1630 G
:= by
  have eq1443_implies_eq21374 : ∀ X Y : G, X = ((X ◇ (X ◇ Y)) ◇ (X ◇ (X ◇ Y))) :=
    fun X Y => h X (X ◇ Y) Y
  have eq21374_implies_eq1630 (X Y : G) : ((X ◇ X) ◇ ((X ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1443_implies_eq21374, eq21374_implies_eq1630]

theorem _root_.Finite.Equation1447_implies_Equation1431 (G : Type*) [Magma G] [Finite G] (h : Equation1447 G) : Equation1431 G
:= by
  have eq1447_implies_eq21413 : ∀ X Y : G, X = ((X ◇ (Y ◇ X)) ◇ (X ◇ (Y ◇ X))) :=
    fun X Y => h X (Y ◇ X) Y
  have eq21413_implies_eq1431 (X Y : G) : ((X ◇ X) ◇ (Y ◇ (X ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp only
      exact (eq1447_implies_eq21413 a Y).symm
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1447_implies_eq21413, eq21413_implies_eq1431]

theorem _root_.Finite.Equation1701_implies_Equation1884 (G : Type*) [Magma G] [Finite G] (h : Equation1701 G) : Equation1884 G
:= by
  have eq1701_implies_eq24202 : ∀ X Y : G, X = (((Y ◇ X) ◇ X) ◇ ((Y ◇ X) ◇ X)) :=
    fun X Y => h X (Y ◇ X) Y
  have eq24202_implies_1884 (X Y : G) : ((Y ◇ (X ◇ X)) ◇ (X ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1701_implies_eq24202, eq24202_implies_1884]

end EquationalTheories
