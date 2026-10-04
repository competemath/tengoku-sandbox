-- Tengoku.EquationalTheories.StringMagmas: verified translations of equational_theories/StringMagmas.lean (1 theorem)
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
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

namespace StringMagmas

private abbrev M : Type := List Nat

private def M.mul (a b : M) : M :=
  if a = b then b else
  if (b ++ b ++ b) <:+ a then b else a ++ b

scoped infix:70 " * " => M.mul

private theorem M.mul_def (a b : M) : a * b =
    if a = b then b else
    if (b ++ b ++ b) <:+ a then b else a ++ b :=
  rfl

@[simp]
private theorem M.mul_self (a : M) : a * a = a := by
  simp [M.mul_def a a]

private theorem Msat3102 (x y : M) : x = (((y * x) * x) * x) * x := by
  rw [M.mul_def y x]
  split
  · next h => simp
  next h =>
  split
  · next h => simp
  rw [M.mul_def (y ++ x) x]
  split
  · next h => simp
  next h =>
  split
  · next h => simp
  rw [M.mul_def (y ++ x ++ x) x]
  split
  · next h => simp
  next h =>
  split
  · next h => simp
  rw [M.mul_def _ x]
  split
  · next h => simp
  next h =>
  rw [if_pos]
  repeat rw [List.append_assoc]
  exact List.suffix_append y (x ++ (x ++ x))

/-- `M` does not satisfy 3176 -/
private theorem Mnot3176 : ∃ (x y z : M), x ≠ (((y * z) * x) * x) * x := by
  exists [0], [1], [2]

theorem Equation3102_not_implies_Equation3176 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation3176 G
:= by
  refine ⟨M, ⟨M.mul⟩, Msat3102, ?_⟩
  · unfold Equation3176
    push Not
    exact Mnot3176

end StringMagmas

end EquationalTheories
