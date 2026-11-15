/-! Every root-level name of this module is one Lean generates: none is spelled where it is declared. tengoku-leakscan reports each as `root-instance:` or `root-syntax:`
(expected/Generated.txt) and the roots guard lets the module through. -/
namespace Fixture
structure Foo where
  n : Nat
class Marked (α : Type) where
  mark : α
class Small (n : Nat) : Prop where
  ok : True
end Fixture

open Fixture

local instance : Inhabited Foo := ⟨⟨0⟩⟩
local instance : Small 0 := ⟨trivial⟩
instance : Marked Nat := ⟨0⟩
deriving instance Repr for Foo
notation "fixtureℝ²" => (2 : Nat)
infixl:65 " +fixture+ " => Nat.add
macro "fixture_tac" : tactic => `(tactic| rfl)
