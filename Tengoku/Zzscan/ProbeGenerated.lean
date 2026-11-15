/-! Probe for tengoku-leakscan (competemath/tengoku, the roots guard): every root-level name of this module is one Lean generates. -/
namespace Tengoku.Zzscan
structure Foo where
  n : Nat
class Marked (α : Type) where
  mark : α
class Small (n : Nat) : Prop where
  ok : True
end Tengoku.Zzscan

open Tengoku.Zzscan

local instance : Inhabited Foo := ⟨⟨0⟩⟩
local instance : Small 0 := ⟨trivial⟩
instance : Marked Nat := ⟨0⟩
notation "probeℝ²" => (2 : Nat)
infixl:65 " +probe+ " => Nat.add
