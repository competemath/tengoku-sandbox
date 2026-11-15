/-! Probe for tengoku-leakscan (competemath/tengoku, the roots guard): root-level names someone wrote beside generated ones. -/
namespace Tengoku.Zzscan.W
class Tagged (α : Type) where
  tag : α
end Tengoku.Zzscan.W

open Tengoku.Zzscan.W

def probeWritten : Nat := 1
def instLooksGenerated : Nat := 2
def myTagged : Tagged Bool := ⟨true⟩
syntax (name := probeNamedKind) "probe_named_kind" : term
local instance : Tagged Nat := ⟨0⟩
notation "probe∂" => (3 : Nat)
