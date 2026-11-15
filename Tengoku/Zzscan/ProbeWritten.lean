/-! Probe for tengoku-leakscan (competemath/tengoku, the roots guard): root-level names someone wrote, some in the shape of a generated one, beside two generated ones. -/
namespace Tengoku.Zzscan.W
class Tagged (α : Type) where
  tag : α
end Tengoku.Zzscan.W

open Tengoku.Zzscan.W

def probeWritten : Nat := 1
def instLooksGenerated : Nat := 2
def myTagged : Tagged Bool := ⟨true⟩
def instNamedLikeGenerated : Tagged Char := ⟨'a'⟩
instance instWrittenInstance : Tagged Unit := ⟨()⟩
syntax (name := probeNamedKind) "probe_named_kind" : term
syntax (name := termNamedLikeGenerated) "probe_named_term" : term
def termHandWritten : Lean.ParserDescr := Lean.ParserDescr.symbol "probe_hand_written"
local instance : Tagged Nat := ⟨0⟩
notation "probe∂" => (3 : Nat)
