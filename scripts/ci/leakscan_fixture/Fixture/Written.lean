/-! Root-level names someone wrote, most of them in the shape of a name Lean generates, beside two that Lean did generate (the last two commands). tengoku-leakscan reports only
those two as `root-instance:` / `root-syntax:` (expected/Written.txt) and the roots guard refuses the module for the other eleven. -/
namespace Fixture.W
class Tagged (α : Type) where
  tag : α
end Fixture.W

open Fixture.W

def fixtureWritten : Nat := 1
def instLooksGenerated : Nat := 2
def myTagged : Tagged Bool := ⟨true⟩
def instNamedLikeGenerated : Tagged Char := ⟨'a'⟩
def «instQuotedDef» : Tagged String := ⟨""⟩
instance instWrittenInstance : Tagged Unit := ⟨()⟩
instance «instQuotedInstance» : Tagged Int := ⟨0⟩
syntax (name := fixtureNamedKind) "fixture_named_kind" : term
syntax (name := termNamedLikeGenerated) "fixture_named_term" : term
syntax (name := «termQuotedKind») "fixture_quoted_term" : term
def termHandWritten : Lean.ParserDescr := Lean.ParserDescr.symbol "fixture_hand_written"
local instance : Tagged Nat := ⟨0⟩
notation "fixture∂" => (3 : Nat)
