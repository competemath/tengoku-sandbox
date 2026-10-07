-- jinshi: only instdrift
/-
Jinshi fixture for `instdrift`: a theorem whose statement was elaborated with one instance, and a higher-priority instance of
the same class registered after it, so that the same text elaborates to a different term today (docs/jinshi.md). Lean's own
library only. tools/jinshi/fixtures/Instdrift.expected.tsv names what must be found; everything else here must stay quiet.
-/
namespace JinshiFixtures

class Weight (α : Type) where
  w : α → Nat

instance instA : Weight Nat := ⟨fun n => n⟩

-- elaborated with instA: `Weight.w (3 : Nat)` is 3 for the instance the theorem holds; today's synthesis picks instB
theorem drifted : Weight.w (3 : Nat) = 3 := rfl

instance (priority := high) instB : Weight Nat := ⟨fun n => n + 1⟩

-- quiet: proved with instB, the instance synthesis picks today
theorem steady : Weight.w (3 : Nat) = 4 := rfl

-- quiet: an honest theorem whose instances (instHAdd, instAddNat, instOfNatNat) are what they were
theorem plain : (3 : Nat) + 0 = 3 := rfl

end JinshiFixtures
