/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku.Automatatheory.AutomataTheory.Automata.Prod
import Tengoku.Automatatheory.AutomataTheory.Automata.Hist
import Tengoku.Automatatheory.AutomataTheory.Sequences.Temporal

/-!
The OI2 [*] construction is used to prove the closure of ω-regular langauges
under (finite) intersection.  The new accepting condition uses the 1-bit
history state to ensure that the accepting states of (M 0) and those of (M 1)
alternate with each other, so that both occur infinitely often if either occurs
infinitely often.

[*] "OI2" = "Omega Intersection of 2 automata"
-/

open Function Set Filter Stream'

namespace Automata

section AutomataOI2

open Classical

variable {A : Type} (M : Fin 2 → NA A) (acc : (i : Fin 2) → Set ((M i).State))

def NA.OI2_HistInit : Set (Fin 2) := {0}

/-- The intuitive idea is that when the history state is `i`, the OI2 NA
is waiting to see an accepting state of `Mi`, where `i` is either 0 or 1.
Once it has seen what it is waiting for, the OI2 NA toggles its history state.
-/
def NA.OI2_HistNext : (NA.Prod M).State × Fin 2 → A → Set (Fin 2) :=
  fun s _ ↦
    if s.1 0 ∈ acc 0 ∧ s.2 = 0 then {1} else
    if s.1 1 ∈ acc 1 ∧ s.2 = 1 then {0} else {s.2}

def NA.OI2 : NA A :=
  (NA.Prod M).addHist NA.OI2_HistInit (NA.OI2_HistNext M acc)

/-- A state is accepting iff the OI2 NA sees an accepting state of `Mi`
when it is waiting to see an accepting state of `Mi`, where `i` is either 0 or 1.
-/
def NA.OI2_Acc : Set (NA.OI2 M acc).State :=
  { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 } ∪ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }

end AutomataOI2
