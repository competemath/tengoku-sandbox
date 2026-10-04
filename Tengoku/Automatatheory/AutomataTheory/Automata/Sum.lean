/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku.Automatatheory.AutomataTheory.Automata.Basic

/-!
The indexed sum of automata, which is used to prove the closure of
both regular and ω-regular langauges under union.
Note that the theorems in this file are true even when the alphabet,
state, or index types are infinite.
-/

open Function Set Filter Stream'

namespace Automata

section AutomataSum

variable {I A : Type}

def NA.Sum (M : I → NA A) : NA A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable {M : I → NA A}

end AutomataSum

section AcceptedLangUnion

variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))

def NA.Sum_Acc : Set (NA.Sum M).State := ⋃ i : I, Sigma.mk i '' acc i

end  AcceptedLangUnion
