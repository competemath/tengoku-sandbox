/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku.Automatatheory.AutomataTheory.Automata.Basic

/-!
The construction of adding a history state component to an NA.
-/

open Function Set Filter Stream'

namespace Automata

section AutomataHist

variable {A H : Type}

/-- Note that in the next state, the history component can depend on both the original
and the history components of the current state, but the original component is unaffected
by the history component of the current state.
-/
def NA.addHist (M : NA A) (hist_init : Set H) (hist_next : M.State × H → A → Set H) : NA A where
  State := M.State × H
  init := { s | s.1 ∈ M.init ∧ s.2 ∈ hist_init }
  next := fun s a ↦ { s' | s'.1 ∈ M.next s.1 a ∧ s'.2 ∈ hist_next s a }

variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}

private def MakeHist (as : Stream' A) (ss : Stream' M.State) (hs0 : H) (hs' : M.State × H → A -> H) : Stream' H
  | 0 => hs0
  | k + 1 => hs' (ss k, MakeHist as ss hs0 hs' k) (as k)

end AutomataHist
