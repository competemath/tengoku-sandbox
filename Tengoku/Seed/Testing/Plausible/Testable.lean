/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Testing.Random.Testable
public meta import Tengoku.Seed.Logic.Basic
public import Tengoku.Seed.Tactic.Basic
public import Tengoku.Seed.Testing.Random.Gen
public meta import Tengoku.Seed.Testing.Random.Testable

/-!
This module contains `Plausible.Testable` and `Plausible.PrintableProb` instances for mathlib types.
-/

public section

namespace Plausible

namespace Testable

open TestResult

meta instance factTestable {p : Prop} [Testable p] : Testable (Fact p) where
  run cfg min := do
    let h ← runProp p cfg min
    pure <| iff fact_iff h

end Testable

section PrintableProp

meta instance Fact.printableProp {p : Prop} [PrintableProp p] : PrintableProp (Fact p) where
  printProp := printProp p

end PrintableProp

end Plausible
