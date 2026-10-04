/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
Changed for Tengoku: copied from Aesop (leanprover-community/aesop at 18889deb9e83); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Aesop.Percent

public section

namespace Aesop

def unificationGoalPenalty : Percent :=
  ⟨0.8⟩

def postponedSafeRuleSuccessProbability : Percent :=
  ⟨0.9⟩

end Aesop
