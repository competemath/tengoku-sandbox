/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Notation.Support
public import Tengoku.Seed.Algebra.FiniteSupport.Defs
public import Tengoku.Seed.Data.Set.Finite.Basic

/-!
# Finiteness of support
-/

public section

assert_not_exists Monoid

namespace Function
variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
lemma mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun b ↦ f (a, b) :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end Function
