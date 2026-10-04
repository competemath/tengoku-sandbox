/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.Noetherian.Defs
public import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.Ideal
/-!
# Noetherian domains have unique factorization

## Main results

- IsNoetherianRing.wfDvdMonoid
-/

public section

variable {R : Type*} [CommSemiring R] [IsDomain R]

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherianRing.wfDvdMonoid [h : IsNoetherianRing R] :
    WfDvdMonoid R :=
  WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt h.wf.wellFoundedOn
