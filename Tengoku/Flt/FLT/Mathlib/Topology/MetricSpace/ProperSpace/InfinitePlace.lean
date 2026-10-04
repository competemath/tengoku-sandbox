/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import Tengoku

/-!
# Infinite Place

Material destined for Mathlib.
-/

@[expose] public section

open NumberField

open InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

-- TODO these should really be a proof of ProperSpace v.Completion etc
