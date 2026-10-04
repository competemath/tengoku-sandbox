/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Tengoku
import Tengoku.Flt.FLT.Mathlib.Topology.MetricSpace.ProperSpace.InfinitePlace

/-!
# Infinite Place

Material destined for Mathlib.
-/

@[expose] public section

open NumberField

open InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

noncomputable instance : MeasurableSpace (v.Completion) := borel _

noncomputable instance : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ _, _))
