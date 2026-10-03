/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Finite Adele Ring

Material destined for Mathlib.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

open IsDedekindDomain

noncomputable instance : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
