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
# Adic Completion

Material destined for Mathlib.
-/

@[expose] public section

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _
