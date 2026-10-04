/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Init
public import Lean.ScopedEnvExtension

/-!
# Helper function for environment extensions and attributes.
-/

public section

open Lean

instance {σ : Type} [Inhabited σ] : Inhabited (ScopedEnvExtension.State σ) := ⟨{state := default}⟩
