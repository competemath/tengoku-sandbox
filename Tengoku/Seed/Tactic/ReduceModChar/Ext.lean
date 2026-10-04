/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Init
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# `@[reduce_mod_char]` attribute

This file registers `@[reduce_mod_char]` as a `simp` attribute.
-/

public meta section

open Lean Meta

/-- `@[reduce_mod_char]` is an attribute that tags lemmas for preprocessing and cleanup in the
`reduce_mod_char` tactic -/
initialize reduceModCharExt : SimpExtension ←
  registerSimpAttr `reduce_mod_char
    "lemmas for preprocessing and cleanup in the `reduce_mod_char` tactic"
