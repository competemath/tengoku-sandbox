/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.GRewrite.Elab

/-!

# The generalized rewriting tactic

The `grw`/`grewrite` tactic is a generalization of the `rewrite` tactic that works with relations
other than equality. The core implementation of `grewrite` is in the file
`Mathlib/Tactic/GRewrite/Core.lean`

-/

public meta section
