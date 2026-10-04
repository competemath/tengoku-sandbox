/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.Category.CompHausLike.Cartesian
public import Tengoku.Seed.Topology.Category.LightProfinite.Basic

/-!
# Cartesian monoidal structure on `LightProfinite`

This file defines the cartesian monoidal structure on `LightProfinite` given by the type-theoretic
product.

-/

public section

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

end LightProfinite
