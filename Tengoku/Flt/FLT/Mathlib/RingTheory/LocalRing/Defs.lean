/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Defs

Material destined for Mathlib.
-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]

open IsLocalRing

instance IsLocalRing.quot : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
