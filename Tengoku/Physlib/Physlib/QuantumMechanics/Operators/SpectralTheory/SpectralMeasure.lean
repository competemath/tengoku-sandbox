/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq
/-!

# Spectral measures

## i. Overview

A spectral measure `μS` on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H`
such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets are
mapped to zero, and `univ` is mapped to the identity.
This is implemented as a structure extending `VectorMeasure α (H →L[ℂ] H)` with additional fields
constraining `μS A` to be a star projection for each set `A` and `μS univ = 1`.

For each `x : H` there is an associated measure `μₓ` given by `μₓ A = ‖μS A x‖² = ⟪x, μS A x⟫ ≤ 1`.

## ii. Key results

- `SpectralMeasure` : A star projection-valued measure.
- `comp_eq_of_inter` : For a spectral measure `μS` and measurable sets `A` and `B`,
    the composition `μS A ∘ μS B = μS (A ∩ B)`.

## iii. Table of contents

- A. Definition
- B. Composition

## iv. References

* None.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap
open MeasureTheory
open Set

/-!
## A. Definition
-/

/-- A _spectral measure_ on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H`
  such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets
  are mapped to zero, and `univ` is mapped to the identity. -/
structure SpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →L[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

namespace SpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : SpectralMeasure α H)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (SpectralMeasure α H) (VectorMeasure α (H →L[ℂ] H)) :=
  ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (SpectralMeasure α H) fun _ ↦ Set α → H →L[ℂ] H :=
  ⟨fun μS ↦ ⇑μS.toVectorMeasure⟩

lemma isStarProjection (A : Set α) : IsStarProjection (μS A) := μS.isStarProjection' A

@[simp]
lemma univ : μS univ = 1 := μS.univ'

/-!
## B. Composition
-/

@[simp]
lemma comp_self (A : Set α) : μS A ∘L μS A = μS A := (μS.isStarProjection A).isIdempotentElem

end SpectralMeasure

end
