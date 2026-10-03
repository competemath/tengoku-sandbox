/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Native measure semantics for polynomial free monads

This module interprets a polynomial free program directly as a Mathlib `Measure`. Each operation
is assigned a probability measure on its answer type, and `PFunctor.FreeM.denote` recursively
composes those measures with `Measure.bind`.

`Measure α` becomes a type only after `α` receives a `MeasurableSpace`, so this interpretation is
an explicit fold rather than an unrestricted Lean monad morphism. The measurable-continuation
boundary remains visible in the general laws. Discrete answer types discharge the internal
measurability obligations while leaving the result space arbitrary.

## Main definitions

* `PFunctor.IsMeasureSpec` assigns a probability measure to each operation.
* `PFunctor.IsMeasureSpec.uniformOfFintypeInhabited` assigns the native uniform measure to every
  finite, inhabited answer type.
* `PFunctor.FreeM.denote` is the measure denoted by a free program.

## Main statements

* `PFunctor.FreeM.denote_lift` identifies the denotation of one operation.
* `PFunctor.FreeM.denote_bind_of_discrete` and `PFunctor.FreeM.denote_map_of_discrete` give the
  discrete Giry composition laws.
* `PFunctor.FreeM.denote_bind_bind_prod_mk_eq_prod` identifies two independent executions with
  Mathlib's product measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v w uA

namespace PFunctor

/-- Per-operation answer measures for a polynomial interface.

The measurable structure on answer types is a separate parameter rather than a field, mirroring
Mathlib's separation of `MeasurableSpace` from the measures carried on it. Answer types need not
be discrete. -/
class IsMeasureSpec (P : PFunctor.{uA, u}) [∀ a, MeasurableSpace (P.B a)] where
  /-- The distribution of answers to an operation. -/
  toMeasure : (a : P.A) → Measure (P.B a)
  /-- Answering an operation is lossless. -/
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (toMeasure a)

attribute [instance] IsMeasureSpec.isProbabilityMeasure

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  {α : Type v} {β : Type w}

/-! ## Giry composition laws -/

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

end FreeM
end PFunctor
