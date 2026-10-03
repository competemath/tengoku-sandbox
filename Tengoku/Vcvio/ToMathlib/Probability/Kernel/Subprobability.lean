/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Tengoku.Vcvio.ToMathlib.MeasureTheory.Measure.Subprobability
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Subprobability kernels

`IsSubprobabilityKernel κ` states that every measure produced by `κ` has total mass at most one.
It is the kernel-level mass discipline for a parameterized computation that may fail or diverge.

Mathlib's `IsZeroOrMarkovKernel` is different: it allows only kernels that are identically zero or
have mass exactly one at every input. A subprobability kernel may lose a different, nontrivial
amount of mass at each input.

The class is closed under the standard kernel operations used by probabilistic semantics. In
particular, a subprobability kernel is finite and hence s-finite, so Mathlib's composition and
product APIs apply without additional finiteness assumptions.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A kernel whose value at every input is a subprobability measure. -/
class IsSubprobabilityKernel (κ : Kernel α β) : Prop where
  /-- Every kernel value has total mass at most one. -/
  measure_univ_le' : ∀ a, κ a Set.univ ≤ 1

namespace Kernel

variable (κ : Kernel α β) [IsSubprobabilityKernel κ]

/-- Every value of a subprobability kernel has total mass at most one. -/
theorem measure_univ_le (a : α) : κ a Set.univ ≤ 1 :=
  IsSubprobabilityKernel.measure_univ_le' a

/-- Every measurable event has mass at most one under a subprobability kernel. -/
theorem measure_le_one (a : α) (s : Set β) : κ a s ≤ 1 :=
  (measure_mono (Set.subset_univ s)).trans (κ.measure_univ_le a)

end Kernel

end ProbabilityTheory
