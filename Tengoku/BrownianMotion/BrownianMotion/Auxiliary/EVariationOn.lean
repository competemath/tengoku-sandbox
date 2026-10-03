/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Variation of a function over a countable or dense set of points

The variation of a function over a set is an uncountable supremum, so it is not measurable in a
parameter for free. This file provides tools to compute it over a countable set of points instead.
Measurability of the variation of a family of functions is deduced from these tools in the file
`BrownianMotion.StochasticIntegral.VariationProcess`.

## Main results

* `eVariationOn_eq_iSup_fin`: the variation over `s` as a supremum over monotone tuples with values
  in `s`.

Which dense sets suffice to compute the variation depends on the regularity of the function, and
this file provides two independent sets of assumptions:

1. the first assumes **continuity** of the function together with **separability** of the domain —
  `eVariationOn_eq_comp_val_of_dense`;
2. the second assumes only **right-continuity** of the function, but requires the domain to be
  **second countable** — `eVariationOn_eq_comp_val_of_dense_Ioi`, together with the left-continuous
  counterpart `eVariationOn_eq_comp_val_of_dense_Iio`.

-/

@[expose] public section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

variable {ι Ω E : Type*}

variable [LinearOrder ι] [PseudoEMetricSpace E]

variable [TopologicalSpace ι]

section Separable

end Separable

section SecondCountableTopology

/-- A point of a subset `s` is isolated on the right in the subspace `↥s` exactly when it is
isolated on the right within `s`. -/
lemma nhdsGT_subtype_eq_bot_iff {s : Set ι} {x : ι} (hx : x ∈ s) :
    𝓝[>] (⟨x, hx⟩ : s) = ⊥ ↔ 𝓝[s ∩ Ioi x] x = ⊥ := by
  have : ((↑) : s → ι) ⁻¹' Ioi x = Ioi ⟨x, hx⟩ := rfl
  rw [← this, nhdsWithin_subtype_eq_bot_iff, nhdsWithin, inf_assoc, inf_principal, inter_comm,
    ← nhdsWithin]

end SecondCountableTopology
