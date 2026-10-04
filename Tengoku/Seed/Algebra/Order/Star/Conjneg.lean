/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Pi
public import Tengoku.Seed.Algebra.Order.Star.Basic
public import Tengoku.Seed.Algebra.Star.Conjneg

/-!
# Order properties of conjugation-negation
-/

public section

open scoped ComplexConjugate

variable {G R : Type*} [AddGroup G]

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {f : G → R}

@[simp] lemma conjneg_nonneg : 0 ≤ conjneg f ↔ 0 ≤ f :=
  (Equiv.neg _).forall_congr' <| by simp [starRingEnd_apply]

@[simp] lemma conjneg_pos : 0 < conjneg f ↔ 0 < f := by
  simp_rw [lt_iff_le_and_ne, ne_comm, conjneg_nonneg, conjneg_ne_zero]

end OrderedCommSemiring

section OrderedCommRing
variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {f : G → R}

@[simp] lemma conjneg_nonpos : conjneg f ≤ 0 ↔ f ≤ 0 := by
  simp_rw [← neg_nonneg, ← conjneg_neg, conjneg_nonneg]

@[simp] lemma conjneg_neg' : conjneg f < 0 ↔ f < 0 := by
  simp_rw [← neg_pos, ← conjneg_neg, conjneg_pos]

end OrderedCommRing
