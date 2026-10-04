/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/

module

public import Tengoku.Seed.Algebra.Group.ModEq
public import Tengoku.Seed.GroupTheory.QuotientGroup.Defs
public import Tengoku.Seed.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Congruence modulo multiples and congruence modulo `AddSubgroup.zmultiples _`

In this file we show that in an additive commutative group, the congruence relation `a ≡ b [PMOD p]`
is equivalent to the coercions of `a` and `b` to `G ⧸ AddSubgroup.zmultiples p` being equal.
-/

public section

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G] {a b p : G}

theorem modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) = b := by
  rw [modEq_comm]
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]

theorem not_modEq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) ≠ b :=
  modEq_iff_eq_mod_zmultiples.not

end AddCommGroup
