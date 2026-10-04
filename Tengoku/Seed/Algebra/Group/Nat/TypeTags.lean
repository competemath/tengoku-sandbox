/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Nat.Defs
public import Tengoku.Seed.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℕ`
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Multiplicative

namespace Nat

lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

@[simp] lemma ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm

end Nat
