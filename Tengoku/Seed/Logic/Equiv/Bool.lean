/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Emily Riehl, Wrenna Robson
-/
module

public import Tengoku.Seed.Logic.Equiv.Basic
public import Tengoku.Seed.Logic.Function.Basic

/-!
# Equivalences involving `Bool`

This file shows that `not : Bool → Bool` is an equivalence and derives some consequences
-/

@[expose] public section

/-- The boolean negation function `not : Bool → Bool` is an involution and thus an equivalence. -/
@[simps!]
def Equiv.boolNot : Equiv.Perm Bool := Bool.involutive_not.toPerm

namespace Bool

open Function

/--
@isnad1 id=bijectiv.0h0v.s2.4f5dfb9b8355 from=seed src=0 shape=e3d48bcb vocab=94d8b9a2
-/
theorem not_bijective : Bijective not := Equiv.boolNot.bijective
/--
@isnad1 id=injectiv.0h0v.s2.2c1842271ede from=seed src=0 shape=e3d48bcb vocab=ed3f7012
-/
theorem not_injective : Injective not := Equiv.boolNot.injective
/--
@isnad1 id=surjecti.0h0v.s2.db2faabc029a from=seed src=0 shape=e3d48bcb vocab=550cabb8
-/
theorem not_surjective : Surjective not := Equiv.boolNot.surjective

/--
@isnad1 id=leftinve.0h0v.s2.558c4b4419ad from=seed src=0 shape=4ce37f0a vocab=c382b15e
-/
theorem not_leftInverse : LeftInverse not not := not_not
/--
@isnad1 id=rightinv.0h0v.s2.e5e7a1b40e71 from=seed src=0 shape=4ce37f0a vocab=4d4bc4f6
-/
theorem not_rightInverse : RightInverse not not := not_not

/--
@isnad1 id=haslefti.0h0v.s2.c53b316412a8 from=seed src=0 shape=e3d48bcb vocab=db87e0d9
-/
theorem not_hasLeftInverse : HasLeftInverse not := ⟨not, not_leftInverse⟩
/--
@isnad1 id=hasright.0h0v.s2.94312e6cacbb from=seed src=0 shape=e3d48bcb vocab=744cb878
-/
theorem not_hasRightInverse : HasRightInverse not := ⟨not, not_rightInverse⟩

end Bool
