/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Module.Defs
public import Tengoku.Seed.Algebra.Order.GroupWithZero.Action.Synonym
public import Tengoku.Seed.Algebra.Order.Ring.Synonym

/-!
# Action instances for `OrderDual`


This PR transfers group action with zero instances from a type `α` to `αᵒᵈ` and `Lex α`. Note that
the `SMul` instances are already defined in `Mathlib/Algebra/Order/Group/Synonym.lean`.

## See also

* `Mathlib/Algebra/Order/Group/Action/Synonym.lean`
* `Mathlib/Algebra/Order/GroupWithZero/Action/Synonym.lean`
-/

public section

variable {α β : Type*}

namespace OrderDual

instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β where
  add_smul := add_smul (R := α)
  zero_smul := zero_smul _

instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ where
  add_smul := add_smul (M := β)
  zero_smul := zero_smul _

end OrderDual

namespace Lex

instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module (Lex α) β :=
  ‹Module α β›

instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α (Lex β) :=
  ‹Module α β›

end Lex
