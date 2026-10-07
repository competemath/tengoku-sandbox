/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Tengoku.Seed.Logic.Function.FromTypes

/-! # Function types of a given arity

This provides `Function.OfArity`, such that `OfArity α β 2 = α → α → β`.
Note that it is often preferable to use `(Fin n → α) → β` in place of `OfArity n α β`.

## Main definitions

* `Function.OfArity α β n`: `n`-ary function `α → α → ... → β`. Defined inductively.
* `Function.OfArity.const α b n`: `n`-ary constant function equal to `b`.
-/

@[expose] public section

universe u

namespace Function

/-- The type of `n`-ary functions `α → α → ... → β`.

Note that this is not universe polymorphic, as this would require that when `n=0` we produce either
`Unit → β` or `ULift β`. -/
abbrev OfArity (α β : Type u) (n : ℕ) : Type u := FromTypes (fun (_ : Fin n) => α) β

/--
@isnad1 id=eq.0h2v.s3.81e21de9d728 from=seed src=0 shape=1686f2ad vocab=de15e91e
-/
@[simp]
theorem ofArity_zero (α β : Type u) : OfArity α β 0 = β := fromTypes_zero _ _

/--
@isnad1 id=eq.0h3v.s4.0e46b275939f from=seed src=0 shape=d7f734f4 vocab=44612dca
-/
@[simp]
theorem ofArity_succ (α β : Type u) (n : ℕ) :
    OfArity α β n.succ = (α → OfArity α β n) := fromTypes_succ _ _

namespace OfArity

/-- Constant `n`-ary function with value `b`. -/
def const (α : Type u) {β : Type u} (b : β) (n : ℕ) : OfArity α β n :=
  FromTypes.const (fun _ => α) b

/--
@isnad1 id=eq.0h3v.s4.1b9c5edef340 from=seed src=0 shape=e7c6b9eb vocab=b1212bf4
-/
@[simp]
theorem const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b :=
  FromTypes.const_zero (fun _ => α) b

/--
@isnad1 id=eq.0h4v.s5.19a2c65bf4ed from=seed src=0 shape=9b304e50 vocab=153eec24
-/
@[simp]
theorem const_succ (α : Type u) {β : Type u} (b : β) (n : ℕ) :
    const α b n.succ = fun _ => const _ b n :=
  FromTypes.const_succ (fun _ => α) b

/--
@isnad1 id=eq.0h5v.s5.904fcea9715d from=seed src=0 shape=1472aa23 vocab=1b140cb7
-/
theorem const_succ_apply (α : Type u) {β : Type u} (b : β) (n : ℕ) (x : α) :
    const α b n.succ x = const _ b n := FromTypes.const_succ_apply _ b x

instance inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n) :=
  inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))

end OfArity

namespace FromTypes

/--
@isnad1 id=eq.0h3v.s4.1f35e1474d1c from=seed src=0 shape=58e0a02c vocab=da517049
-/
lemma fromTypes_fin_const (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β = OfArity α β n := rfl

/-- The definitional equality between heterogeneous functions with constant
domain and `n`-ary functions with that domain. -/
def fromTypes_fin_const_equiv (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β ≃ OfArity α β n := .refl _

end FromTypes

end Function
