module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

public section

open scoped Pointwise

namespace Set
variable {α : Type*} [Group α]

@[to_additive (attr := simp)]
lemma mul_mem_smul_set_iff (a : α) {b : α} {s : Set α} : a * b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_set_iff

end Set
