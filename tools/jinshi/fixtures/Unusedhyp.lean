-- jinshi: only unusedhyp
/-
Jinshi fixture for `unusedhyp` (docs/jinshi.md): theorems whose statements name a propositional hypothesis the proof never
uses, against Lean's own library. Unusedhyp.expected.tsv names what must be found; the rest must stay quiet.
-/
namespace JinshiFixtures

-- a hypothesis the proof never mentions: the theorem holds without `h`
theorem unused_hyp (n : Nat) (h : n > 0) : n + 0 = n := Nat.add_zero n

-- two hypotheses, one used (`h`), one not (`hlt`)
theorem one_of_two_unused (n : Nat) (h : n > 0) (hlt : n < 5) : n ≠ 0 := Nat.pos_iff_ne_zero.mp h

-- quiet: the hypothesis is used
theorem hyp_used (n : Nat) (h : n > 0) : n ≠ 0 := Nat.pos_iff_ne_zero.mp h

-- quiet: `h` is mentioned only in the type of a later binder (`x`, a subtype, not a proposition, so not a hypothesis itself)
theorem hyp_in_later_binder (n : Nat) (h : n > 0) (x : { m : Nat // m = n ∧ h = h }) : True := trivial

-- `h` is mentioned in the type of the later hypothesis `h2`, so `h` is quiet; `h2` itself is never used
theorem hyp_in_later_unused_hyp (n : Nat) (h : n > 0) (h2 : h = h) : n + 0 = n := Nat.add_zero n

-- quiet: variables and instances are the statement's subject, not hypotheses
theorem no_hyps (α : Type) [Inhabited α] (a : α) : a = a := rfl

end JinshiFixtures
