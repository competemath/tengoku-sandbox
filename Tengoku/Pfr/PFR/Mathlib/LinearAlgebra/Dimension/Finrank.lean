module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

public section

/-- The dimension of a submodule -/
noncomputable abbrev Submodule.finrank {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) : ℕ := Module.finrank R S
