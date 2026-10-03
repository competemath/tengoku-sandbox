module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

public section

@[expose]
noncomputable def Submodule.finrank {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Submodule R M) : ℕ := Module.finrank R s
