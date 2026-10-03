/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

-- import Mathlib.CategoryTheory.Monad.Basic
public import Tengoku.Control.Lawful
public import Tengoku.Std.Control.OptionT

/-!
# Monad transformers

Taken from [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/MonadFunctor.20misunderstanding.20or.20bug.3F/near/477088609).

-/

@[expose] public section

universe u v w

/-- A type class for monad transformers. -/
class MonadTransformer (t : (Type u → Type v) → Type u → Type w) where
  [mapMonad (m) [Monad m] : Monad (t m)]
  [transform (m) [Monad m] : MonadLift m (t m)]

variable {t : (Type u → Type v) → Type u → Type w} {m : Type u → Type v} {n : Type u → Type v}
  {α β ρ ε σ : Type u}

instance [MonadTransformer t] [Monad m] : Monad (t m) := MonadTransformer.mapMonad m

@[always_inline, inline, simp]
abbrev MonadTransformer.liftOf [MonadTransformer t] (m) [Monad m] : m α → t m α :=
  (transform m).monadLift

export MonadTransformer (liftOf)

@[always_inline, inline, simp]
abbrev MonadTransformer.lift [MonadTransformer t] {m} [Monad m] : m α → t m α :=
  liftOf m

instance : MonadTransformer (ReaderT ρ) where
  mapMonad _ := inferInstance
  transform := inferInstance

instance : MonadTransformer (ExceptT ε) where
  mapMonad _ := inferInstance
  transform _ := inferInstance

instance : MonadTransformer (StateT σ) where
  mapMonad _ := inferInstance
  transform _ := inferInstance

instance : MonadTransformer OptionT where
  mapMonad _ := inferInstance
  transform _ := inferInstance

/--
The `MonadTransformer` typeclass only contains the operations of a monad transformer.
`LawfulMonadTransformer` also asserts these operations satisfy the laws of a monad transformer:
```
liftOf m (pure x) = pure x
liftOf m (x >>= f) = liftOf m x >>= liftOf m ∘ f
```
-/
class LawfulMonadTransformer (t) [MonadTransformer t] : Prop where
  [monad_functor {m : Type u → Type v} [Monad m] [LawfulMonad m] : LawfulMonad (t m)]
  liftOf_pure {m : Type u → Type v} [Monad m] [LawfulMonad m] {α} (x : α) :
    liftOf m (pure x) = (pure x : t m α)
  liftOf_bind {m : Type u → Type v} [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    liftOf (t := t) m (x >>= f) = liftOf m x >>= (fun a => liftOf m (f a))

export LawfulMonadTransformer (liftOf_pure liftOf_bind)

attribute [simp] liftOf_pure liftOf_bind

section
attribute [local simp] MonadLift.monadLift Bind.bind

end

namespace MonadTransformer

/-- A monad transformer is covariant if it lifts monad morphisms to monad morphisms. -/
class IsCovariant (t : (Type u → Type v) → Type u → Type w) [MonadTransformer t] where
  functorMap {m n : Type u → Type v} [MonadLiftT m n] :
    MonadLiftT (t m) (t n)

instance [MonadTransformer t] [Monad m] : MonadLift m (t m) := MonadTransformer.transform m

end MonadTransformer
