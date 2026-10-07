/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Tengoku.Seed.Init

/-!
# Coequalizer of a pair of functions

The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) that
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`.

In this file we define the coequalizer and provide the basic API.
-/

@[expose] public section

universe v

namespace Function

/-- The relation generating the equivalence relation used for defining `Function.coequalizer`. -/
inductive Coequalizer.Rel {α β : Type*} (f g : α → β) : β → β → Prop where
  | intro (x : α) : Rel f g (f x) (g x)

/-- The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) that
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`. -/
def Coequalizer {α : Type*} {β : Type v} (f g : α → β) : Type v :=
  Quot (Function.Coequalizer.Rel f g)

namespace Coequalizer

variable {α β : Type*} (f g : α → β)

/-- The canonical projection to the coequalizer. -/
def mk (x : β) : Coequalizer f g :=
  Quot.mk _ x

/--
@isnad1 id=eq.0h5v.s5.4ee285afa79a from=seed src=0 shape=5b7c74ee vocab=eaca9942
-/
lemma condition (x : α) : mk f g (f x) = mk f g (g x) :=
  Quot.sound (.intro x)

/--
@isnad1 id=surjecti.0h4v.s4.34467e2c66db from=seed src=0 shape=16bda6e7 vocab=96dd644a
-/
lemma mk_surjective : Function.Surjective (mk f g) :=
  Quot.exists_rep

/-- Any map `u : β → γ` with `u ∘ f = u ∘ g` factors via `Function.Coequalizer.mk`. -/
def desc {γ : Type*} (u : β → γ) (hu : u ∘ f = u ∘ g) : Coequalizer f g → γ :=
  Quot.lift u (fun _ _ (.intro e) ↦ congrFun hu e)

/--
@isnad1 id=eq.1h7v.s5.9d17b9fde257 from=seed src=0 shape=af33906b vocab=dcf8c647
-/
@[simp] lemma desc_mk {γ : Type*} (u : β → γ) (hu : u ∘ f = u ∘ g) (x : β) :
    desc f g u hu (mk f g x) = u x :=
  rfl

end Function.Coequalizer
