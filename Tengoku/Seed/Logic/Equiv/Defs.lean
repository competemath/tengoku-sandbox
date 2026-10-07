/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Tengoku.Seed.Data.FunLike.Equiv
public import Tengoku.Seed.Data.Quot
public import Tengoku.Seed.Data.Subtype
public import Tengoku.Seed.Logic.Unique
public import Tengoku.Seed.Tactic.Simps


/-!
# Equivalence between types

In this file we define two types:

* `Equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `Equiv.Perm α`: the group of permutations `α ≃ α`. More lemmas about `Equiv.Perm` can be found in
  `Mathlib/GroupTheory/Perm/`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `Equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `Equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `Equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `Equiv.inhabited` takes `e : α ≃ β` and `[Inhabited β]` and returns `Inhabited α`;
  - `Equiv.unique` takes `e : α ≃ β` and `[Unique β]` and returns `Unique α`;
  - `Equiv.decidableEq` takes `e : α ≃ β` and `[DecidableEq β]` and returns `DecidableEq α`.

  More definitions of this kind can be found in other files.
  E.g., `Mathlib/Algebra/Group/TransferInstance.lean` does it for `Group`,
  `Mathlib/Algebra/Module/TransferInstance.lean` does it for `Module`, and similar files exist for
  other algebraic type classes.

Many more such isomorphisms and operations are defined in `Mathlib/Logic/Equiv/Basic.lean`.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α β : Sort*) where
  /-- The forward map of an equivalence.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : α → β
  /-- The backward map of an equivalence.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
infixl:25 " ≃ " => Equiv

/-- Turn an element of a type `F` satisfying `EquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`. -/
@[coe]
def EquivLike.toEquiv {F} [EquivLike F α β] (f : F) : α ≃ β where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f

/-- Any type satisfying `EquivLike` can be cast into `Equiv` via `EquivLike.toEquiv`. -/
instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨EquivLike.toEquiv⟩

/-- `Perm α` is the type of bijections from `α` to itself. -/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α

namespace Equiv

instance : EquivLike (α ≃ β) α β where
  coe := Equiv.toFun
  inv := Equiv.invFun
  left_inv := Equiv.left_inv
  right_inv := Equiv.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by cases e₁; cases e₂; congr

@[simp, norm_cast]
lemma _root_.EquivLike.coe_coe {F} [EquivLike F α β] (e : F) :
    ((e : α ≃ β) : α → β) = e := rfl

/--
@isnad1 id=eq.2h4v.s5.f85a831ea3a2 from=seed src=0 shape=93f5d69f vocab=5e860e0c
-/
@[simp, grind =] theorem coe_fn_mk (f : α → β) (g l r) : (Equiv.mk f g l r : α → β) = f :=
  rfl

/-- The map `(r ≃ s) → (r → s)` is injective.
@isnad1 id=injectiv.0h2v.s5.402d3f108c28 from=seed src=0 shape=d8da120a vocab=53d25045
-/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α → β) (fun e => e) :=
  DFunLike.coe_injective

/--
@isnad1 id=iff.0h4v.s5.7de6dcf727b8 from=seed src=0 shape=ee852657 vocab=c53aac11
-/
protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  @DFunLike.coe_fn_eq _ _ _ _ e₁ e₂

/--
@isnad1 id=eq.1h4v.s5.14451b68d9a6 from=seed src=0 shape=149ba31d vocab=c53aac11
-/
@[ext, grind ext] theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g := DFunLike.ext f g H

/--
@isnad1 id=eq.1h5v.s5.9ac6cf5bb8f7 from=seed src=0 shape=db35865f vocab=c53aac11
-/
protected theorem congr_arg {f : Equiv α β} {x x' : α} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

/--
@isnad1 id=eq.1h5v.s5.31029b7ee293 from=seed src=0 shape=c17ca912 vocab=c53aac11
-/
protected theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

/--
@isnad1 id=eq.1h3v.s5.6a3ad1ddd19a from=seed src=0 shape=d82adda6 vocab=26837e6f
-/
@[ext] theorem Perm.ext {σ τ : Equiv.Perm α} (H : ∀ x, σ x = τ x) : σ = τ := Equiv.ext H

/--
@isnad1 id=eq.1h4v.s5.7dd69bec20df from=seed src=0 shape=33304551 vocab=26837e6f
-/
protected theorem Perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equiv.congr_arg

/--
@isnad1 id=eq.1h4v.s5.9af5eab4b34c from=seed src=0 shape=36c50730 vocab=26837e6f
-/
protected theorem Perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x

/-- Any type is equivalent to itself. -/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

instance inhabited' : Inhabited (α ≃ α) := ⟨Equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm, implicit_reducible]
protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)

/-- Restatement of `Equiv.left_inv` in terms of `Function.LeftInverse`.
@isnad1 id=leftinve.0h3v.s5.b6d805ba88d9 from=seed src=0 shape=2e346384 vocab=f797c4b3
-/
theorem left_inv' (e : α ≃ β) : Function.LeftInverse e.symm e := e.left_inv
/-- Restatement of `Equiv.right_inv` in terms of `Function.RightInverse`.
@isnad1 id=rightinv.0h3v.s5.a249a04db0d6 from=seed src=0 shape=2e346384 vocab=ad3a93fa
-/
theorem right_inv' (e : α ≃ β) : Function.RightInverse e.symm e := e.right_inv

/--
@isnad1 id=eq.2h4v.s5.dd3a0502dbdf from=seed src=0 shape=63c1323d vocab=9132d0ba
-/
@[simp] lemma symm_mk (f : α → β) (g hl hr) : (mk f g hl hr).symm = mk g f hr hl := rfl

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simps]
instance : Trans Equiv Equiv Equiv where
  trans := Equiv.trans

/-- `Equiv.symm` defines an equivalence between `α ≃ β` and `β ≃ α`. -/
@[simps! (attr := grind =)]
def symmEquiv (α β : Sort*) : (α ≃ β) ≃ (β ≃ α) where
  toFun := .symm
  invFun := .symm

/--
@isnad1 id=eq.0h3v.s5.e547a147981f from=seed src=0 shape=4bf4240a vocab=3a185bf1
-/
@[simp, mfld_simps] theorem toFun_as_coe (e : α ≃ β) : e.toFun = e := rfl

/--
@isnad1 id=eq.0h3v.s5.1f3ac86139c5 from=seed src=0 shape=8b97d918 vocab=d56f8705
-/
@[simp, mfld_simps] theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm := rfl

/--
@isnad1 id=injectiv.0h3v.s4.5e800ab78925 from=seed src=0 shape=8d068dd3 vocab=53d25045
-/
protected theorem injective (e : α ≃ β) : Injective e := EquivLike.injective e

/--
@isnad1 id=surjecti.0h3v.s4.5c108da7bf8d from=seed src=0 shape=8d068dd3 vocab=7da565df
-/
protected theorem surjective (e : α ≃ β) : Surjective e := EquivLike.surjective e

/--
@isnad1 id=bijectiv.0h3v.s4.d40914427c2b from=seed src=0 shape=8d068dd3 vocab=70e77864
-/
protected theorem bijective (e : α ≃ β) : Bijective e := EquivLike.bijective e

/--
@isnad1 id=subsingl.0h3v.s3.cf04d9e6d988 from=seed src=0 shape=6aa8801c vocab=800f30d1
-/
protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.injective.subsingleton

/--
@isnad1 id=subsingl.0h3v.s3.191ccb0b0088 from=seed src=0 shape=8ba992df vocab=800f30d1
-/
protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.injective.subsingleton

/--
@isnad1 id=iff.0h3v.s3.fec3ce013a7d from=seed src=0 shape=f8a886ac vocab=800f30d1
-/
theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩

/--
@isnad1 id=subsingl.0h2v.s3.78114af8d09d from=seed src=0 shape=1417b07d vocab=800f30d1
-/
instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩

/--
@isnad1 id=subsingl.0h2v.s3.c56790add64e from=seed src=0 shape=f9923b89 vocab=800f30d1
-/
instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f _ => Equiv.ext fun _ => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩

instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)

/--
@isnad1 id=eq.0h2v.s3.c43c47f0f218 from=seed src=0 shape=868c5411 vocab=eb141a85
-/
theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equiv.refl α :=
  Subsingleton.elim _ _

/--
@isnad1 id=nontrivi.0h3v.s3.9795e630a371 from=seed src=0 shape=6bb65de6 vocab=79604efb
-/
protected theorem nontrivial {α β} (e : α ≃ β) [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial

/--
@isnad1 id=iff.0h3v.s3.83124a155bcb from=seed src=0 shape=f377a2d2 vocab=79604efb
-/
theorem nontrivial_congr {α β} (e : α ≃ β) : Nontrivial α ↔ Nontrivial β :=
  ⟨fun _ ↦ e.symm.nontrivial, fun _ ↦ e.nontrivial⟩

/-- Transfer `DecidableEq` across an equivalence. -/
protected abbrev decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.injective.decidableEq

/--
@isnad1 id=iff.0h3v.s3.2bbb29272df4 from=seed src=0 shape=f8a886ac vocab=4f68101a
-/
theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β := Nonempty.congr e e.symm

/--
@isnad1 id=nonempty.0h3v.s3.6c2052644ee4 from=seed src=0 shape=6aa8801c vocab=4f68101a
-/
protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α := e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected abbrev inhabited [Inhabited β] (e : α ≃ β) : Inhabited α := ⟨e.symm default⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected abbrev unique [Unique β] (e : α ≃ β) : Unique α := e.symm.surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β where
  toFun := cast h
  invFun := cast h.symm
  left_inv := by grind
  right_inv := by grind

/--
@isnad1 id=eq.2h4v.s5.2703b8a77b88 from=seed src=0 shape=780f79bb vocab=a4e01716
-/
@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((Equiv.mk f g l r).symm : β → α) = g := rfl

/--
@isnad1 id=eq.0h1v.s4.569890738f49 from=seed src=0 shape=f527b7d1 vocab=906f363a
-/
@[simp] theorem coe_refl : (Equiv.refl α : α → α) = id := rfl

/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `Multiplicative.ofAdd` etc.
@isnad1 id=eq.0h2v.s4.ee97cd3ffaec from=seed src=0 shape=208e62d6 vocab=c8dc74a5
-/
theorem Perm.coe_subsingleton {α : Type*} [Subsingleton α] (e : Perm α) : (e : α → α) = id := by
  rw [Perm.subsingleton_eq_refl e, coe_refl]

/--
@isnad1 id=eq.0h2v.s4.be4a7fdcd202 from=seed src=0 shape=f8d54099 vocab=2f9000b8
-/
@[simp, grind =] theorem refl_apply (x : α) : Equiv.refl α x = x := rfl

/--
@isnad1 id=eq.0h5v.s6.c60661fb1b04 from=seed src=0 shape=c1c49f9d vocab=20cfb7ba
-/
@[simp] theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g : α → γ) = g ∘ f := rfl

/--
@isnad1 id=eq.0h6v.s6.fc508e6db916 from=seed src=0 shape=138f468e vocab=7fb123da
-/
@[simp, grind =] theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) :
    (f.trans g) a = g (f a) := rfl

/--
@isnad1 id=eq.0h4v.s5.660e0e5113f1 from=seed src=0 shape=ec1c32fa vocab=eb0e1a8d
-/
@[simp, grind =] theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x := e.right_inv x

/--
@isnad1 id=eq.0h4v.s5.c8c08e7ad05a from=seed src=0 shape=93a39e7e vocab=eb0e1a8d
-/
@[simp, grind =] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := e.left_inv x

/--
@isnad1 id=eq.0h3v.s5.1a85c17c2512 from=seed src=0 shape=1ee74e5b vocab=0bb429b3
-/
@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id := funext e.symm_apply_apply

/--
@isnad1 id=eq.0h3v.s5.12159fe91e64 from=seed src=0 shape=c7f0b2db vocab=0bb429b3
-/
@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id := funext e.apply_symm_apply

@[simp] lemma _root_.EquivLike.apply_coe_symm_apply {F} [EquivLike F α β] (e : F) (x : β) :
    e ((e : α ≃ β).symm x) = x :=
  (e : α ≃ β).apply_symm_apply x

@[simp] lemma _root_.EquivLike.coe_symm_apply_apply {F} [EquivLike F α β] (e : F) (x : α) :
    (e : α ≃ β).symm (e x) = x :=
  (e : α ≃ β).symm_apply_apply x

@[simp] lemma _root_.EquivLike.coe_symm_comp_self {F} [EquivLike F α β] (e : F) :
    (e : α ≃ β).symm ∘ e = id :=
  (e : α ≃ β).symm_comp_self

@[simp] lemma _root_.EquivLike.self_comp_coe_symm {F} [EquivLike F α β] (e : F) :
    e ∘ (e : α ≃ β).symm = id :=
  (e : α ≃ β).self_comp_symm

/--
@isnad1 id=eq.0h6v.s6.8ba0f8aa8b6f from=seed src=0 shape=e327f7cc vocab=f35cfa51
-/
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl

/--
@isnad1 id=eq.0h5v.s5.4117640742c8 from=seed src=0 shape=d3dde45a vocab=8659874e
-/
@[simp, grind =]
theorem symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = g.symm.trans f.symm := rfl

/--
@isnad1 id=eq.0h4v.s5.6959dcbe4b5c from=seed src=0 shape=c0c86d73 vocab=eb0e1a8d
-/
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b := rfl

/--
@isnad1 id=iff.0h5v.s5.1181badb41ef from=seed src=0 shape=4b07764f vocab=c53aac11
-/
theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f

/--
@isnad1 id=eq.1h3v.s5.af46a2a27de3 from=seed src=0 shape=5eb373a5 vocab=4e300d20
-/
@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x := rfl

/--
@isnad1 id=eq.1h2v.s4.dcaca65bb784 from=seed src=0 shape=89a68033 vocab=14dd4d04
-/
theorem cast_symm {α β} (h : α = β) : Equiv.cast h.symm = (Equiv.cast h).symm := rfl

/--
@isnad1 id=eq.0h2v.s4.b6c83c3842a5 from=seed src=0 shape=e24c3cfe vocab=ba44ac2d
-/
@[simp] theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α := rfl

/--
@isnad1 id=eq.2h3v.s5.1a8928f204e5 from=seed src=0 shape=9bb11c3a vocab=be37e252
-/
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
    Equiv.cast (h.trans h2) = (Equiv.cast h).trans (Equiv.cast h2) :=
  ext fun x => by subst h h2; rfl

/--
@isnad1 id=iff.1h4v.s5.02f3478e6558 from=seed src=0 shape=60ab4fdf vocab=71ef3ae8
-/
theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ a ≍ b := by
  subst h; simp

/--
@isnad1 id=iff.0h5v.s5.2a624865f274 from=seed src=0 shape=f421647c vocab=eb0e1a8d
-/
theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y := by grind

theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x := by grind

/--
@isnad1 id=iff.0h5v.s5.f7b86882f60e from=seed src=0 shape=7bd505ed vocab=eb0e1a8d
-/
@[deprecated eq_symm_apply (since := "2026-07-26")]
theorem apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : α ≃ β) : f x = y ↔ x = f.symm y :=
  f.eq_symm_apply.symm

/--
@isnad1 id=eq.0h3v.s4.ea4425396bf6 from=seed src=0 shape=d677378a vocab=a3c9a444
-/
@[simp, grind =] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := rfl

/--
@isnad1 id=bijectiv.0h2v.s3.d084e7b84f7d from=seed src=0 shape=7d207def vocab=2db258e7
-/
theorem symm_bijective : Function.Bijective (Equiv.symm : (α ≃ β) → β ≃ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
@isnad1 id=eq.0h3v.s4.58a75a189517 from=seed src=0 shape=cd3ab17f vocab=0255356c
-/
@[simp] theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e := by grind

/--
@isnad1 id=eq.0h1v.s3.7805c81c14a8 from=seed src=0 shape=b71d1e01 vocab=dad3976f
-/
@[simp, grind =] theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α := rfl

/--
@isnad1 id=eq.0h3v.s4.a3c6f6bcce7a from=seed src=0 shape=b8933f5f vocab=0255356c
-/
@[simp] theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e := by cases e; rfl

/--
@isnad1 id=eq.0h3v.s4.f88aaad6e9e9 from=seed src=0 shape=e236a264 vocab=9f8f4f38
-/
@[simp] theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β := by grind

/--
@isnad1 id=eq.0h3v.s4.3336f1db3e16 from=seed src=0 shape=06cd046a vocab=9f8f4f38
-/
@[simp] theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α := by grind

/--
@isnad1 id=eq.0h7v.s5.ac4dea1e58fc from=seed src=0 shape=3d239f2a vocab=e29ca379
-/
theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := by grind

/--
@isnad1 id=iff.0h6v.s5.9cc2562b7bda from=seed src=0 shape=ce4bfea2 vocab=8659874e
-/
theorem trans_cancel_left (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ f = e.symm.trans g := by
  grind

/--
@isnad1 id=iff.0h6v.s5.6cb45083bf10 from=seed src=0 shape=038c52ce vocab=8659874e
-/
theorem trans_cancel_right (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ e = g.trans f.symm := by
  grind

/--
@isnad1 id=leftinve.0h3v.s5.b6d805ba88d9 from=seed src=0 shape=2e346384 vocab=f797c4b3
-/
theorem leftInverse_symm (f : α ≃ β) : LeftInverse f.symm f := f.left_inv

/--
@isnad1 id=rightinv.0h3v.s5.a249a04db0d6 from=seed src=0 shape=2e346384 vocab=ad3a93fa
-/
theorem rightInverse_symm (f : α ≃ β) : Function.RightInverse f.symm f := f.right_inv

/--
@isnad1 id=iff.0h5v.s5.af98e0addf95 from=seed src=0 shape=7d48d088 vocab=b287ef2e
-/
theorem injective_comp (e : α ≃ β) (f : β → γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f

/--
@isnad1 id=iff.0h5v.s5.8a7a1809b8d6 from=seed src=0 shape=a9523f48 vocab=b287ef2e
-/
theorem comp_injective (f : α → β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e

/--
@isnad1 id=iff.0h5v.s5.0491c7471382 from=seed src=0 shape=7d48d088 vocab=21ecd880
-/
theorem surjective_comp (e : α ≃ β) (f : β → γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f

/--
@isnad1 id=iff.0h5v.s5.f1c42a96b15a from=seed src=0 shape=a9523f48 vocab=21ecd880
-/
theorem comp_surjective (f : α → β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e

/--
@isnad1 id=iff.0h5v.s5.ade5e93927c3 from=seed src=0 shape=7d48d088 vocab=f71f65d0
-/
theorem bijective_comp (e : α ≃ β) (f : β → γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f

/--
@isnad1 id=iff.0h5v.s5.010002d570c8 from=seed src=0 shape=a9523f48 vocab=f71f65d0
-/
theorem comp_bijective (f : α → β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e

/--
@isnad1 id=eq.0h7v.s6.ae85797947d8 from=seed src=0 shape=ae07202a vocab=fa16d55a
-/
@[simp]
theorem extend_apply {f : α ≃ β} (g : α → γ) (e' : β → γ) (b : β) :
    extend f g e' b = g (f.symm b) := by
  rw [← f.apply_symm_apply b, f.injective.extend_apply, apply_symm_apply]

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equivCongr {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) where
  toFun ac := (ab.symm.trans ac).trans cd
  invFun bd := ab.trans <| bd.trans <| cd.symm
  left_inv ac := by grind
  right_inv ac := by grind

/--
@isnad1 id=eq.0h8v.s7.14341d26a735 from=seed src=0 shape=ce8c235e vocab=f6fae7d5
-/
@[simp, grind =] theorem equivCongr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) := rfl

/--
@isnad1 id=eq.0h6v.s5.238e424c2ce5 from=seed src=0 shape=cede0f3d vocab=8bb84cd5
-/
@[simp, grind =] theorem equivCongr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
    (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm := by ext; rfl

/--
@isnad1 id=eq.0h2v.s4.bc0401895adb from=seed src=0 shape=8ea4aa76 vocab=8d2f0cda
-/
@[simp] theorem equivCongr_refl {α β} :
    (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) := by grind

/--
@isnad1 id=eq.0h10v.s6.07fb841dc0a6 from=seed src=0 shape=553dd4a9 vocab=242db64f
-/
@[simp] theorem equivCongr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) := by
  grind

/--
@isnad1 id=eq.0h5v.s6.9de4104c0e27 from=seed src=0 shape=e3972219 vocab=b4d0ee7f
-/
@[simp] theorem equivCongr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
    (Equiv.refl α).equivCongr bg e = e.trans bg := rfl

/--
@isnad1 id=eq.0h4v.s6.c7a5ba0faeb5 from=seed src=0 shape=73b8f6c5 vocab=21a6f504
-/
@[simp] theorem equivCongr_refl_right {α β} (ab e : α ≃ β) :
    ab.equivCongr (Equiv.refl β) e = ab.symm.trans e := rfl
section permCongr

variable {α' β' : Type*} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `Perm α` is equivalent to `Perm β`. -/
def permCongr : Perm α' ≃ Perm β' := equivCongr e e

/--
@isnad1 id=eq.0h4v.s5.eb03ad6358b9 from=seed src=0 shape=2d1ca3c3 vocab=8f73c1d3
-/
theorem permCongr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e := rfl

/--
@isnad1 id=eq.0h3v.s5.132c82f64cae from=seed src=0 shape=f9b1080d vocab=bc569b49
-/
@[simp] theorem permCongr_refl : e.permCongr (Equiv.refl _) = Equiv.refl _ := by
  simp [permCongr_def]

/--
@isnad1 id=eq.0h3v.s4.516cbe650e1a from=seed src=0 shape=5dd9fa4d vocab=7c1a01d3
-/
@[simp, grind =] theorem permCongr_symm : e.permCongr.symm = e.symm.permCongr := rfl

/--
@isnad1 id=eq.0h5v.s6.12cb996a83e5 from=seed src=0 shape=1d327ae2 vocab=3fa793fa
-/
@[simp, grind =] theorem permCongr_apply (p : Equiv.Perm α') (x) :
    e.permCongr p x = e (p (e.symm x)) := rfl

/--
@isnad1 id=eq.0h5v.s6.26700490b545 from=seed src=0 shape=53099617 vocab=3fa793fa
-/
theorem permCongr_symm_apply (p : Equiv.Perm β') (x) :
    e.permCongr.symm p x = e.symm (p (e x)) := rfl

/--
@isnad1 id=eq.0h5v.s6.5dfb60b8c56e from=seed src=0 shape=15da7623 vocab=5ee7733c
-/
theorem permCongr_trans (p p' : Equiv.Perm α') :
    (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') := by grind

end permCongr

/-- Two empty types are equivalent. -/
def equivOfIsEmpty (α β : Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- If `α` is an empty type, then it is equivalent to the `Empty` type. -/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty := equivOfIsEmpty α _

/-- If `α` is an empty type, then it is equivalent to the `PEmpty` type in any universe. -/
def equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} := equivOfIsEmpty α _

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `PEmpty`. -/
def propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty := @equivPEmpty p <| IsEmpty.prop_iff.2 h

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
@[simps (attr := grind =)]
def ofUnique (α β : Sort _) [Unique.{u} α] [Unique.{v} β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` has a unique element, then it is equivalent to any `PUnit`. -/
@[simps! (attr := grind =)]
def equivPUnit (α : Sort u) [Unique α] : α ≃ PUnit.{v} := ofUnique α _

/-- The `Sort` of proofs of a true proposition is equivalent to `PUnit`. -/
def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0} := @equivPUnit p <| uniqueProp h

/-- `ULift α` is equivalent to `α`. -/
@[simps (attr := grind =) -fullyApplied apply symm_apply]
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩

/-- `PLift α` is equivalent to `α`. -/
@[simps (attr := grind =) -fullyApplied apply symm_apply]
protected def plift : PLift α ≃ α := ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩

/-- equivalence of propositions is the same as iff -/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q := ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[simps (attr := grind =) apply]
def arrowCongr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := by grind
  right_inv f := by grind

/--
@isnad1 id=eq.0h11v.s7.328a866b2465 from=seed src=0 shape=f00e2386 vocab=9b49b57e
-/
theorem arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ → β₁) (g : β₁ → γ₁) :
    arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f := by grind

/--
@isnad1 id=eq.0h2v.s4.1b33b027f1d7 from=seed src=0 shape=f76ec74c vocab=b11c6bb7
-/
@[simp] theorem arrowCongr_refl {α β : Sort*} :
    arrowCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) := rfl

/--
@isnad1 id=eq.0h10v.s6.a059cc2db7f3 from=seed src=0 shape=8bfa767b vocab=95d077ef
-/
@[simp] theorem arrowCongr_trans {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := rfl

/--
@isnad1 id=eq.0h6v.s5.b917d401f668 from=seed src=0 shape=fbf29ef5 vocab=cbaed184
-/
@[simp, grind =] theorem arrowCongr_symm {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := rfl

/-- A version of `Equiv.arrowCongr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `Equiv.arrowCongr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[simps! (attr := grind =) apply]
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ

/--
@isnad1 id=eq.0h2v.s4.fd332f6268c5 from=seed src=0 shape=2917e4f3 vocab=00c67bae
-/
@[simp] theorem arrowCongr'_refl {α β : Type*} :
    arrowCongr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) := rfl

/--
@isnad1 id=eq.0h10v.s6.4cf31b870c22 from=seed src=0 shape=20252226 vocab=c1f4951a
-/
@[simp] theorem arrowCongr'_trans {α₁ α₂ β₁ β₂ α₃ β₃ : Type*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.d9c530bda0ab from=seed src=0 shape=28a4482e vocab=bb1a91f8
-/
@[simp, grind =] theorem arrowCongr'_symm {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm := rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps! (attr := grind =) apply] def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrowCongr e e

/--
@isnad1 id=eq.0h1v.s4.a1c263846bc3 from=seed src=0 shape=1d001a59 vocab=63d4c074
-/
@[simp] theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α → α) := rfl

/--
@isnad1 id=eq.0h3v.s5.851d844a1e7a from=seed src=0 shape=400ba2b5 vocab=059dbeff
-/
@[simp, grind =] theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj := rfl

/--
@isnad1 id=eq.0h5v.s5.61cbd3a5bea6 from=seed src=0 shape=80f2f995 vocab=d3d3a915
-/
@[simp] theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (e₁.trans e₂).conj = e₁.conj.trans e₂.conj := rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := fun x ↦ x`. This causes nontermination.
/--
@isnad1 id=eq.0h5v.s7.91b1d7f3bb6e from=seed src=0 shape=ba8dc906 vocab=103781ff
-/
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by
  apply arrowCongr_comp

theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm

/--
@isnad1 id=iff.0h6v.s6.7d48834b6a22 from=seed src=0 shape=239e1401 vocab=b13a937e
-/
theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm

theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equiv.refl γ).arrowCongr e).eq_symm_apply

/--
@isnad1 id=iff.0h6v.s6.2cfea4de2fac from=seed src=0 shape=22d82b54 vocab=b13a937e
-/
theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equiv.refl γ).arrowCongr e).symm_apply_eq

/--
@isnad1 id=iff.0h4v.s5.539742b96095 from=seed src=0 shape=d0a3b35c vocab=9f8f4f38
-/
theorem trans_eq_refl_iff_eq_symm {f : α ≃ β} {g : β ≃ α} :
    f.trans g = Equiv.refl α ↔ f = g.symm := by
  rw [← Equiv.coe_inj, coe_trans, coe_refl, ← eq_symm_comp, comp_id, Equiv.coe_inj]

/--
@isnad1 id=iff.0h4v.s5.d329891082cc from=seed src=0 shape=95b28de9 vocab=9f8f4f38
-/
theorem trans_eq_refl_iff_symm_eq {f : α ≃ β} {g : β ≃ α} :
    f.trans g = Equiv.refl α ↔ f.symm = g := by
  rw [trans_eq_refl_iff_eq_symm]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ h ▸ rfl⟩

theorem eq_symm_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} :
    f = g.symm ↔ f.trans g = Equiv.refl α :=
  trans_eq_refl_iff_eq_symm.symm

/--
@isnad1 id=iff.0h4v.s5.1be8876d3e15 from=seed src=0 shape=1faab536 vocab=9f8f4f38
-/
theorem symm_eq_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} :
    f.symm = g ↔ f.trans g = Equiv.refl α :=
  trans_eq_refl_iff_symm_eq.symm

/-- `PUnit` sorts in any two universes are equivalent. -/
def punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} where
  toFun _ := .unit
  invFun _ := .unit

/-- `Prop` is noncomputably equivalent to `Bool`. -/
noncomputable def propEquivBool : Prop ≃ Bool where
  toFun p := @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp
  right_inv b := by simp

section

/-- The sort of maps to `PUnit.{v}` is equivalent to `PUnit.{w}`. -/
def arrowPUnitEquivPUnit (α : Sort*) : (α → PUnit.{v}) ≃ PUnit.{w} where
  toFun _ := .unit
  invFun _ _ := .unit

/-- The equivalence `(∀ i, β i) ≃ β ⋆` when the domain of `β` only contains `⋆` -/
@[simps (attr := grind =) -fullyApplied]
def piUnique [Unique α] (β : α → Sort*) : (∀ i, β i) ≃ β default where
  toFun f := f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps! (attr := grind =) -fullyApplied apply symm_apply]
def funUnique (α β) [Unique.{u} α] : (α → β) ≃ β := piUnique _

/-- The sort of maps from `PUnit` is equivalent to the codomain. -/
def punitArrowEquiv (α : Sort*) : (PUnit.{u} → α) ≃ α := funUnique PUnit.{u} α

/-- The sort of maps from `True` is equivalent to the codomain. -/
def trueArrowEquiv (α : Sort*) : (True → α) ≃ α := funUnique _ _

/-- The sort of maps from a type that `IsEmpty` is equivalent to `PUnit`. -/
def arrowPUnitOfIsEmpty (α β : Sort*) [IsEmpty α] : (α → β) ≃ PUnit.{u} where
  toFun _ := PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim

/-- The sort of maps from `Empty` is equivalent to `PUnit`. -/
def emptyArrowEquivPUnit (α : Sort*) : (Empty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

/-- The sort of maps from `PEmpty` is equivalent to `PUnit`. -/
def pemptyArrowEquivPUnit (α : Sort*) : (PEmpty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

/-- The sort of maps from `False` is equivalent to `PUnit`. -/
def falseArrowEquivPUnit (α : Sort*) : (False → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

end

section

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
def psigmaEquivSigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
def psigmaEquivSigmaPLift {α} (β : α → Sort*) : (Σ' i, β i) ≃ Σ i : PLift α, PLift (β i.down) where
  toFun a := ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps (attr := grind =) apply]
def psigmaCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind

/--
@isnad1 id=eq.0h6v.s6.54e746facf00 from=seed src=0 shape=d6f8c63c vocab=c5c05a7a
-/
theorem psigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Sort*}
    (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) =
      psigmaCongrRight fun a => (F a).trans (G a) := rfl

/--
@isnad1 id=eq.0h4v.s6.3a07a1be5a16 from=seed src=0 shape=458a22ff vocab=13d56cfc
-/
@[grind =]
theorem psigmaCongrRight_symm {α} {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm := rfl

/--
@isnad1 id=eq.0h2v.s5.64fe63f7eb50 from=seed src=0 shape=93633e2f vocab=e1fcb1e2
-/
@[simp]
theorem psigmaCongrRight_refl {α} {β : α → Sort*} :
    (psigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ' a, β a) := rfl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps (attr := grind =) apply]
def sigmaCongrRight {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind

/--
@isnad1 id=eq.0h6v.s6.d38634ac7d7a from=seed src=0 shape=47d2d9a1 vocab=5b1b38fe
-/
theorem sigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Type*}
    (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) =
      sigmaCongrRight fun a => (F a).trans (G a) := rfl

/--
@isnad1 id=eq.0h4v.s6.532ee647a9c1 from=seed src=0 shape=94e2e4c2 vocab=247a3738
-/
@[grind =]
theorem sigmaCongrRight_symm {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm := rfl

/--
@isnad1 id=eq.0h2v.s5.7252a1cc3147 from=seed src=0 shape=564a64ea vocab=965fbdd2
-/
@[simp]
theorem sigmaCongrRight_refl {α} {β : α → Type*} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) := rfl

/-- A `PSigma` with `Prop` fibers is equivalent to the subtype. -/
def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ' i, P i) ≃ Subtype P where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

/-- A `Sigma` with `PLift` fibers is equivalent to the subtype. -/
def sigmaPLiftEquivSubtype {α : Type v} (P : α → Prop) : (Σ i, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)

/-- A `Sigma` with `fun i ↦ ULift (PLift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigmaPLiftEquivSubtype`.
-/
def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α → Prop) :
    (Σ i, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)

namespace Perm

/-- A family of permutations `Π a, Perm (β a)` generates a permutation `Perm (Σ a, β₁ a)`. -/
abbrev sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σ a, β a) :=
  Equiv.sigmaCongrRight F

/--
@isnad1 id=eq.0h4v.s6.a13dcb109c98 from=seed src=0 shape=a1c9a32d vocab=e2841b17
-/
@[simp] theorem sigmaCongrRight_trans {α} {β : α → Sort _}
    (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.dd5103dbe622 from=seed src=0 shape=31d75b3f vocab=f2c248f9
-/
@[simp] theorem sigmaCongrRight_symm {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.45a880948cc6 from=seed src=0 shape=414c3085 vocab=1b8e5b2a
-/
@[simp] theorem sigmaCongrRight_refl {α} {β : α → Sort _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) :=
  rfl

end Perm

/-- `Function.swap` as an equivalence. -/
@[simps (attr := grind =) -fullyApplied]
def functionSwap (α β : Sort*) (γ : α → β → Sort*) :
    ((a : α) → (b : β) → γ a b) ≃ ((b : β) → (a : α) → γ a b) where
  toFun := Function.swap
  invFun := Function.swap

theorem _root_.Function.swap_bijective {α β : Sort*} {γ : α → β → Sort*} :
    Function.Bijective (@Function.swap _ _ γ) :=
  functionSwap _ _ _ |>.bijective

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps (attr := grind =) apply]
def sigmaCongrLeft {α₁ α₂ : Type*} {β : α₂ → Sort _} (e : α₁ ≃ α₂) :
    (Σ a : α₁, β (e a)) ≃ Σ a : α₂, β a where
  toFun a := ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  left_inv := fun ⟨a, b⟩ => by simp
  right_inv := fun ⟨a, b⟩ => by simp

/-- Transporting a sigma type through an equivalence of the base -/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) :
    (Σ a : α₁, β a) ≃ Σ a : α₂, β (f.symm a) := (sigmaCongrLeft f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)

/-- `Sigma` type with a constant fiber is equivalent to the product. -/
@[simps (attr := mfld_simps, grind =) apply symm_apply]
def sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≃ α × β where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/-- If each fiber of a `Sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)

/-- The dependent product of types is associative up to an equivalence. -/
def sigmaAssoc {α : Type*} {β : α → Type*} (γ : ∀ a : α, β a → Type*) :
    (Σ ab : Σ a : α, β a, γ ab.1 ab.2) ≃ Σ a : α, Σ b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/-- The dependent product of sorts is associative up to an equivalence. -/
def pSigmaAssoc {α : Sort*} {β : α → Sort*} (γ : ∀ a : α, β a → Sort*) :
    (Σ' ab : Σ' a : α, β a, γ ab.1 ab.2) ≃ Σ' a : α, Σ' b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

end

variable {p : α → Prop} {q : β → Prop} (e : α ≃ β)

/--
@isnad1 id=iff.0h4v.s5.078c1a6282db from=seed src=0 shape=0a25a8b3 vocab=c53aac11
-/
protected lemma forall_congr_right : (∀ a, q (e a)) ↔ ∀ b, q b :=
  ⟨fun h a ↦ by simpa using h (e.symm a), fun h _ ↦ h _⟩

/--
@isnad1 id=iff.0h4v.s5.2986a04803e2 from=seed src=0 shape=b8863744 vocab=eb0e1a8d
-/
protected lemma forall_congr_left : (∀ a, p a) ↔ ∀ b, p (e.symm b) :=
  e.symm.forall_congr_right.symm

/--
@isnad1 id=iff.1h5v.s5.c2a47e1a3ee8 from=seed src=0 shape=31aaa7bd vocab=c53aac11
-/
protected lemma forall_congr (h : ∀ a, p a ↔ q (e a)) : (∀ a, p a) ↔ ∀ b, q b :=
  e.forall_congr_left.trans (by simp [h])

/--
@isnad1 id=iff.1h5v.s5.eb0e4116ed47 from=seed src=0 shape=25fff31d vocab=eb0e1a8d
-/
protected lemma forall_congr' (h : ∀ b, p (e.symm b) ↔ q b) : (∀ a, p a) ↔ ∀ b, q b :=
  e.forall_congr_left.trans (by simp [h])

/--
@isnad1 id=iff.0h4v.s5.3b2824cbde7d from=seed src=0 shape=06b6369c vocab=c53aac11
-/
protected lemma exists_congr_right : (∃ a, q (e a)) ↔ ∃ b, q b :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h⟩, fun ⟨a, h⟩ ↦ ⟨e.symm a, by simpa using h⟩⟩

/--
@isnad1 id=iff.0h4v.s5.1571c0388f16 from=seed src=0 shape=659ed9a7 vocab=eb0e1a8d
-/
protected lemma exists_congr_left : (∃ a, p a) ↔ ∃ b, p (e.symm b) :=
  e.symm.exists_congr_right.symm

/--
@isnad1 id=iff.1h5v.s5.3bbfdfe6f279 from=seed src=0 shape=fa07c585 vocab=c53aac11
-/
protected lemma exists_congr (h : ∀ a, p a ↔ q (e a)) : (∃ a, p a) ↔ ∃ b, q b :=
  e.exists_congr_left.trans <| by simp [h]

/--
@isnad1 id=iff.1h5v.s5.188ab5a405e9 from=seed src=0 shape=073809de vocab=eb0e1a8d
-/
protected lemma exists_congr' (h : ∀ b, p (e.symm b) ↔ q b) : (∃ a, p a) ↔ ∃ b, q b :=
  e.exists_congr_left.trans <| by simp [h]

/--
@isnad1 id=iff.0h5v.s5.8bd756f78cd9 from=seed src=0 shape=1aabfd13 vocab=879eceb1
-/
protected lemma exists_subtype_congr (e : {a // p a} ≃ {b // q b}) : (∃ a, p a) ↔ ∃ b, q b := by
  simp [← nonempty_subtype, nonempty_congr e]

/--
@isnad1 id=iff.0h4v.s5.b41e25763351 from=seed src=0 shape=06b6369c vocab=859c31aa
-/
protected lemma existsUnique_congr_right : (∃! a, q (e a)) ↔ ∃! b, q b :=
  e.exists_congr <| by simpa using fun _ _ ↦ e.forall_congr (by simp)

/--
@isnad1 id=iff.0h4v.s5.bf30a8b395b1 from=seed src=0 shape=659ed9a7 vocab=f3f2a5bb
-/
protected lemma existsUnique_congr_left : (∃! a, p a) ↔ ∃! b, p (e.symm b) :=
  e.symm.existsUnique_congr_right.symm

/--
@isnad1 id=iff.1h5v.s5.bea6c52f0f5e from=seed src=0 shape=fa07c585 vocab=859c31aa
-/
protected lemma existsUnique_congr (h : ∀ a, p a ↔ q (e a)) : (∃! a, p a) ↔ ∃! b, q b :=
  e.existsUnique_congr_left.trans <| by simp [h]

/--
@isnad1 id=iff.1h5v.s5.18f69a3cf75d from=seed src=0 shape=073809de vocab=f3f2a5bb
-/
protected lemma existsUnique_congr' (h : ∀ b, p (e.symm b) ↔ q b) : (∃! a, p a) ↔ ∃! b, q b :=
  e.existsUnique_congr_left.trans <| by simp [h]

/--
@isnad1 id=iff.0h5v.s5.58d692a0407f from=seed src=0 shape=1aabfd13 vocab=94b5a27b
-/
protected lemma existsUnique_subtype_congr (e : {a // p a} ≃ {b // q b}) :
    (∃! a, p a) ↔ ∃! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        nonempty_congr e, subsingleton_congr e]

-- We next build some higher arity versions of `Equiv.forall_congr`.
-- Although they appear to just be repeated applications of `Equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)

/--
@isnad1 id=iff.1h8v.s6.7905da8d4978 from=seed src=0 shape=2c9162ed vocab=c53aac11
-/
protected theorem forall₂_congr {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) :
    (∀ x y, p x y) ↔ ∀ x y, q x y :=
  eα.forall_congr fun _ ↦ eβ.forall_congr <| @h _

/--
@isnad1 id=iff.1h8v.s6.96fdd322b297 from=seed src=0 shape=692c1c7b vocab=eb0e1a8d
-/
protected theorem forall₂_congr' {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
    (∀ x y, p x y) ↔ ∀ x y, q x y := (Equiv.forall₂_congr eα.symm eβ.symm h.symm).symm

/--
@isnad1 id=iff.1h11v.s7.bd6d2764e0e2 from=seed src=0 shape=96b56e31 vocab=c53aac11
-/
protected theorem forall₃_congr
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  Equiv.forall₂_congr _ _ <| Equiv.forall_congr _ <| @h _ _

/--
@isnad1 id=iff.1h11v.s7.2aa8abbfbdbe from=seed src=0 shape=168a153d vocab=eb0e1a8d
-/
protected theorem forall₃_congr'
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
    (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm h.symm).symm

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps (attr := grind =) apply]
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _

/--
@isnad1 id=eq.1h3v.s5.bf9f5ae858b8 from=seed src=0 shape=1349ab4b vocab=25330abd
-/
@[simp] lemma coe_ofBijective (f : α → β) (hf : Bijective f) : ⇑(ofBijective f hf) = f := rfl

/--
@isnad1 id=eq.0h3v.s5.d75e53cbd07b from=seed src=0 shape=67cd99ec vocab=48d399d5
-/
@[simp] lemma ofBijective_coe {f : α ≃ β} :
    Equiv.ofBijective f f.bijective = f := Equiv.ext (congrFun rfl)

/--
@isnad1 id=eq.1h4v.s5.d697075e43b1 from=seed src=0 shape=a20be93c vocab=0f5f2179
-/
lemma ofBijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

/--
@isnad1 id=eq.1h4v.s5.69f44611e407 from=seed src=0 shape=744ae47c vocab=0f5f2179
-/
@[simp]
lemma ofBijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

/-- Bijective functions are equivalent to equivalences. -/
@[simps]
noncomputable def bijectiveEquiv : { f : α → β // Bijective f } ≃ (α ≃ β) where
  toFun f := .ofBijective f f.prop
  invFun f := ⟨f, f.bijective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

end Equiv

namespace Quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.apply_symm_apply]

/--
@isnad1 id=eq.1h6v.s7.9b0392f0dfd4 from=seed src=0 shape=031540d5 vocab=1b3b344c
-/
@[simp] theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quot.congr e eq (Quot.mk ra a) = Quot.mk rb (e a) := rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ Quot r' := Quot.congr (Equiv.refl α) eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congrLeft {r : α → α → Prop} (e : α ≃ β) :
    Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    Quotient ra ≃ Quotient rb := Quot.congr e eq

/--
@isnad1 id=eq.1h6v.s7.be4c96cf5ddc from=seed src=0 shape=c9ae6a2f vocab=5a85796a
-/
@[simp] theorem congr_mk {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quotient.congr e eq (Quotient.mk ra a) = Quotient.mk rb (e a) := rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : Setoid α}
    (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quotient r ≃ Quotient r' :=
  Quot.congrRight eq

end Quotient

/-- Equivalence between `Fin 0` and `Empty`. -/
def finZeroEquiv : Fin 0 ≃ Empty := .equivEmpty _

/-- Equivalence between `Fin 0` and `PEmpty`. -/
def finZeroEquiv' : Fin 0 ≃ PEmpty.{u} := .equivPEmpty _

/-- Equivalence between `Fin 1` and `Unit`. -/
def finOneEquiv : Fin 1 ≃ Unit := .equivPUnit _

/-- Equivalence between `Fin 2` and `Bool`. -/
def finTwoEquiv : Fin 2 ≃ Bool where
  toFun i := i == 1
  invFun b := bif b then 1 else 0
  left_inv i := by grind
  right_inv b := by grind

namespace Equiv

variable {α β : Type*}

/-- The left summand of `α ⊕ β` is equivalent to `α`. -/
@[simps (attr := grind =)]
def sumIsLeft : {x : α ⊕ β // x.isLeft} ≃ α where
  toFun x := x.1.getLeft x.2
  invFun a := ⟨.inl a, Sum.isLeft_inl⟩
  left_inv | ⟨.inl _a, _⟩ => rfl

/-- The right summand of `α ⊕ β` is equivalent to `β`. -/
@[simps (attr := grind =)]
def sumIsRight : {x : α ⊕ β // x.isRight} ≃ β where
  toFun x := x.1.getRight x.2
  invFun b := ⟨.inr b, Sum.isRight_inr⟩
  left_inv | ⟨.inr _b, _⟩ => rfl

variable (e : α ≃ β)

/-- Transfer `LE` across an `Equiv`. -/
protected abbrev le [LE β] : LE α where
  le a b := e a ≤ e b

/--
@isnad1 id=iff.0h5v.s6.d672261fed00 from=seed src=0 shape=0d00de4a vocab=35ccad42
-/
lemma le_def [LE β] (a b : α) :
    letI := e.le
    e a ≤ e b ↔ a ≤ b := Iff.rfl

/-- Transfer `LT` across an `Equiv`. -/
protected abbrev lt [LT β] : LT α where
  lt a b := e a < e b

/--
@isnad1 id=iff.0h5v.s6.56b7fb2430f1 from=seed src=0 shape=0d00de4a vocab=26844470
-/
lemma lt_def [LT β] (a b : α) :
    letI := e.lt
    e a < e b ↔ a < b := Iff.rfl

/-- Transfer `Max` across an `Equiv`. -/
protected abbrev max [Max β] : Max α where
  max a b := e.symm (max (e a) (e b))

/--
@isnad1 id=eq.0h5v.s6.82ee8f8915ec from=seed src=0 shape=9f05f6fc vocab=a54ae9d4
-/
lemma max_def [Max β] (a b : α) :
    letI := e.max
    max a b = e.symm (max (e a) (e b)) := rfl

/-- Transfer `Min` across an `Equiv`. -/
protected abbrev min [Min β] : Min α where
  min a b := e.symm (min (e a) (e b))

/--
@isnad1 id=eq.0h5v.s6.17c6864cf110 from=seed src=0 shape=9f05f6fc vocab=cb46cea3
-/
lemma min_def [Min β] (a b : α) :
    letI := e.min
    min a b = e.symm (min (e a) (e b)) := rfl

/-- Transfer `Ord` across an `Equiv`. -/
protected abbrev ord [Ord β] : Ord α where
  compare a b := compare (e a) (e b)

/--
@isnad1 id=eq.0h5v.s6.ba26f4f6070c from=seed src=0 shape=68d0f654 vocab=06c52e07
-/
lemma ord_def [Ord β] (a b : α) :
    letI := e.ord
    compare a b = compare (e a) (e b) := rfl

end Equiv
