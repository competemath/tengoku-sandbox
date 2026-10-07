/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Tengoku.Seed.Data.Option.Basic
public import Tengoku.Seed.Data.Prod.Basic
public import Tengoku.Seed.Data.Prod.PProd
public import Tengoku.Seed.Data.Sum.Basic
public import Tengoku.Seed.Logic.Equiv.Basic
public import Tengoku.Seed.Logic.IsEmpty.Basic

/-!
# Injective functions
-/

@[expose] public section

universe u v w x

namespace Function

/-- `α ↪ β` is a bundled injective function. -/
structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α → β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun

/-- An embedding, a.k.a. a bundled injective function. -/
infixr:25 " ↪ " => Embedding

instance {α : Sort u} {β : Sort v} : FunLike (α ↪ β) α β where
  coe := Embedding.toFun
  coe_injective f g h := by { cases f; cases g; congr }

instance {α : Sort u} {β : Sort v} : EmbeddingLike (α ↪ β) α β where
  injective' := Embedding.inj'

initialize_simps_projections Embedding (toFun → apply)

instance {α β : Sort*} : CanLift (α → β) (α ↪ β) (↑) Injective where prf f hf := ⟨⟨f, hf⟩, rfl⟩

/--
@isnad1 id=iff.0h2v.s4.868bfb9fd4d4 from=seed src=0 shape=90ce8653 vocab=c01bf5d0
-/
theorem exists_surjective_iff {α β : Sort*} :
    (∃ f : α → β, Surjective f) ↔ Nonempty (α → β) ∧ Nonempty (β ↪ α) :=
  ⟨fun ⟨f, h⟩ ↦ ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ ↦ (nonempty_fun.mp h).elim
    (fun _ ↦ ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ ↦ ⟨_, invFun_surjective e.inj'⟩⟩

end Function

namespace Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `Equiv.coeEmbedding`.
The explicit `Equiv.toEmbedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f.toEmbedding = s.map f := by simp
-- Error, `f` has type `Fin 3 ≃ Fin 3` but is expected to have type `Fin 3 ↪ ?m_1 : Type ?`
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f = s.map f.toEmbedding := by simp
```
-/
@[reducible]
protected def toEmbedding : α ↪ β :=
  ⟨f, f.injective⟩

/--
@isnad1 id=eq.0h3v.s5.dfefe2a12525 from=seed src=0 shape=2fc87eb5 vocab=f7758a9d
-/
@[simp]
theorem coe_toEmbedding : (f.toEmbedding : α → β) = f :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.c1e268c2883f from=seed src=0 shape=d1c0e4d1 vocab=f7758a9d
-/
theorem toEmbedding_apply (a : α) : f.toEmbedding a = f a :=
  rfl

/--
@isnad1 id=injectiv.0h2v.s3.7e0b67790141 from=seed src=0 shape=40217037 vocab=36ad5db2
-/
theorem toEmbedding_injective : Function.Injective (Equiv.toEmbedding : (α ≃ β) → (α ↪ β)) :=
  fun _ _ h ↦ by rwa [DFunLike.ext'_iff] at h ⊢

instance coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equiv.toEmbedding⟩

end Equiv

namespace Function

namespace Embedding

/--
@isnad1 id=injectiv.0h2v.s4.a4b3f99e2383 from=seed src=0 shape=d8da120a vocab=a016b593
-/
theorem coe_injective {α β} : @Injective (α ↪ β) (α → β) (fun f ↦ ↑f) :=
  DFunLike.coe_injective

/--
@isnad1 id=eq.1h4v.s5.ab8fc3a6833d from=seed src=0 shape=149ba31d vocab=9a98cd91
-/
@[ext]
theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance {α β : Sort*} [IsEmpty α] : Unique (α ↪ β) where
  default := ⟨isEmptyElim, Function.injective_of_subsingleton _⟩
  uniq := by intro; ext v; exact isEmptyElim v

/--
@isnad1 id=eq.0h3v.s4.64534fc49877 from=seed src=0 shape=4bf4240a vocab=9216a3f9
-/
@[simp]
theorem toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.7cd65a0d51c6 from=seed src=0 shape=1349ab4b vocab=19e17222
-/
@[simp]
theorem coeFn_mk {α β} (f : α → β) (i) : (@mk _ _ f i : α → β) = f :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.f59bc03a7cf7 from=seed src=0 shape=34f34229 vocab=19e17222
-/
@[simp]
theorem mk_coe {α β : Type*} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f :=
  rfl

/--
@isnad1 id=injectiv.0h3v.s4.d7208c2e7b2a from=seed src=0 shape=8d068dd3 vocab=a016b593
-/
@[grind! .] -- This adds `Injective f` into the grind context for every embedding `f : α ↪ β`.
protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f

/--
@isnad1 id=iff.0h5v.s5.35ec77396c4f from=seed src=0 shape=4b07764f vocab=9a98cd91
-/
theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

/-- The identity map as a `Function.Embedding`. -/
@[refl, simps +simpRhs]
protected def refl (α : Sort*) : α ↪ α :=
  ⟨id, injective_id⟩

/--
@isnad1 id=eq.0h1v.s4.ffeb51e1f7bf from=seed src=0 shape=f527b7d1 vocab=aba9367d
-/
@[norm_cast]
theorem coe_refl (α : Sort*) : ⇑(Embedding.refl α) = id := rfl

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps +simpRhs]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.injective.comp f.injective⟩

/--
@isnad1 id=eq.0h5v.s5.443d54712c0c from=seed src=0 shape=c1c49f9d vocab=700f9380
-/
@[norm_cast]
theorem coe_trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : ⇑(f.trans g) = ⇑g ∘ ⇑f := rfl

/--
@isnad1 id=eq.0h3v.s4.c976e9fc09df from=seed src=0 shape=a5aaf17e vocab=d4e35722
-/
@[simp]
theorem refl_trans {α β : Type*} (f : α ↪ β) : .trans (.refl α) f = f :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.d8b3f1c65599 from=seed src=0 shape=0b17db3e vocab=d4e35722
-/
@[simp]
theorem trans_refl {α β : Type*} (f : α ↪ β) : .trans f (.refl β) = f :=
  rfl

/--
@isnad1 id=eq.0h7v.s5.932f0c8a8ac4 from=seed src=0 shape=1b6cb8ea vocab=f75e194e
-/
theorem trans_assoc {α β γ δ : Type*} (f : α ↪ β) (g : β ↪ γ) (h : γ ↪ δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

instance : Trans Embedding Embedding Embedding := ⟨Embedding.trans⟩

/--
@isnad1 id=eq.0h1v.s3.50e48de644d4 from=seed src=0 shape=6cea78b2 vocab=aa88b78c
-/
@[simp] lemma mk_id {α} : mk id injective_id = .refl α := rfl

/--
@isnad1 id=eq.2h5v.s5.665e4a8dff85 from=seed src=0 shape=d3c33503 vocab=8e8e102a
-/
@[simp] lemma mk_trans_mk {α β γ} (f : α → β) (g : β → γ) (hf hg) :
    (mk f hf).trans (mk g hg) = mk (g ∘ f) (hg.comp hf) := rfl

/--
@isnad1 id=eq.0h3v.s4.37010817a2b0 from=seed src=0 shape=56259398 vocab=4a2722f0
-/
theorem equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by
  simp

/--
@isnad1 id=eq.0h3v.s4.8084daa39bee from=seed src=0 shape=55c1f82e vocab=4a2722f0
-/
theorem equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by
  simp

/-- Transfer an embedding along a pair of equivalences. -/
@[simps! -fullyApplied +simpRhs]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)

/-- A right inverse `surjInv` of a surjective function as an `Embedding`. -/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩

/-- Convert a surjective `Embedding` to an `Equiv` -/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.injective, hf⟩

/-- Surjective embeddings are equivalent to equivalences. -/
@[simps]
noncomputable def _root_.Equiv.embeddingSurjectiveEquiv {α β} :
    { f : α ↪ β // Surjective f } ≃ (α ≃ β) where
  toFun f := f.val.equivOfSurjective f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/-- There is always an embedding from an empty type. -/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def setValue {α β : Sort*} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    grind⟩

/--
@isnad1 id=eq.0h5v.s5.1e77e267dd92 from=seed src=0 shape=e3012ea3 vocab=ee443a3b
-/
@[simp]
theorem setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a = b := by
  simp [setValue]

/--
@isnad1 id=iff.0h6v.s6.63caaa2488e5 from=seed src=0 shape=c6f76164 vocab=ee443a3b
-/
@[simp]
theorem setValue_eq_iff {α β} (f : α ↪ β) {a a' : α} {b : β} [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a' = b ↔ a' = a :=
  (setValue f a b).injective.eq_iff' <| setValue_eq ..

/--
@isnad1 id=eq.2h6v.s6.6b78ae143a84 from=seed src=0 shape=18ab845e vocab=ee443a3b
-/
lemma setValue_eq_of_ne {α β} {f : α ↪ β} {a : α} {b : β} {c : α} [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] (hc : c ≠ a) (hb : f c ≠ b) : setValue f a b c = f c := by
  simp [setValue, hc, hb]

/--
@isnad1 id=eq.0h5v.s6.8b73cadf2f90 from=seed src=0 shape=dd9c2464 vocab=ee443a3b
-/
@[simp]
lemma setValue_right_apply_eq {α β} (f : α ↪ β) (a c : α) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = f c)] : setValue f a (f c) c = f a := by
  simp [setValue]

/-- Embedding into `Option α` using `some`. -/
@[simps -fullyApplied]
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩

/-- A version of `Option.map` for `Function.Embedding`s. -/
@[simps -fullyApplied]
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.injective⟩

/-- Embedding of a `Subtype`. -/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨Subtype.val, fun _ _ => Subtype.ext⟩

/--
@isnad1 id=eq.0h3v.s5.9b4620b4e908 from=seed src=0 shape=9a38c36a vocab=b02cdd2e
-/
@[simp]
theorem subtype_apply {α} {p : α → Prop} (x : Subtype p) : subtype p x = x :=
  rfl

/--
@isnad1 id=injectiv.0h2v.s5.5045e24d6cee from=seed src=0 shape=6b56d4c0 vocab=321ec74c
-/
theorem subtype_injective {α} (p : α → Prop) : Function.Injective (subtype p) :=
  Subtype.coe_injective

/--
@isnad1 id=eq.0h2v.s5.1678621ed4ff from=seed src=0 shape=e13e3118 vocab=b02cdd2e
-/
@[simp]
theorem coe_subtype {α} (p : α → Prop) : ↑(subtype p) = Subtype.val :=
  rfl

/-- `Quotient.out` as an embedding. -/
noncomputable def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩

/--
@isnad1 id=eq.0h1v.s5.d5e8021f7309 from=seed src=0 shape=421494ff vocab=1a1ae9b0
-/
@[simp]
theorem coe_quotientOut (α) [Setoid α] : ↑(quotientOut α) = Quotient.out :=
  rfl

/-- Choosing an element `b : β` gives an embedding of `PUnit` into `β`. -/
def punit {β : Sort*} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩

/-- The equivalence `one ↪ α` with `α`, for `Unique one`. -/
def oneEmbeddingEquiv {one α : Type*} [Unique one] : (one ↪ α) ≃ α where
  toFun f := f default
  invFun a := {
    toFun := fun _ ↦ a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
def sectL (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
def sectR {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩

/-- If `e₁` and `e₂` are embeddings, then so is `Prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.injective.prodMap e₂.injective⟩

/--
@isnad1 id=eq.0h6v.s6.9c999567c375 from=seed src=0 shape=d0147cff vocab=980b3150
-/
@[simp]
theorem coe_prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
    e₁.prodMap e₂ = Prod.map e₁ e₂ :=
  rfl

/-- If `e₁` and `e₂` are embeddings,
  then so is `fun ⟨a, b⟩ ↦ ⟨e₁ a, e₂ b⟩ : PProd α γ → PProd β δ`. -/
def pprodMap {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

section Sum

open Sum

/-- If `e₁` and `e₂` are embeddings, then so is `Sum.map e₁ e₂`. -/
def sumMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α ⊕ γ ↪ β ⊕ δ :=
  ⟨Sum.map e₁ e₂, e₁.injective.sumMap e₂.injective⟩

/--
@isnad1 id=eq.0h6v.s6.fcd779d78974 from=seed src=0 shape=d0147cff vocab=35d44c8e
-/
@[simp]
theorem coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : sumMap e₁ e₂ = Sum.map e₁ e₂ :=
  rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
def inl {α β : Type*} : α ↪ α ⊕ β :=
  ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
def inr {α β : Type*} : β ↪ α ⊕ β :=
  ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩

end Sum

section Sigma

variable {α α' : Type*} {β : α → Type*} {β' : α' → Type*}

/-- `Sigma.mk` as a `Function.Embedding`. -/
@[simps apply]
def sigmaMk (a : α) : β a ↪ Σ x, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩

attribute [grind =] sigmaMk_apply

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `Sigma.map f g` is an embedding. -/
@[simps apply]
def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σ a, β a) ↪ Σ a', β' a' :=
  ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩

end Sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `fun a ↦ e a (f a)`. -/
@[simps]
def piCongrRight {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩

/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e

/--
@isnad1 id=eq.0h5v.s6.d9e299a45440 from=seed src=0 shape=c7edabc0 vocab=7e2507e6
-/
@[simp]
theorem arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ → α) :
    arrowCongrRight e f = e ∘ f :=
  rfl

/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩

-- `simps` would generate this over-applied
/--
@isnad1 id=eq.0h5v.s6.4b0c9abe7d64 from=seed src=0 shape=c56d0d86 vocab=d7bd782a
-/
@[simp]
theorem arrowCongrLeft_apply {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
    (f : α → γ) :
    arrowCongrLeft e f = extend e f default :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.25ba6cc679da from=seed src=0 shape=df344318 vocab=831e8ab1
-/
@[simp]
theorem arrowCongrLeft_refl {α : Sort u} {γ : Sort w} [Inhabited γ] :
    (Function.Embedding.refl α).arrowCongrLeft (γ := γ) = .refl _ := by
  ext
  simp [coe_refl]

/--
@isnad1 id=eq.0h6v.s5.842dff7f3537 from=seed src=0 shape=148c5040 vocab=807d4add
-/
@[simp]
theorem trans_arrowCongrLeft {α₁ : Sort u} {α₂ : Sort v} {α₃ : Sort x} {γ : Sort w}
    [Inhabited γ] (e₁₂ : α₁ ↪ α₂) (e₂₃ : α₂ ↪ α₃) :
    e₁₂.arrowCongrLeft.trans e₂₃.arrowCongrLeft = (e₁₂.trans e₂₃).arrowCongrLeft (γ := γ) := by
  ext f a
  simp only [trans_apply, arrowCongrLeft_apply, Pi.default_def, coe_trans]
  rw [e₁₂.injective.extend_comp e₂₃.injective, Function.comp_def]

/-- Restrict both domain and codomain of an embedding. -/
protected def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
    (h : ∀ ⦃x⦄, p x → q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩

open Set

/--
@isnad1 id=eq.0h6v.s6.39b9c95dafc8 from=seed src=0 shape=43802fd5 vocab=e2bfbc05
-/
theorem swap_apply {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  f.injective.swap_apply x y z

/--
@isnad1 id=eq.0h5v.s6.e5d584c4014f from=seed src=0 shape=7a61000d vocab=8a1ec2b9
-/
theorem swap_comp {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  f.injective.swap_comp x y

end Embedding

end Function

namespace Equiv

open Function Embedding

/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps!]
def asEmbedding {β α : Sort*} {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  e.toEmbedding.trans (subtype p)

/-- The type of embeddings `α ↪ β` is equivalent to
the subtype of all injective functions `α → β`. -/
def subtypeInjectiveEquivEmbedding (α β : Sort*) :
    { f : α → β // Injective f } ≃ (α ↪ β) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩

/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[simps apply]
def embeddingCongr {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) where
  toFun f := f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

/--
@isnad1 id=eq.0h2v.s4.8a61b84d8384 from=seed src=0 shape=f79ec984 vocab=03f44d14
-/
@[simp]
theorem embeddingCongr_refl {α β : Sort*} :
    embeddingCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ↪ β) :=
  rfl

/--
@isnad1 id=eq.0h10v.s6.6f57266b075d from=seed src=0 shape=07123048 vocab=cdb2bae1
-/
@[simp]
theorem embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.53991e9c66c2 from=seed src=0 shape=9965395b vocab=bcb8e0a9
-/
@[simp]
theorem embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl

/--
@isnad1 id=eq.0h11v.s7.8a20d80d6eeb from=seed src=0 shape=e45c6584 vocab=acc3057a
-/
theorem embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
    (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equiv.embeddingCongr ea ec (f.trans g) =
      (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb ec g) := by
  ext
  simp

/--
@isnad1 id=eq.0h1v.s3.0b755eff3ffb from=seed src=0 shape=6a4c69a9 vocab=1cd6c74f
-/
@[simp]
theorem refl_toEmbedding {α : Type*} : (Equiv.refl α).toEmbedding = Embedding.refl α :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.acdcc56a112f from=seed src=0 shape=1a025900 vocab=82926b83
-/
@[simp]
theorem trans_toEmbedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl

end Equiv

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ { x // p x } ⊕ { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩

/--
@isnad1 id=eq.0h5v.s7.98db4e52bd78 from=seed src=0 shape=5ccf0d49 vocab=9957bec9
-/
@[simp]
theorem subtypeOrLeftEmbedding_apply_left {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : p x) :
    subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dite_eq_left hx

/--
@isnad1 id=eq.1h4v.s7.7c660446cda0 from=seed src=0 shape=007a96c7 vocab=eb024619
-/
@[simp]
theorem subtypeOrLeftEmbedding_apply_right {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.prop.resolve_left hx⟩ :=
  dite_eq_right hx

/--
@isnad1 id=eq.0h4v.s8.5ab37de977b6 from=seed src=0 shape=915b66bd vocab=614b29a6
-/
@[grind =]
theorem subtypeOrLeftEmbedding_apply {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) :
    subtypeOrLeftEmbedding p q x =
      if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩ :=
  rfl

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps (attr := grind =)]
def Subtype.impEmbedding (p q : α → Prop) (h : ∀ x, p x → q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩

end Subtype
