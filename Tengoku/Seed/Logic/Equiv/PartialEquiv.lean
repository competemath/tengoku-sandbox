/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Tengoku.Seed.Data.Set.Piecewise
public import Tengoku.Seed.Logic.Equiv.Defs
public import Tengoku.Seed.Tactic.Core
public import Tengoku.Seed.Tactic.Attr.Core

/-!
# Partial equivalences

This file defines equivalences between subsets of given types.
An element `e` of `PartialEquiv α β` is made of two maps `e.toFun` and `e.invFun` respectively
from α to β and from β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two partial equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.toFun x` and `e.invFun y`.

## Main definitions

* `Equiv.toPartialEquiv`: associating a partial equiv to an equiv, with source = target = univ
* `PartialEquiv.symm`: the inverse of a partial equivalence
* `PartialEquiv.trans`: the composition of two partial equivalences
* `PartialEquiv.refl`: the identity partial equivalence
* `PartialEquiv.ofSet`: the identity on a set `s`
* `EqOnSource`: equivalence relation describing the "right" notion of equality for partial
  equivalences (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of partial equivalences:
* equivs on subtypes
* pairs of functions taking values in `Option α` and `Option β`, equal to none where the partial
  equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
  restriction of domains. Checking that one always belongs to the right subtype makes things very
  tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
  instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
  the domain is restricted automatically). These are implemented in `PEquiv.lean`. For manifolds,
  where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
  overhead as one would need to extend all classes of smoothness to option-valued maps.
* The `PartialEquiv` version as explained above is easier to use for manifolds. The drawback is that
  there is extra useless data (the values of `toFun` and `invFun` outside of `source` and `target`).
  In particular, the equality notion between partial equivs is not "the right one", i.e., coinciding
  source and target and equality there. Moreover, there are no partial equivs in this sense between
  an empty type and a nonempty type. Since empty types are not that useful, and since one almost
  never needs to talk about equal partial equivs, this is not an issue in practice.
  Still, we introduce an equivalence relation `EqOnSource` that captures this right notion of
  equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/

@[expose] public section
open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`PartialEquiv`, `OpenPartialHomeomorph`, etc).

This is in a separate file from `Mathlib/Tactic/Attr/Register.lean` because attributes need a
new file to become functional.
-/

namespace Mathlib.Tactic.MfldSetTac

/-- A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another. -/
elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      apply Set.ext; intro my_y
      constructor <;>
        · intro h_my_y
          try simp only [*, mfld_simps] at h_my_y
          try simp only [*, mfld_simps])))
  | (``LE.le, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      intro my_y h_my_y
      try simp only [*, mfld_simps] at h_my_y
      try simp only [*, mfld_simps])))
  | _ => throwError "goal should be an equality or an inclusion"

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply

end Mathlib.Tactic.MfldSetTac

open Function Set

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Local equivalence between subsets `source` and `target` of `α` and `β` respectively. The
(global) maps `toFun : α → β` and `invFun : β → α` map `source` to `target` and conversely, and are
inverse to each other there. The values of `toFun` outside of `source` and of `invFun` outside of
`target` are irrelevant. -/
structure PartialEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a partial inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α → β
  /-- The partial inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β → α
  /-- The domain of the partial equivalence. -/
  source : Set α
  /-- The codomain of the partial equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
  /-- The proposition that `invFun` is a left-inverse of `toFun` on `source`. -/
  left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  /-- The proposition that `invFun` is a right-inverse of `toFun` on `target`. -/
  right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x

attribute [coe] PartialEquiv.toFun

namespace PartialEquiv

variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

instance [Inhabited α] [Inhabited β] : Inhabited (PartialEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

/-- The inverse of a partial equivalence -/
@[symm]
protected def symm : PartialEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'

instance : CoeFun (PartialEquiv α β) fun _ => α → β :=
  ⟨PartialEquiv.toFun⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : PartialEquiv α β) : β → α :=
  e.symm

initialize_simps_projections PartialEquiv (toFun → apply, invFun → symm_apply)

/--
@isnad1 id=eq.4h6v.s6.fed26ba56971 from=seed src=0 shape=63c57f49 vocab=5de7a0b2
-/
theorem coe_mk (f : α → β) (g s t ml mr il ir) :
    (PartialEquiv.mk f g s t ml mr il ir : α → β) = f := rfl

/--
@isnad1 id=eq.4h6v.s6.b975fb9686d1 from=seed src=0 shape=9687ff4e vocab=a79f33b9
-/
@[simp, mfld_simps]
theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
    ((PartialEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.0cdcb3ee7cf6 from=seed src=0 shape=f9866a73 vocab=f18916ef
-/
@[simp, mfld_simps]
theorem invFun_as_coe : e.invFun = e.symm :=
  rfl

/--
@isnad1 id=mem.1h4v.s5.3786e58884a4 from=seed src=0 shape=7ac0bf44 vocab=5962a607
-/
@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

/-- Variant of `e.map_source` and `map_source'`, stated for images of subsets of `source`.
@isnad1 id=le.0h3v.s4.4a132e7a4a10 from=seed src=0 shape=a3dd9331 vocab=2ace7b73
-/
lemma image_source_subset : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

/--
@isnad1 id=le.0h3v.s4.4a132e7a4a10 from=seed src=0 shape=a3dd9331 vocab=2ace7b73
-/
@[deprecated (since := "2026-06-17")] alias map_source'' := image_source_subset

/--
@isnad1 id=mem.1h4v.s5.c0813c67fdb1 from=seed src=0 shape=21e019a9 vocab=34220e7e
-/
@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

/--
@isnad1 id=eq.1h4v.s5.a95808b4375c from=seed src=0 shape=2422a8be vocab=7825945b
-/
@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

/--
@isnad1 id=eq.1h4v.s5.1e89d47bd5fe from=seed src=0 shape=f9cb9be5 vocab=ffe2c1c7
-/
@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h

/--
@isnad1 id=le.0h3v.s4.b3b6caa6206d from=seed src=0 shape=7b2e4a7c vocab=20cd9cef
-/
theorem target_subset_range : e.target ⊆ range e :=
  fun x hx ↦ ⟨e.symm x, right_inv e hx⟩

/--
@isnad1 id=iff.2h5v.s5.a5ec1d3c71c2 from=seed src=0 shape=3b1c2649 vocab=34220e7e
-/
theorem symm_apply_eq {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    e.symm y = x ↔ y = e x :=
  ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y := by
  simp [eq_comm, ← symm_apply_eq e hx hy]

/--
@isnad1 id=mapsto.0h3v.s4.0f4d20af3198 from=seed src=0 shape=f189f322 vocab=0b2be288
-/
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

/--
@isnad1 id=mapsto.0h3v.s4.8be36f097b74 from=seed src=0 shape=b7ede6d0 vocab=f113dcd0
-/
theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

/--
@isnad1 id=mapsto.0h3v.s4.8be36f097b74 from=seed src=0 shape=b7ede6d0 vocab=f113dcd0
-/
@[deprecated (since := "2026-05-18")] alias symm_mapsTo := mapsTo_symm

/--
@isnad1 id=leftinvo.0h3v.s4.42e61af6c02f from=seed src=0 shape=3dfecd00 vocab=053ae5bd
-/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv

/--
@isnad1 id=rightinv.0h3v.s4.d995e93dc58f from=seed src=0 shape=3dfecd00 vocab=5eb4697f
-/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv

/--
@isnad1 id=invon.0h3v.s4.e1ce153ff5b9 from=seed src=0 shape=53e54c3a vocab=c4a8e264
-/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩

/--
@isnad1 id=injon.0h3v.s4.bca4aba72506 from=seed src=0 shape=fd1749ae vocab=8c223044
-/
protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn

/--
@isnad1 id=bijon.0h3v.s4.fab7a0dd98f5 from=seed src=0 shape=f189f322 vocab=ea89eb37
-/
protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.mapsTo_symm

/--
@isnad1 id=surjon.0h3v.s4.e644436363e0 from=seed src=0 shape=f189f322 vocab=0aa398f5
-/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

/-- Interpret an `Equiv` as a `PartialEquiv` by restricting it to `s` in the domain
and to `t` in the codomain. -/
@[simps -fullyApplied]
def _root_.Equiv.toPartialEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
    PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := s
  target := t
  map_source' _ hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

/-- Associate a `PartialEquiv` to an `Equiv`. -/
@[simps! (attr := mfld_simps) -fullyApplied]
def _root_.Equiv.toPartialEquiv (e : α ≃ β) : PartialEquiv α β :=
  e.toPartialEquivOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]

instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (PartialEquiv α β) :=
  ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩

/-- Create a copy of a `PartialEquiv` providing better definitional equalities. -/
@[simps -fullyApplied]
def copy (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    PartialEquiv α β where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv

/--
@isnad1 id=eq.4h7v.s6.f88ed0423676 from=seed src=0 shape=4d566558 vocab=9e1681ff
-/
theorem copy_eq (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g)
    (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    e.copy f hf g hg s hs t ht = e := by
  subst f g s t
  cases e
  rfl

/-- Associate to a `PartialEquiv` an `Equiv` between the source and the target. -/
protected def toEquiv : e.source ≃ e.target where
  toFun x := ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.ext <| e.left_inv hx
  right_inv := fun ⟨_, hy⟩ => Subtype.ext <| e.right_inv hy

/--
@isnad1 id=eq.0h3v.s6.39bb17a04a70 from=seed src=0 shape=96540611 vocab=00d91002
-/
lemma toEquiv_eq_codRestrict_restrict :
    e.toEquiv = codRestrict (e.source.domRestrict e) e.target (by simp) :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.fab47ab27584 from=seed src=0 shape=7382c648 vocab=3c4f8cd7
-/
lemma toEquiv_symm_eq_codRestrict_restrict :
    e.toEquiv.symm = codRestrict (e.target.domRestrict e.invFun) e.source (by simp) := by
  rfl

/--
@isnad1 id=eq.0h3v.s4.684735fd7316 from=seed src=0 shape=d197e048 vocab=6d578b29
-/
@[simp, mfld_simps]
theorem symm_source : e.symm.source = e.target :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.1816ff709478 from=seed src=0 shape=d6bb0dce vocab=6d578b29
-/
@[simp, mfld_simps]
theorem symm_target : e.symm.target = e.source :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.fec4f6e300d7 from=seed src=0 shape=143197b8 vocab=fe7dd5b5
-/
@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e := rfl

/--
@isnad1 id=bijectiv.0h2v.s3.2333b7f46a74 from=seed src=0 shape=a0bd6008 vocab=61a7830b
-/
theorem symm_bijective :
    Function.Bijective (PartialEquiv.symm : PartialEquiv α β → PartialEquiv β α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
@isnad1 id=eq.0h3v.s4.f0a3913ef53b from=seed src=0 shape=a3dd9331 vocab=0c8838c5
-/
theorem image_source_eq_target : e '' e.source = e.target :=
  e.bijOn.image_eq

/--
@isnad1 id=iff.0h4v.s5.e8ecd2c5571a from=seed src=0 shape=2a7ff401 vocab=5962a607
-/
theorem forall_mem_target {p : β → Prop} : (∀ y ∈ e.target, p y) ↔ ∀ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, forall_mem_image]

/--
@isnad1 id=iff.0h4v.s5.f9af9babec59 from=seed src=0 shape=1eeb7a71 vocab=5962a607
-/
theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.target, p y) ↔ ∃ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, exists_mem_image]

/-- We say that `t : Set β` is an image of `s : Set α` under a partial equivalence if
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α}

/--
@isnad1 id=iff.2h6v.s5.18ceaa9760bb from=seed src=0 shape=08bb918f vocab=868a9800
-/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx

/--
@isnad1 id=iff.2h6v.s5.165de13b7bca from=seed src=0 shape=859f5063 vocab=9623aa88
-/
theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.target → (e.symm y ∈ s ↔ y ∈ t) :=
  e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]

/--
@isnad1 id=isimage.1h5v.s4.608040e32aa4 from=seed src=0 shape=1bbe8a8a vocab=d453e813
-/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff

/--
@isnad1 id=iff.0h5v.s4.aad31fd681ad from=seed src=0 shape=b8b5002a vocab=d453e813
-/
@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/--
@isnad1 id=mapsto.1h5v.s5.9f31ab89a040 from=seed src=0 shape=7641208e vocab=7881af6a
-/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩

/--
@isnad1 id=mapsto.1h5v.s5.c83100f23f24 from=seed src=0 shape=2a3b3440 vocab=ea3e5693
-/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo

/-- Restrict a `PartialEquiv` to a pair of corresponding sets. -/
@[simps -fullyApplied]
def restr (h : e.IsImage s t) : PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := e.source ∩ s
  target := e.target ∩ t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono inter_subset_left
  right_inv' := e.rightInvOn.mono inter_subset_left

/--
@isnad1 id=eq.1h5v.s5.b4b9a58a53e0 from=seed src=0 shape=366bf4d7 vocab=a1a8ff67
-/
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.restr.image_source_eq_target

/--
@isnad1 id=eq.1h5v.s5.09ab80b5d1dd from=seed src=0 shape=f9e002b6 vocab=40eaa65d
-/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq

/--
@isnad1 id=iff.0h5v.s5.13e6465fcf7a from=seed src=0 shape=30317b93 vocab=8f87f8c2
-/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s := by
  simp only [IsImage, Set.ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

/--
@isnad1 id=iff.0h5v.s5.3ab7575ac365 from=seed src=0 shape=99c6d4a0 vocab=882c30b9
-/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

/--
@isnad1 id=isimage.1h5v.s5.8c2941db78dd from=seed src=0 shape=69e0303c vocab=a1a8ff67
-/
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  of_symm_preimage_eq <| Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

/--
@isnad1 id=isimage.1h5v.s5.e6893abd64f5 from=seed src=0 shape=443ca12f vocab=40eaa65d
-/
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  of_preimage_eq <| Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h

/--
@isnad1 id=isimage.1h5v.s5.79c1d941e55a from=seed src=0 shape=c1ae1380 vocab=2f977fcb
-/
protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => not_congr (h hx)

/--
@isnad1 id=isimage.2h7v.s5.ae967f2e0e69 from=seed src=0 shape=a5b49e67 vocab=e178b7f7
-/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => and_congr (h hx) (h' hx)

/--
@isnad1 id=isimage.2h7v.s5.fa6209764d00 from=seed src=0 shape=a5b49e67 vocab=104e3863
-/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => or_congr (h hx) (h' hx)

/--
@isnad1 id=isimage.2h7v.s5.c3670984c0b5 from=seed src=0 shape=a5b49e67 vocab=67bff137
-/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

/--
@isnad1 id=leftinvo.2h6v.s6.7f7667bad886 from=seed src=0 shape=eeabc746 vocab=fd1712d7
-/
theorem leftInvOn_piecewise {e' : PartialEquiv α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  · rw [piecewise_eq_of_notMem _ _ _ hs, piecewise_eq_of_notMem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]

/--
@isnad1 id=eq.4h6v.s6.2238cb3df1f9 from=seed src=0 shape=d127b714 vocab=d8cf94e2
-/
theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t := by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]

/--
@isnad1 id=eqon.3h6v.s6.33ebf9351745 from=seed src=0 shape=00438ef6 vocab=d6486d24
-/
theorem symm_eq_on_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) := by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1, heq hx, e'.left_inv hx'.1]

end IsImage

/--
@isnad1 id=isimage.0h3v.s4.539205ddf0e7 from=seed src=0 shape=b5905826 vocab=0cc082b0
-/
theorem isImage_source_target : e.IsImage e.source e.target := fun x hx => by simp [hx]

/--
@isnad1 id=isimage.2h4v.s6.cdce42d0caee from=seed src=0 shape=5c252d6b vocab=397018db
-/
theorem isImage_source_target_of_disjoint (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.target :=
  IsImage.of_image_eq <| by rw [hs.inter_eq, ht.inter_eq, image_empty]

/--
@isnad1 id=eq.0h4v.s5.0da7b7400859 from=seed src=0 shape=16f096dc vocab=04fc5ffc
-/
theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s := by
  rw [inter_comm, e.leftInvOn.image_inter', image_source_eq_target, inter_comm]

/--
@isnad1 id=eq.0h4v.s5.852455aedfca from=seed src=0 shape=fa97868c vocab=04fc5ffc
-/
theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) := by
  rw [inter_comm, e.leftInvOn.image_inter, image_source_eq_target, inter_comm]

/--
@isnad1 id=eq.1h4v.s5.5ff4b2224ac7 from=seed src=0 shape=a93b7c2c vocab=9ee3036f
-/
theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq', inter_eq_self_of_subset_right h]

/--
@isnad1 id=eq.1h4v.s5.e0ea765f4595 from=seed src=0 shape=6a4f0c1d vocab=9ee3036f
-/
theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

/--
@isnad1 id=eq.0h4v.s5.15a297b7269d from=seed src=0 shape=ccca7bca vocab=04fc5ffc
-/
theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _

/--
@isnad1 id=eq.0h4v.s5.73d5a44ac942 from=seed src=0 shape=a0d85c60 vocab=04fc5ffc
-/
theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.symm.image_source_inter_eq' _

/--
@isnad1 id=eq.0h4v.s5.3693cac75213 from=seed src=0 shape=e6fb7b9e vocab=d4baf1c9
-/
theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' e.symm ⁻¹' s = e.source ∩ s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]

/--
@isnad1 id=eq.0h4v.s5.970c2879294d from=seed src=0 shape=ddfe408e vocab=28f418b5
-/
theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩

/--
@isnad1 id=eq.0h4v.s5.24e1b4e3d24e from=seed src=0 shape=0ffd171e vocab=e9aa6bf6
-/
theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' e ⁻¹' s = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

/--
@isnad1 id=eq.1h4v.s5.a9ac304f4a0d from=seed src=0 shape=d5bbbd52 vocab=8c0e3f7b
-/
theorem symm_image_image_of_subset_source {s : Set α} (h : s ⊆ e.source) : e.symm '' e '' s = s :=
  (e.leftInvOn.mono h).image_image

/--
@isnad1 id=eq.1h4v.s5.f954940002ff from=seed src=0 shape=8f577241 vocab=8a3b26cd
-/
theorem image_symm_image_of_subset_target {s : Set β} (h : s ⊆ e.target) : e '' e.symm '' s = s :=
  e.symm.symm_image_image_of_subset_source h

/--
@isnad1 id=le.0h3v.s4.08d95e26f424 from=seed src=0 shape=bad8d3d7 vocab=ae79ac2c
-/
theorem source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo

/--
@isnad1 id=eq.0h3v.s4.d5ecf7accec5 from=seed src=0 shape=c90d7f38 vocab=fd35ed3a
-/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

/--
@isnad1 id=le.0h3v.s4.94cdf7ae229b from=seed src=0 shape=a1d75e33 vocab=b96f6677
-/
theorem target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
  e.mapsTo_symm

/-- Two partial equivs that have the same `source`, same `toFun` and same `invFun`, coincide.
@isnad1 id=eq.3h4v.s6.4738ddb04a13 from=seed src=0 shape=dee88fdb vocab=7f495aff
-/
@[ext]
protected theorem ext {e e' : PartialEquiv α β} (h : ∀ x, e x = e' x)
    (hsymm : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' := by
  have A : (e : α → β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β → α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A, hs, I'] at I
  cases e; cases e'
  simp_all

/-- Restricting a partial equivalence to `e.source ∩ s` -/
protected def restr (s : Set α) : PartialEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

/--
@isnad1 id=eq.0h4v.s4.b4ee0153a641 from=seed src=0 shape=cde06022 vocab=a899e015
-/
@[simp, mfld_simps]
theorem restr_coe (s : Set α) : (e.restr s : α → β) = e :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.a222104f9412 from=seed src=0 shape=208cf57f vocab=f903cd7b
-/
@[simp, mfld_simps]
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β → α) = e.symm :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.1ec8fce37b52 from=seed src=0 shape=7cf3d7c5 vocab=01498b1e
-/
@[simp, mfld_simps]
theorem restr_source (s : Set α) : (e.restr s).source = e.source ∩ s :=
  rfl

/--
@isnad1 id=le.0h4v.s4.164ad1a47d28 from=seed src=0 shape=14295a6c vocab=b8e93ece
-/
theorem source_restr_subset_source (s : Set α) : (e.restr s).source ⊆ e.source := inter_subset_left

/--
@isnad1 id=eq.0h4v.s5.a695f3182993 from=seed src=0 shape=b48aa2e9 vocab=d45e8c50
-/
@[simp, mfld_simps]
theorem restr_target (s : Set α) : (e.restr s).target = e.target ∩ e.symm ⁻¹' s :=
  rfl

/--
@isnad1 id=eq.1h4v.s5.2412f44c2d3d from=seed src=0 shape=04d66267 vocab=b8e93ece
-/
theorem restr_eq_of_source_subset {e : PartialEquiv α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])

/--
@isnad1 id=eq.0h3v.s4.509802ba943c from=seed src=0 shape=9267e1f3 vocab=75c845af
-/
@[simp, mfld_simps]
theorem restr_univ {e : PartialEquiv α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

/-- The identity partial equiv -/
protected def refl (α : Type*) : PartialEquiv α α :=
  (Equiv.refl α).toPartialEquiv

/--
@isnad1 id=eq.0h1v.s3.ceac1558dcc9 from=seed src=0 shape=166e7269 vocab=d0b5b29d
-/
@[simp, mfld_simps]
theorem refl_source : (PartialEquiv.refl α).source = univ :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.3c7b55531074 from=seed src=0 shape=166e7269 vocab=c0001363
-/
@[simp, mfld_simps]
theorem refl_target : (PartialEquiv.refl α).target = univ :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.0f681193ace9 from=seed src=0 shape=5242f510 vocab=68c7e8bf
-/
@[simp, mfld_simps]
theorem refl_coe : (PartialEquiv.refl α : α → α) = id :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.ef08b810e2c3 from=seed src=0 shape=6a4c69a9 vocab=7007d65f
-/
@[simp, mfld_simps]
theorem refl_symm : (PartialEquiv.refl α).symm = PartialEquiv.refl α :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.40c63066b500 from=seed src=0 shape=40229612 vocab=d824697a
-/
@[mfld_simps]
theorem refl_restr_source (s : Set α) : ((PartialEquiv.refl α).restr s).source = s := by simp

/--
@isnad1 id=eq.0h2v.s4.15df83ca5661 from=seed src=0 shape=40229612 vocab=c6f7d5e1
-/
@[mfld_simps]
theorem refl_restr_target (s : Set α) : ((PartialEquiv.refl α).restr s).target = s := by simp

/-- The identity partial equivalence on a set `s` -/
def ofSet (s : Set α) : PartialEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

/--
@isnad1 id=eq.0h2v.s3.cffb9a02fadf from=seed src=0 shape=b2114021 vocab=6bc29d66
-/
@[simp, mfld_simps]
theorem ofSet_source (s : Set α) : (PartialEquiv.ofSet s).source = s :=
  rfl

/--
@isnad1 id=eq.0h2v.s3.352331fdc738 from=seed src=0 shape=b2114021 vocab=a3449382
-/
@[simp, mfld_simps]
theorem ofSet_target (s : Set α) : (PartialEquiv.ofSet s).target = s :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.f5e930336460 from=seed src=0 shape=34513f40 vocab=a753779d
-/
@[simp, mfld_simps]
theorem ofSet_coe (s : Set α) : (PartialEquiv.ofSet s : α → α) = id :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.2b4c16efa560 from=seed src=0 shape=546fbedb vocab=882162de
-/
@[simp, mfld_simps]
theorem ofSet_symm (s : Set α) : (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet s :=
  rfl

/-- `Function.const` as a `PartialEquiv`.
It consists of two constant maps in opposite directions. -/
@[simps]
def single (a : α) (b : β) : PartialEquiv α β where
  toFun := Function.const α b
  invFun := Function.const β a
  source := {a}
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := rfl
  left_inv' a' ha' := by rw [eq_of_mem_singleton ha', const_apply]
  right_inv' b' hb' := by rw [eq_of_mem_singleton hb', const_apply]

/-- Composing two partial equivs if the target of the first coincides with the source of the
second. -/
@[simps]
protected def trans' (e' : PartialEquiv β γ) (h : e.target = e'.source) : PartialEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]

/-- Composing two partial equivs, by restricting to the maximal domain where their composition
is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ f` for this.
-/
@[trans]
protected def trans : PartialEquiv α γ :=
  PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)

/--
@isnad1 id=eq.0h5v.s5.853ca058205f from=seed src=0 shape=2dc8a004 vocab=ad8a5ed9
-/
@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.93b25ca43e5f from=seed src=0 shape=cfd834e1 vocab=1c5f9631
-/
@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.5e734436692e from=seed src=0 shape=5384e6d7 vocab=1846092f
-/
theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.35c7ab90f233 from=seed src=0 shape=05050ef9 vocab=c2f72ee8
-/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

/--
@isnad1 id=eq.0h5v.s5.c5e0cc8bb83d from=seed src=0 shape=0e6ae732 vocab=031a6523
-/
@[simp, mfld_simps]
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.6fb079b5a9f2 from=seed src=0 shape=265fc79b vocab=af948133
-/
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) := by
  mfld_set_tac

/--
@isnad1 id=eq.0h5v.s5.eda76ca17835 from=seed src=0 shape=4d8c1606 vocab=b00622c3
-/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) := by
  rw [e.trans_source', e.symm_image_target_inter_eq]

/--
@isnad1 id=eq.0h5v.s5.5b86fab5d12c from=seed src=0 shape=1f97ec63 vocab=c1d4ea3b
-/
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  (e.symm.restr e'.source).symm.image_source_eq_target

/--
@isnad1 id=eq.0h5v.s5.17428e0bbf93 from=seed src=0 shape=f8336357 vocab=4887649f
-/
@[simp, mfld_simps]
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.c231ae62d661 from=seed src=0 shape=e18fded5 vocab=fd796f07
-/
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm

/--
@isnad1 id=eq.0h5v.s5.cddc3d608958 from=seed src=0 shape=43517708 vocab=c1d4ea3b
-/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm

/--
@isnad1 id=eq.0h5v.s5.430f0985b655 from=seed src=0 shape=cce3537a vocab=b00622c3
-/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm

/--
@isnad1 id=eq.0h7v.s5.241a2b57e7f4 from=seed src=0 shape=1b6cb8ea vocab=540b532f
-/
theorem trans_assoc (e'' : PartialEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

/--
@isnad1 id=eq.0h3v.s4.80da7924e413 from=seed src=0 shape=0b17db3e vocab=83e1d8ac
-/
@[simp, mfld_simps]
theorem trans_refl : e.trans (PartialEquiv.refl β) = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

/--
@isnad1 id=eq.0h3v.s4.b1cecc80d779 from=seed src=0 shape=a5aaf17e vocab=83e1d8ac
-/
@[simp, mfld_simps]
theorem refl_trans : (PartialEquiv.refl α).trans e = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source, preimage_id])

/--
@isnad1 id=eq.0h4v.s5.7cfb8b7a1b6e from=seed src=0 shape=4ffef755 vocab=86032ac2
-/
theorem trans_ofSet (s : Set β) : e.trans (ofSet s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl

/--
@isnad1 id=eq.0h4v.s5.7a263a47042d from=seed src=0 shape=810d0c7b vocab=91312842
-/
theorem trans_refl_restr (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

/--
@isnad1 id=eq.0h4v.s5.5c8e6695e182 from=seed src=0 shape=10d99d4a vocab=fb5998ea
-/
theorem trans_refl_restr' (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e.source ∩ e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) <| by
    simp only [trans_source, restr_source, refl_source, univ_inter]
    rw [← inter_assoc, inter_self]

/--
@isnad1 id=eq.0h6v.s5.0ada70d9c9b6 from=seed src=0 shape=18f260bd vocab=c13feb19
-/
theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) <| by
    simp [trans_source, inter_comm, inter_assoc]

/-- A lemma commonly useful when `e` and `e'` are charts of a manifold.
@isnad1 id=mem.2h6v.s5.7afe451de0d1 from=seed src=0 shape=3489b3d0 vocab=284a722f
-/
theorem mem_symm_trans_source {e' : PartialEquiv α γ} {x : α} (he : x ∈ e.source)
    (he' : x ∈ e'.source) : e x ∈ (e.symm.trans e').source :=
  ⟨e.mapsTo he, by rwa [mem_preimage, PartialEquiv.symm_symm, e.left_inv he]⟩

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same partial equiv. -/
def EqOnSource (e e' : PartialEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'

/-- `EqOnSource` is an equivalence relation. This instance provides the `≈` notation between two
`PartialEquiv`s. -/
instance eqOnSourceSetoid : Setoid (PartialEquiv α β) where
  r := EqOnSource
  iseqv := by constructor <;> grind [EqOnSource, EqOn]

/--
@isnad1 id=equiv.0h3v.s4.1f028b1e91b6 from=seed src=0 shape=a7c11bd3 vocab=0668552f
-/
theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _

/-- Two equivalent partial equivs have the same source.
@isnad1 id=eq.0h5v.s5.129f0d39b871 from=seed src=0 shape=1824f929 vocab=6876b75a
-/
theorem EqOnSource.source_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1

/-- Two equivalent partial equivs coincide on the source.
@isnad1 id=eqon.0h5v.s5.6801f6904af3 from=seed src=0 shape=c5cbb061 vocab=7e1953ed
-/
theorem EqOnSource.eqOn {e e' : PartialEquiv α β} (h : e ≈ e') : e.source.EqOn e e' :=
  h.2

/-- Two equivalent partial equivs have the same target.
@isnad1 id=eq.0h5v.s5.0facda558f77 from=seed src=0 shape=ab380cc8 vocab=f5d8470b
-/
theorem EqOnSource.target_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.target = e'.target := by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]

/-- If two partial equivs are equivalent, so are their inverses.
@isnad1 id=equiv.0h5v.s5.4c0da6e6dbc5 from=seed src=0 shape=ff209cbc vocab=56f02b3e
-/
theorem EqOnSource.symm' {e e' : PartialEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
  refine ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_source, target_eq h, source_eq h, e'.mapsTo_symm]
  exact e'.rightInvOn.congr_right e'.mapsTo_symm (source_eq h ▸ h.eqOn.symm)

/-- Two equivalent partial equivs have coinciding inverses on the target.
@isnad1 id=eqon.0h5v.s5.9dd8c23e55e7 from=seed src=0 shape=fe8cf4fb vocab=e2609cd1
-/
theorem EqOnSource.symm_eqOn {e e' : PartialEquiv α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  eqOn h.symm'

/-- Composition of partial equivs respects equivalence.
@isnad1 id=equiv.0h9v.s6.f4a9392a24de from=seed src=0 shape=48d4f042 vocab=865490f8
-/
theorem EqOnSource.trans' {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' := by
  constructor
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    exact (he.symm'.eqOn.mono inter_subset_left).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [Function.comp_apply, PartialEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]

/-- Restriction of partial equivs respects equivalence.
@isnad1 id=equiv.0h6v.s5.95c0bf121c7f from=seed src=0 shape=3532bb1f vocab=b94c1a49
-/
theorem EqOnSource.restr {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s := by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1

/-- Preimages are respected by equivalence.
@isnad1 id=eq.0h6v.s6.f725657bf7b1 from=seed src=0 shape=0abb6778 vocab=b4103828
-/
theorem EqOnSource.source_inter_preimage_eq {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set β) :
    e.source ∩ e ⁻¹' s = e'.source ∩ e' ⁻¹' s := by rw [he.eqOn.inter_preimage_eq, source_eq he]

/-- Composition of a partial equivalence and its inverse is equivalent to
the restriction of the identity to the source.
@isnad1 id=equiv.0h3v.s5.f69b82f6cd6c from=seed src=0 shape=53ac76af vocab=b57d1761
-/
theorem self_trans_symm : e.trans e.symm ≈ ofSet e.source := by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine ⟨by rw [A, ofSet_source], fun x hx => ?_⟩
  rw [A] at hx
  simp only [hx, mfld_simps]

/-- Composition of the inverse of a partial equivalence and this partial equivalence is equivalent
to the restriction of the identity to the target.
@isnad1 id=equiv.0h3v.s5.1c6cf415933e from=seed src=0 shape=84a27f3f vocab=6bf2cd3a
-/
theorem symm_trans_self : e.symm.trans e ≈ ofSet e.target :=
  self_trans_symm e.symm

/-- Two equivalent partial equivs are equal when the source and target are `univ`. -/
theorem eq_of_eqOnSource_univ (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' := by
  refine PartialEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source, t]
    exact mem_univ _

section Prod

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The product of two partial equivalences, as a partial equivalence on the product. -/
def prod (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : PartialEquiv (α × γ) (β × δ) where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp   := by simp_all
  right_inv' p hp  := by simp_all

/--
@isnad1 id=eq.0h6v.s5.ed4b47aa0806 from=seed src=0 shape=40552e5f vocab=255b4c18
-/
@[simp, mfld_simps]
theorem prod_source (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').source = e.source ×ˢ e'.source :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.5175341a634e from=seed src=0 shape=e5a182ec vocab=6d7270ba
-/
@[simp, mfld_simps]
theorem prod_target (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').target = e.target ×ˢ e'.target :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.924e6c9bb0b8 from=seed src=0 shape=095a8fd2 vocab=1edff71b
-/
@[simp, mfld_simps]
theorem prod_coe (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e' : α × γ → β × δ) = fun p => (e p.1, e' p.2) :=
  rfl

/--
@isnad1 id=eq.0h6v.s6.8af4e1325ab1 from=seed src=0 shape=700705dc vocab=461f6ae2
-/
theorem prod_coe_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    ((e.prod e').symm : β × δ → α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.cb79b5a7f2f7 from=seed src=0 shape=cc6f3e0c vocab=be504e0c
-/
@[simp, mfld_simps]
theorem prod_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm := by
  ext x <;> simp [prod_coe_symm]

/--
@isnad1 id=eq.0h2v.s4.8c81785b1f1b from=seed src=0 shape=126382c0 vocab=bd02d5e6
-/
@[simp, mfld_simps]
theorem refl_prod_refl :
    (PartialEquiv.refl α).prod (PartialEquiv.refl β) = PartialEquiv.refl (α × β) := by
  ext ⟨x, y⟩ <;> simp

/--
@isnad1 id=eq.0h10v.s6.2790d2212fbb from=seed src=0 shape=0ea08125 vocab=22548bf2
-/
@[simp, mfld_simps]
theorem prod_trans {η : Type*} {ε : Type*} (e : PartialEquiv α β) (f : PartialEquiv β γ)
    (e' : PartialEquiv δ η) (f' : PartialEquiv η ε) :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') := by
  ext ⟨x, y⟩ <;> simp; tauto

end Prod

/-- Combine two `PartialEquiv`s using `Set.piecewise`. The source of the new `PartialEquiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.isImage s t` and
`e'.isImage s t`. -/
@[simps -fullyApplied]
def piecewise (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    PartialEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm

/--
@isnad1 id=eq.2h6v.s6.88737f9fd71f from=seed src=0 shape=10cd7c1f vocab=bd1c0cab
-/
theorem symm_piecewise (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl

/-- Combine two `PartialEquiv`s with disjoint sources and disjoint targets. We reuse
`PartialEquiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps! -fullyApplied]
def disjointUnion (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] : PartialEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source ∪ e'.source) (ite_left _ _) (e.target ∪ e'.target) (ite_left _ _)

/--
@isnad1 id=eq.2h4v.s7.806341c41a70 from=seed src=0 shape=dca6b1e7 vocab=71440787
-/
theorem disjointUnion_eq_piecewise (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq ..

section Pi

variable {ι : Type*} {αi βi γi : ι → Type*}

/-- The product of a family of partial equivalences, as a partial equivalence on the pi type. -/
@[simps (attr := mfld_simps) -fullyApplied apply source target]
protected def pi (ei : ∀ i, PartialEquiv (αi i) (βi i)) : PartialEquiv (∀ i, αi i) (∀ i, βi i) where
  toFun := Pi.map fun i ↦ ei i
  invFun := Pi.map fun i ↦ (ei i).symm
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' _ hf := funext fun i => (ei i).right_inv (hf i trivial)

/--
@isnad1 id=eq.0h4v.s6.f6d3dbd641cc from=seed src=0 shape=cb705cc3 vocab=2b8adfcb
-/
@[simp, mfld_simps]
theorem pi_symm (ei : ∀ i, PartialEquiv (αi i) (βi i)) :
    (PartialEquiv.pi ei).symm = .pi fun i ↦ (ei i).symm :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.5b9dc53657c5 from=seed src=0 shape=12ea9001 vocab=a542e6b6
-/
theorem pi_symm_apply (ei : ∀ i, PartialEquiv (αi i) (βi i)) :
    ⇑(PartialEquiv.pi ei).symm = fun f i ↦ (ei i).symm (f i) :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.8f6141667ca2 from=seed src=0 shape=5dd7f225 vocab=5265928e
-/
@[simp, mfld_simps]
theorem pi_refl : (PartialEquiv.pi fun i ↦ PartialEquiv.refl (αi i)) = .refl (∀ i, αi i) := by
  ext <;> simp

/--
@isnad1 id=eq.0h6v.s6.31e5368909bd from=seed src=0 shape=c09640c6 vocab=49573fcf
-/
@[simp, mfld_simps]
theorem pi_trans (ei : ∀ i, PartialEquiv (αi i) (βi i)) (ei' : ∀ i, PartialEquiv (βi i) (γi i)) :
    (PartialEquiv.pi ei).trans (PartialEquiv.pi ei') = .pi fun i ↦ (ei i).trans (ei' i) := by
  ext <;> simp [forall_and]

end Pi

/--
@isnad1 id=surjecti.1h3v.s4.d43ab8bcefbc from=seed src=0 shape=5cd945bd vocab=7df9347c
-/
lemma surjective_of_target_eq_univ (h : e.target = univ) :
    Surjective e :=
  surjOn_univ.mp <| e.surjOn.mono (by simp) (by simp [h])

/--
@isnad1 id=injectiv.1h3v.s4.7b87368fc0b4 from=seed src=0 shape=b5840475 vocab=ac7df84a
-/
lemma injective_of_source_eq_univ (h : e.source = univ) : Injective e := by simpa [h] using e.injOn

/--
@isnad1 id=injectiv.1h3v.s4.fdd54718056b from=seed src=0 shape=35ceac84 vocab=071fe177
-/
lemma injective_symm_of_target_eq_univ (h : e.target = univ) :
    Injective e.symm :=
  e.symm.injective_of_source_eq_univ h

/--
@isnad1 id=surjecti.1h3v.s4.c54e9c4758d4 from=seed src=0 shape=1468a062 vocab=754df866
-/
lemma surjective_symm_of_source_eq_univ (h : e.source = univ) :
    Surjective e.symm :=
  e.symm.surjective_of_target_eq_univ h

end PartialEquiv

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : Set α` and `t : Set β` provides a partial equivalence
between `α` and `β`. -/
@[simps -fullyApplied]
noncomputable def BijOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : PartialEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

/-- A map injective on a subset of its domain provides a partial equivalence. -/
@[simp, mfld_simps]
noncomputable def InjOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) :
    PartialEquiv α β :=
  hf.bijOn_image.toPartialEquiv f s (f '' s)

end Set

namespace Equiv

/- `Equiv`s give rise to `PartialEquiv`s. We set up simp lemmas to reduce most properties of the
`PartialEquiv` to that of the `Equiv`. -/
variable (e : α ≃ β) (e' : β ≃ γ)

/--
@isnad1 id=eq.0h1v.s3.d3d8429fd69d from=seed src=0 shape=6a4c69a9 vocab=30e0445d
-/
@[simp, mfld_simps]
theorem refl_toPartialEquiv : (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.e02468f3d88d from=seed src=0 shape=8c75430e vocab=a661097a
-/
@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.dd45948591c0 from=seed src=0 shape=1a025900 vocab=e2e44441
-/
@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [PartialEquiv.trans_source, Equiv.toPartialEquiv])

/-- Precompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
def transPartialEquiv (e : α ≃ β) (f' : PartialEquiv β γ) : PartialEquiv α γ :=
  (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)

/--
@isnad1 id=eq.0h5v.s5.cae427faaded from=seed src=0 shape=f8bb057d vocab=2f251883
-/
theorem transPartialEquiv_eq_trans (e : α ≃ β) (f' : PartialEquiv β γ) :
    e.transPartialEquiv f' = e.toPartialEquiv.trans f' :=
  PartialEquiv.copy_eq ..

/--
@isnad1 id=eq.0h7v.s5.d9745d645b3a from=seed src=0 shape=5bd45eb2 vocab=65e6cef6
-/
@[simp, mfld_simps]
theorem transPartialEquiv_trans (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : PartialEquiv γ δ) :
    (e.transPartialEquiv f').trans f'' = e.transPartialEquiv (f'.trans f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc]

/--
@isnad1 id=eq.0h7v.s5.7a5dce296532 from=seed src=0 shape=98b795a8 vocab=3286900a
-/
@[simp, mfld_simps]
theorem trans_transPartialEquiv (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ) :
    (e.trans e').transPartialEquiv f'' = e.transPartialEquiv (e'.transPartialEquiv f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc, trans_toPartialEquiv]

/--
@isnad1 id=eq.0h5v.s5.bb72a76041e5 from=seed src=0 shape=52f928d9 vocab=11c663f1
-/
@[simp]
lemma coe_transPartialEquiv {f : α ≃ β} {g : PartialEquiv β γ} : f.transPartialEquiv g = g ∘ f :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.e60e54e7456b from=seed src=0 shape=781b5c05 vocab=9b124d0b
-/
@[simp]
lemma coe_transPartialEquiv_symm {f : α ≃ β} {g : PartialEquiv β γ} :
    (f.transPartialEquiv g).symm = f.symm ∘ g.symm :=
  rfl

end Equiv

namespace PartialEquiv

/-- Postcompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
def transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) : PartialEquiv α γ :=
  (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)

/--
@isnad1 id=eq.0h5v.s5.0bd831945ed6 from=seed src=0 shape=c34c48ff vocab=ef1e2930
-/
theorem transEquiv_eq_trans (e : PartialEquiv α β) (e' : β ≃ γ) :
    e.transEquiv e' = e.trans e'.toPartialEquiv :=
  copy_eq ..

/--
@isnad1 id=eq.0h7v.s5.790682b62a22 from=seed src=0 shape=ed52669a vocab=0f768464
-/
@[simp, mfld_simps]
theorem transEquiv_transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ) :
    (e.transEquiv f').transEquiv f'' = e.transEquiv (f'.trans f'') := by
  simp only [transEquiv_eq_trans, trans_assoc, Equiv.trans_toPartialEquiv]

/--
@isnad1 id=eq.0h7v.s5.de2db231f08f from=seed src=0 shape=2b0e3c89 vocab=1fa50f02
-/
@[simp, mfld_simps]
theorem trans_transEquiv (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃ δ) :
    (e.trans e').transEquiv f'' = e.trans (e'.transEquiv f'') := by
  simp only [transEquiv_eq_trans, trans_assoc]

/--
@isnad1 id=eq.0h5v.s5.1890c9f0f9ac from=seed src=0 shape=0eed1301 vocab=88c4a934
-/
@[simp] lemma coe_transEquiv {f : PartialEquiv α β} {g : β ≃ γ} : f.transEquiv g = g ∘ f := rfl

/--
@isnad1 id=eq.0h5v.s5.b560f05381b4 from=seed src=0 shape=26620740 vocab=f0423b9a
-/
@[simp]
lemma coe_transEquiv_symm {f : PartialEquiv α β} {g : β ≃ γ} :
    (f.transEquiv g).symm = f.symm ∘ g.symm :=
  rfl

end PartialEquiv
