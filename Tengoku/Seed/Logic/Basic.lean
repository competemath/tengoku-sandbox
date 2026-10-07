/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Tengoku.Seed.Lean.Meta.Simp
public import Tengoku.Seed.Std.Logic
public import Tengoku.Seed.Std.Util.LibraryNote
public import Tengoku.Seed.Tactic.Attr.Register

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace `Decidable`.
Classical versions are in the namespace `Classical`.
-/

@[expose] public section

open Function

section Miscellany

section CommSimproc

open Lean Meta Simp

theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by rw [@eq_comm _ a b]
/--
@isnad1 id=eq.0h2v.s3.3ba7bfbf8651 from=seed src=0 shape=1b9a7583 vocab=e3b0c442
-/
theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by rw [@iff_comm a b]

/-- On a goal of the form of `x = y`, also try to simplify `y = x`.

If simplifying `y = x` gives `y' = x'` then this simproc returns `x' = y'` (so that the use of
commutativity is transparent), otherwise it returns the result of simplifying `y = x` unmodified.
-/
simproc_decl eqComm (_ = _) := fun e => do
  let_expr Eq _ x y := e | return .continue
  let symmExpr ← mkEq y x
  let r ← withoutTheorems #[`eqComm,
    -- These theorems would cause an infinite loop:
    ``eq_comm, ``Bool.not_eq_eq_eq_not, `inv_eq_iff_eq_inv, `eq_inv_mul_iff_mul_eq,
    `eq_mul_inv_iff_mul_eq, `neg_eq_iff_eq_neg, `Function.Involutive.eq_iff,
    `vadd_eq_iff_eq_neg_vadd, `Equiv.eq_symm_apply,
    -- These theorems aren't commute-resistant (they turn an equality into a non-equality in a
    -- non-commutative way.)
    ``beq_iff_eq, ``funext_iff, ``eq_iff_iff, `Prod.swap_eq_iff_eq_swap, ``left_eq_dite_iff,
    ``right_eq_dite_iff] do
    withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting equality: {e}") <| simp symmExpr
  -- If no actual progress happened (modulo commutativity), return early.
  match_expr r.expr with
  | Eq _ y' x' =>
    if (y' == y && x' == x) || (y' == x && x' == y) then do
      return .continue none
  | _ => pure ()
  let symmR ← Result.mkEqTrans { expr := symmExpr, proof? := ← mkAppM ``eq_comm_eq #[x, y] } r
  -- If we started with `x = y`, and the result of simplifying `y = x` was `y' = x'`, then we want
  -- to end up with `x' = y'`.
  match_expr r.expr with
  | Eq _ y' x' =>
    return .visit (← symmR.mkEqTrans
      { expr := ← mkEq x' y', proof? := ← mkAppM ``eq_comm_eq #[y', x'] })
  | _ => return .done symmR

/-- On a goal of the form of `x ↔ y`, also try to simplify `y ↔ x`.

If simplifying `y ↔ x` gives `y' ↔ x'` then this simproc returns `x' ↔ y'` (so that the use of
commutativity is transparent), otherwise it returns the result of simplifying `y ↔ x` unmodified.
-/
simproc_decl iffComm (_ ↔ _) := fun e => do
  let_expr Iff x y := e | return .continue
  let symmExpr := .app (.app (.const ``Iff []) y) x
  let r ← withoutTheorems #[`iffComm,
      -- These theorems would cause an infinite loop:
      ``Iff.comm,
      -- These theorems aren't commute-resistant (they turn an iff into a non-iff in a
      -- non-commutative way).
      ``and_congr_left_iff, ``and_congr_right_iff,  ``iff_def, ``iff_def',
      ``iff_iff_implies_and_implies, ``Bool.coe_iff_coe] do
    withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting iff: {e}") <| simp symmExpr
  -- If no actual progress happened (modulo commutativity), return early.
  if r.expr == symmExpr || r.expr == e then return .continue
  let symmR ← Result.mkEqTrans { expr := symmExpr, proof? := ← mkAppM ``iff_comm_eq #[x, y] } r
  -- If we started with `x ↔ y`, and the result of simplifying `y ↔ x` was `y' ↔ x'`, then we want
  -- to end up with `x' ↔ y'`.
  match_expr r.expr with
  | Iff y' x' =>
    return .visit (← symmR.mkEqTrans
      { expr := .app (.app (.const ``Iff []) x') y', proof? := ← mkAppM ``iff_comm_eq #[y', x'] })
  | _ => return .done symmR

end CommSimproc

-- attribute [refl] HEq.refl -- FIXME This is still rejected after https://github.com/leanprover-community/mathlib4/pull/857

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
abbrev hidden {α : Sort*} {a : α} := a

variable {α : Sort*}

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b ↦ isTrue (Subsingleton.elim a b)

instance [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ ↦ by cases Subsingleton.elim x y; rfl⟩

/--
@isnad1 id=iff.0h2v.s4.1296a7a64ed7 from=seed src=0 shape=95119c25 vocab=831d023c
-/
theorem Subtype.subsingleton_iff {p : α → Prop} :
    Subsingleton (Subtype p) ↔ ∀ a b, p a → p b → a = b :=
  ⟨fun _ a b ha hb ↦ congr_arg val (Subsingleton.elim ⟨a, ha⟩ ⟨b, hb⟩),
   fun h ↦ ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext (h a b ha hb)⟩⟩

/--
@isnad1 id=eq.2h7v.s5.30d3a72f9827 from=seed src=0 shape=f1d1ff80 vocab=c80cf600
-/
theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y := by
  cases h₂; cases h₁; rfl

/--
@isnad1 id=heq.1h5v.s5.e8e3a71388c6 from=seed src=0 shape=182933eb vocab=c80cf600
-/
theorem congr_arg_heq {β : α → Sort*} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
  | _, _, rfl => HEq.rfl

/--
@isnad1 id=heq.3h8v.s6.3910f5885ddf from=seed src=0 shape=44e5cf30 vocab=c80cf600
-/
theorem dcongr_heq.{u, v}
    {α₁ α₂ : Sort u}
    {β₁ : α₁ → Sort v} {β₂ : α₂ → Sort v}
    {f₁ : ∀ a, β₁ a} {f₂ : ∀ a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hargs : a₁ ≍ a₂)
    (ht : ∀ t₁ t₂, t₁ ≍ t₂ → β₁ t₁ = β₂ t₂)
    (hf : α₁ = α₂ → β₁ ≍ β₂ → f₁ ≍ f₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl

@[simp] theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h ↦ by rw [← h], fun h a ↦ by rw [h]⟩

@[simp] theorem eq_iff_eq_cancel_right {a b : α} : (∀ {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h ↦ by rw [h], fun h a ↦ by rw [h]⟩

/--
@isnad1 id=iff.1h4v.s4.fca8302984a6 from=seed src=0 shape=1bce3236 vocab=e3b0c442
-/
lemma ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
  and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `ZMod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.Prime` into an instance implicit assumption.

On the other hand, making `Nat.Prime` a class would require a major refactoring of the library,
and it is questionable whether making `Nat.Prime` a class is desirable at all.
The compromise is to add the assumption `[Fact p.Prime]` to `ZMod.instField`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first-order logic. -/
class Fact (p : Prop) : Prop where
  /-- `Fact.out` contains the unwrapped witness for the fact represented by the instance of
  `Fact p`. -/
  out : p

library_note «fact non-instances» /--
In most cases, we should not have global instances of `Fact`; typeclass search is not an
advanced proof search engine, and adding any such instance has the potential to cause
slowdowns everywhere. We instead declare them as lemmata and make them local instances as required.
-/

/--
@isnad1 id=var.1h1v.s2.1e40bec65519 from=seed src=0 shape=e458fbb1 vocab=210c2e38
-/
theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
/--
@isnad1 id=iff.0h1v.s2.cb76fb18a965 from=seed src=0 shape=d2421d2d vocab=210c2e38
-/
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

instance {p : Prop} [Decidable p] : Decidable (Fact p) :=
  decidable_of_iff _ fact_iff.symm

/-- Swaps two pairs of arguments to a function. -/
abbrev Function.swap₂ {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort*} (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
    (i₂ j₂ i₁ j₁) : φ i₁ j₁ i₂ j₂ := f i₁ j₁ i₂ j₂

end Miscellany

/-!
### Declarations about propositional connectives
-/

section Propositional

/-! ### Declarations about `implies` -/

/--
@isnad1 id=iff.2h4v.s4.a997ecf90ad6 from=seed src=0 shape=a557db04 vocab=e3b0c442
-/
alias Iff.imp := imp_congr

/-- Provide modus tollens (`mt`) as dot notation for implications.
@isnad1 id=not.1h3v.s3.e48e32a8e478 from=seed src=0 shape=66e2e31f vocab=e3b0c442
-/
protected theorem Function.mt {a b : Prop} : (a → b) → ¬b → ¬a := mt

/-! ### Declarations about `not` -/

/--
@isnad1 id=or.0h1v.s3.898871b32cb4 from=seed src=0 shape=fd1e5128 vocab=4aa5ae2c
-/
alias dec_em := Decidable.em

set_option linter.unusedDecidableInType false in
/--
@isnad1 id=or.0h1v.s3.c5a6932d7c50 from=seed src=0 shape=7a6d3fd4 vocab=4aa5ae2c
-/
theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).symm

/--
@isnad1 id=or.0h1v.s2.d0ba1dcc8190 from=seed src=0 shape=19066b9d vocab=e3b0c442
-/
alias em := Classical.em

/--
@isnad1 id=or.0h1v.s2.e52ecd19d782 from=seed src=0 shape=d2421d2d vocab=e3b0c442
-/
theorem em' (p : Prop) : ¬p ∨ p := (em p).symm

/--
@isnad1 id=or.0h1v.s2.d0ba1dcc8190 from=seed src=0 shape=19066b9d vocab=e3b0c442
-/
theorem or_not {p : Prop} : p ∨ ¬p := em _

theorem Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable (x = y)] : x = y ∨ x ≠ y :=
  dec_em <| x = y

/--
@isnad1 id=or.0h3v.s4.9133ef741b75 from=seed src=0 shape=89535047 vocab=4aa5ae2c
-/
theorem Decidable.ne_or_eq {α : Sort*} (x y : α) [Decidable (x = y)] : x ≠ y ∨ x = y :=
  dec_em' <| x = y

theorem eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x ≠ y := em <| x = y

/--
@isnad1 id=or.0h3v.s3.58b3f70114c6 from=seed src=0 shape=24b2c9cd vocab=e3b0c442
-/
theorem ne_or_eq {α : Sort*} (x y : α) : x ≠ y ∨ x = y := em' <| x = y

/--
@isnad1 id=var.1h1v.s3.fa73f61d2499 from=seed src=0 shape=36c77bf5 vocab=e3b0c442
-/
theorem by_contradiction {p : Prop} : (¬p → False) → p :=
  open scoped Classical in Decidable.byContradiction

/--
@isnad1 id=var.0h4v.s3.630ed044c8ad from=seed src=0 shape=fc4e2dd6 vocab=e3b0c442
-/
theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  open scoped Classical in if hp : p then hpq hp else hnpq hp

/--
@isnad1 id=var.1h1v.s3.fa73f61d2499 from=seed src=0 shape=36c77bf5 vocab=e3b0c442
-/
alias by_contra := by_contradiction

library_note «decidable namespace» /--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `Decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`Classical.choice` appears in the list.
-/

library_note «decidable arguments» /--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `Decidable` instances to state,
it is preferable not to introduce any `Decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `Decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.

Various types that (almost) never have provable decidability, such as `ℝ`, `Set α` or `Ideal R`,
are given global `DecidableEq` instances, so that no decidable arguments have to be provided.
-/

export Classical (not_not)

variable {a b : Prop}

/--
@isnad1 id=var.1h1v.s2.74c0595ce08a from=seed src=0 shape=5339fdcd vocab=e3b0c442
-/
theorem of_not_not {a : Prop} : ¬¬a → a := by_contra

/--
@isnad1 id=iff.0h3v.s4.cc3ba3f0b3d3 from=seed src=0 shape=697545eb vocab=e3b0c442
-/
theorem not_ne_iff {α : Sort*} {a b : α} : ¬a ≠ b ↔ a = b := not_not

/--
@isnad1 id=var.1h2v.s3.465b862e89cc from=seed src=0 shape=4ffca525 vocab=e3b0c442
-/
theorem of_not_imp : ¬(a → b) → a := open scoped Classical in Decidable.of_not_imp

/--
@isnad1 id=var.1h3v.s4.377fdf67c0bb from=seed src=0 shape=44075c06 vocab=4aa5ae2c
-/
alias Not.decidable_imp_symm := Decidable.not_imp_symm

/--
@isnad1 id=var.1h3v.s3.3a1ebc75370e from=seed src=0 shape=d623961c vocab=e3b0c442
-/
theorem Not.imp_symm : (¬a → b) → ¬b → a := open scoped Classical in Not.decidable_imp_symm

/--
@isnad1 id=iff.0h2v.s3.c3fe6a16be3c from=seed src=0 shape=a33509b1 vocab=e3b0c442
-/
theorem not_imp_comm : ¬a → b ↔ ¬b → a := open scoped Classical in Decidable.not_imp_comm

/--
@isnad1 id=iff.0h1v.s3.61651ebf5ba3 from=seed src=0 shape=7c92a209 vocab=e3b0c442
-/
@[simp] theorem not_imp_self : ¬a → a ↔ a := open scoped Classical in Decidable.not_imp_self

/--
@isnad1 id=iff.0h3v.s4.d47b27dd5b94 from=seed src=0 shape=8309dab1 vocab=e3b0c442
-/
theorem Imp.swap {a b : Sort*} {c : Prop} : a → b → c ↔ b → a → c :=
  ⟨fun h x y ↦ h y x, fun h x y ↦ h y x⟩

/--
@isnad1 id=iff.1h2v.s3.4e0e7f4ac997 from=seed src=0 shape=f9674ab4 vocab=e3b0c442
-/
alias Iff.not := not_congr

/--
@isnad1 id=iff.1h2v.s3.a840355f651b from=seed src=0 shape=edca9b3e vocab=e3b0c442
-/
theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b := h.not.trans not_not

/--
@isnad1 id=iff.1h2v.s3.6bbc229e9efd from=seed src=0 shape=0417e30b vocab=e3b0c442
-/
theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b := not_not.symm.trans h.not

/--
@isnad1 id=iff.1h6v.s4.d6aa35a089e9 from=seed src=0 shape=399042fa vocab=e3b0c442
-/
protected lemma Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) :=
  Iff.not

/--
@isnad1 id=iff.1h6v.s4.35493d73ca94 from=seed src=0 shape=31d93f2a vocab=e3b0c442
-/
lemma Iff.ne_left {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c ≠ d) → (a ≠ b ↔ c = d) :=
  Iff.not_left

/--
@isnad1 id=iff.1h6v.s4.b65bdc367bab from=seed src=0 shape=31d93f2a vocab=e3b0c442
-/
lemma Iff.ne_right {α β : Sort*} {a b : α} {c d : β} : (a ≠ b ↔ c = d) → (a = b ↔ c ≠ d) :=
  Iff.not_right

/-! ### Declarations about `Xor` -/

/-- `Xor a b` is the exclusive-or of propositions. -/
def Xor (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)

@[deprecated (since := "2026-04-27")] alias Xor' := Xor

/--
@isnad1 id=iff.0h2v.s4.0cffa63b05b8 from=seed src=0 shape=a0a57f7b vocab=8ad60361
-/
@[grind =] theorem xor_def {a b : Prop} : Xor a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a) := Iff.rfl

instance [Decidable a] [Decidable b] : Decidable (Xor a b) := inferInstanceAs (Decidable (Or ..))

/--
@isnad1 id=eq.0h0v.s2.bb84c29a4b61 from=seed src=0 shape=d0bf0ef9 vocab=8ad60361
-/
@[simp] theorem xor_true : Xor True = Not := by grind

/--
@isnad1 id=eq.0h0v.s3.4737a224e97c from=seed src=0 shape=e28f9909 vocab=73c91e15
-/
@[simp] theorem xor_false : Xor False = id := by grind

/--
@isnad1 id=eq.0h2v.s3.5c2f1fafbeaa from=seed src=0 shape=1b9a7583 vocab=8ad60361
-/
theorem xor_comm (a b : Prop) : Xor a b = Xor b a := by grind

instance : Std.Commutative Xor := ⟨xor_comm⟩

/--
@isnad1 id=eq.0h1v.s3.caaa4a275011 from=seed src=0 shape=68e1ccc3 vocab=8ad60361
-/
@[simp] theorem xor_self (a : Prop) : Xor a a = False := by grind

/--
@isnad1 id=iff.0h2v.s3.4fcd49cd7be7 from=seed src=0 shape=57dfb290 vocab=8ad60361
-/
@[simp] theorem xor_not_left : Xor (¬a) b ↔ (a ↔ b) := by grind

/--
@isnad1 id=iff.0h2v.s3.9de55440d585 from=seed src=0 shape=9ba12b24 vocab=8ad60361
-/
@[simp] theorem xor_not_right : Xor a (¬b) ↔ (a ↔ b) := by grind

/--
@isnad1 id=iff.0h2v.s3.9fc8b2d6a98a from=seed src=0 shape=8f59e671 vocab=8ad60361
-/
theorem xor_not_not : Xor (¬a) (¬b) ↔ Xor a b := by grind

/--
@isnad1 id=or.1h2v.s3.fe637b65e7c4 from=seed src=0 shape=1aacaac3 vocab=8ad60361
-/
protected theorem Xor.or (h : Xor a b) : a ∨ b := by grind

/--
@isnad1 id=or.1h2v.s3.fe637b65e7c4 from=seed src=0 shape=1aacaac3 vocab=8ad60361
-/
@[deprecated (since := "2026-04-27")]
protected alias Xor'.or := Xor.or

/-! ### Declarations about `and` -/

/--
@isnad1 id=iff.2h4v.s4.a0c6bd1cafc4 from=seed src=0 shape=773f6721 vocab=e3b0c442
-/
alias Iff.and := and_congr
/--
@isnad1 id=and.1h3v.s4.a7e998f51b5a from=seed src=0 shape=12875d43 vocab=e3b0c442
-/
alias ⟨And.rotate, _⟩ := and_rotate

/--
@isnad1 id=iff.0h4v.s4.d523f7e6ffcb from=seed src=0 shape=09fbfb7c vocab=e3b0c442
-/
theorem and_symm_right {α : Sort*} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
/--
@isnad1 id=iff.0h4v.s4.67fc91e4cf83 from=seed src=0 shape=f1a9361e vocab=e3b0c442
-/
theorem and_symm_left {α : Sort*} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]

/-! ### Declarations about `or` -/

/--
@isnad1 id=iff.2h4v.s4.70f616114582 from=seed src=0 shape=773f6721 vocab=e3b0c442
-/
alias Iff.or := or_congr
/--
@isnad1 id=or.1h3v.s4.748da142f701 from=seed src=0 shape=12875d43 vocab=e3b0c442
-/
alias ⟨Or.rotate, _⟩ := or_rotate

/--
@isnad1 id=var.1h7v.s4.4522004cd4b9 from=seed src=0 shape=2a6438fb vocab=e3b0c442
-/
theorem Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ ↦ Or.elim h₂ hb hc

/--
@isnad1 id=or.1h9v.s5.fa263e1a11ef from=seed src=0 shape=a01a9751 vocab=e3b0c442
-/
theorem Or.imp3 {d e c f : Prop} (had : a → d) (hbe : b → e) (hcf : c → f) :
    a ∨ b ∨ c → d ∨ e ∨ f :=
  Or.imp had <| Or.imp hbe hcf

export Classical (or_iff_not_imp_left or_iff_not_imp_right)

/--
@isnad1 id=or.0h3v.s3.869649f42eb3 from=seed src=0 shape=efd2d7b8 vocab=e3b0c442
-/
theorem not_or_of_imp : (a → b) → ¬a ∨ b := open scoped Classical in Decidable.not_or_of_imp

-- See Note [decidable namespace]
/--
@isnad1 id=or.0h3v.s3.b697b23dfbe1 from=seed src=0 shape=ecd5e611 vocab=4aa5ae2c
-/
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a → b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr

/--
@isnad1 id=or.0h3v.s3.2d1d86c908fa from=seed src=0 shape=432c8de8 vocab=e3b0c442
-/
theorem or_not_of_imp : (a → b) → b ∨ ¬a := open scoped Classical in Decidable.or_not_of_imp

/--
@isnad1 id=iff.0h2v.s3.be037e5e3a08 from=seed src=0 shape=b1e0d345 vocab=e3b0c442
-/
theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := open scoped Classical in Decidable.imp_iff_not_or

/--
@isnad1 id=iff.0h2v.s3.ab6a67b331bc from=seed src=0 shape=10955f63 vocab=e3b0c442
-/
theorem imp_iff_or_not {b a : Prop} : b → a ↔ a ∨ ¬b :=
  open scoped Classical in Decidable.imp_iff_or_not

/--
@isnad1 id=iff.0h2v.s3.fe92f1b5ce0f from=seed src=0 shape=1f7621e3 vocab=e3b0c442
-/
theorem not_imp_not : ¬a → ¬b ↔ b → a := open scoped Classical in Decidable.not_imp_not

/-- Provide the reverse of modus tollens (`mt`) as dot notation for implications.
@isnad1 id=var.1h3v.s3.c08217841ea1 from=seed src=0 shape=19ef4c49 vocab=e3b0c442
-/
protected theorem Function.mtr : (¬a → ¬b) → b → a := not_imp_not.mp

/--
@isnad1 id=iff.1h3v.s4.acb240fef40a from=seed src=0 shape=a86c5e0f vocab=e3b0c442
-/
theorem or_congr_left' {c a b : Prop} (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c :=
  open scoped Classical in Decidable.or_congr_left' h

/--
@isnad1 id=iff.1h3v.s4.878f216aa08e from=seed src=0 shape=45bf086d vocab=e3b0c442
-/
theorem or_congr_right' {c : Prop} (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c :=
  open scoped Classical in Decidable.or_congr_right' h

/-! ### Declarations about distributivity -/

/-! Declarations about `iff` -/

/--
@isnad1 id=iff.2h4v.s4.2982af24fa2a from=seed src=0 shape=72b0a5cc vocab=e3b0c442
-/
alias Iff.iff := iff_congr

-- @[simp] -- FIXME simp ignores proof rewrites
/--
@isnad1 id=eq.0h2v.s3.28e357acfa99 from=seed src=0 shape=6e6d0dfe vocab=acdd13b1
-/
theorem iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl

/--
@isnad1 id=iff.0h3v.s4.b94ad2f7b30b from=seed src=0 shape=da92956c vocab=e3b0c442
-/
theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  open scoped Classical in Decidable.imp_or

/--
@isnad1 id=iff.0h3v.s4.639317680db3 from=seed src=0 shape=e3285851 vocab=e3b0c442
-/
theorem imp_or' {a : Sort*} {b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  open scoped Classical in Decidable.imp_or'

/--
@isnad1 id=var.0h3v.s3.134fd079286d from=seed src=0 shape=134fd079 vocab=e3b0c442
-/
theorem peirce (a b : Prop) : ((a → b) → a) → a := open scoped Classical in Decidable.peirce _ _

/--
@isnad1 id=iff.0h2v.s3.5a6da654fea3 from=seed src=0 shape=ae58cda2 vocab=e3b0c442
-/
theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) := open scoped Classical in Decidable.not_iff_not

/--
@isnad1 id=iff.0h2v.s3.9ebd45a8d158 from=seed src=0 shape=e0a6905f vocab=e3b0c442
-/
theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) := open scoped Classical in Decidable.not_iff_comm

/--
@isnad1 id=iff.0h2v.s3.7b236002c73a from=seed src=0 shape=26390e14 vocab=e3b0c442
-/
theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := open scoped Classical in Decidable.not_iff

/--
@isnad1 id=iff.0h2v.s3.ebffe25d1b03 from=seed src=0 shape=8798b3ab vocab=e3b0c442
-/
theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) := open scoped Classical in Decidable.iff_not_comm

/--
@isnad1 id=iff.0h2v.s4.e33fdd9d77be from=seed src=0 shape=31c32412 vocab=e3b0c442
-/
theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  open scoped Classical in Decidable.iff_iff_and_or_not_and_not

/--
@isnad1 id=iff.0h2v.s4.85613cac4f28 from=seed src=0 shape=602201e3 vocab=e3b0c442
-/
theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  open scoped Classical in Decidable.iff_iff_not_or_and_or_not

/--
@isnad1 id=iff.0h2v.s3.a80d5bde652e from=seed src=0 shape=93e95b05 vocab=e3b0c442
-/
theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a → b :=
  open scoped Classical in Decidable.not_and_not_right

/-! ### De Morgan's laws -/

/-- One of **de Morgan's laws**: the negation of a conjunction is logically equivalent to the
disjunction of the negations.
@isnad1 id=iff.0h2v.s3.bca8c985ce5d from=seed src=0 shape=3808593d vocab=e3b0c442
-/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := open scoped Classical in Decidable.not_and_iff_not_or_not

/--
@isnad1 id=iff.0h2v.s3.81d8330a23fa from=seed src=0 shape=158a0239 vocab=e3b0c442
-/
theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  open scoped Classical in Decidable.or_iff_not_not_and_not

/--
@isnad1 id=iff.0h2v.s3.a08e94239e48 from=seed src=0 shape=158a0239 vocab=e3b0c442
-/
theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  open scoped Classical in Decidable.and_iff_not_not_or_not

/--
@isnad1 id=iff.0h2v.s3.4366c9ad927f from=seed src=0 shape=a4f5e7a3 vocab=8ad60361
-/
@[simp] theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor, not_or, not_not, ← iff_iff_implies_and_implies]

/--
@isnad1 id=iff.0h2v.s3.77697a17a24f from=seed src=0 shape=5f3827e2 vocab=8ad60361
-/
theorem xor_iff_not_iff (P Q : Prop) : Xor P Q ↔ ¬(P ↔ Q) := (not_xor P Q).not_right

/--
@isnad1 id=iff.0h2v.s3.90d9bf0e0617 from=seed src=0 shape=5465c352 vocab=8ad60361
-/
theorem xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b) := by simp only [← @xor_not_right a, not_not]

/--
@isnad1 id=iff.0h2v.s3.1adddfed0e3b from=seed src=0 shape=3fe615eb vocab=8ad60361
-/
theorem xor_iff_not_iff' : Xor a b ↔ (¬a ↔ b) := by simp only [← @xor_not_left _ b, not_not]

/--
@isnad1 id=iff.0h2v.s4.261673c481ad from=seed src=0 shape=7d34cf49 vocab=8ad60361
-/
theorem xor_iff_or_and_not_and (a b : Prop) : Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b)) := by
  rw [Xor, or_and_right, not_and_or, and_or_left, and_not_self_iff, false_or,
    and_or_left, and_not_self_iff, or_false]

end Propositional

/-! ### Declarations about equality -/

section Equality

-- todo: change name
/--
@isnad1 id=iff.0h3v.s5.7f068d255446 from=seed src=0 shape=dfd49fd3 vocab=e3b0c442
-/
theorem forall_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
    (∀ a, s a → ∀ b, s b → p a b) ↔ ∀ a b, s a → s b → p a b :=
  ⟨fun h a b ha hb ↦ h a ha b hb, fun h a ha b hb ↦ h a b ha hb⟩

/--
@isnad1 id=iff.0h4v.s5.0cba4fcd9674 from=seed src=0 shape=95219f43 vocab=80addd8f
-/
theorem forall_mem_comm {α β} [Membership α β] {s : β} {p : α → α → Prop} :
    (∀ a (_ : a ∈ s) b (_ : b ∈ s), p a b) ↔ ∀ a b, a ∈ s → b ∈ s → p a b :=
  forall_cond_comm


/--
@isnad1 id=ne.2h4v.s4.7652ba1e3574 from=seed src=0 shape=0b73c5ed vocab=e3b0c442
-/
lemma ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c := h₁.symm ▸ h₂
/--
@isnad1 id=ne.2h4v.s4.2f7756fe40e2 from=seed src=0 shape=b44516e1 vocab=e3b0c442
-/
lemma ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c := h₂ ▸ h₁

/--
@isnad1 id=ne.2h4v.s4.7652ba1e3574 from=seed src=0 shape=0b73c5ed vocab=e3b0c442
-/
alias Eq.trans_ne := ne_of_eq_of_ne
/--
@isnad1 id=ne.2h4v.s4.2f7756fe40e2 from=seed src=0 shape=b44516e1 vocab=e3b0c442
-/
alias Ne.trans_eq := ne_of_ne_of_eq

theorem eq_equivalence {α : Sort*} : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

-- @[simp] -- FIXME simp ignores proof rewrites
/--
@isnad1 id=eq.1h5v.s4.a9ad5d8bba3c from=seed src=0 shape=128f414b vocab=a9eb6aed
-/
theorem congr_refl_left {α β : Sort*} (f : α → β) {a b : α} (h : a = b) :
    congr (Eq.refl f) h = congr_arg f h := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
@isnad1 id=eq.1h5v.s5.c4dfbd001bbb from=seed src=0 shape=2e384f64 vocab=8e0a2577
-/
theorem congr_refl_right {α β : Sort*} {f g : α → β} (h : f = g) (a : α) :
    congr h (Eq.refl a) = congr_fun h a := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
@isnad1 id=eq.0h4v.s4.7ac812e2cd25 from=seed src=0 shape=8db88519 vocab=a0318e43
-/
theorem congr_arg_refl {α β : Sort*} (f : α → β) (a : α) :
    congr_arg f (Eq.refl a) = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
@isnad1 id=eq.0h4v.s4.7ac812e2cd25 from=seed src=0 shape=8db88519 vocab=dea3c00b
-/
theorem congr_fun_rfl {α β : Sort*} (f : α → β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
@isnad1 id=eq.1h7v.s5.17078c43486e from=seed src=0 shape=c87b20ee vocab=3fc358f5
-/
theorem congr_fun_congr_arg {α β γ : Sort*} (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a ↦ f a b) p := rfl

/--
@isnad1 id=heq.2h7v.s5.4057281acea6 from=seed src=0 shape=1e597fc4 vocab=92429e3d
-/
theorem rec_heq_of_heq {α β : Sort _} {a b : α} {C : α → Sort*} {x : C a} {y : β}
    (e : a = b) (h : x ≍ y) : e ▸ x ≍ y :=
  eqRec_heq_iff.mpr h

/--
@isnad1 id=iff.1h5v.s4.7fcd5b8e3143 from=seed src=0 shape=79a20820 vocab=df1b483c
-/
@[simp]
theorem cast_heq_iff_heq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) :
    cast e a ≍ c ↔ a ≍ c := by subst e; rfl

/--
@isnad1 id=iff.1h5v.s4.6903fe39dd9e from=seed src=0 shape=f1834f2a vocab=df1b483c
-/
@[simp]
theorem heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :
    a ≍ cast e b ↔ a ≍ b := by subst e; rfl

universe u
variable {α β : Sort u} {e : β = α} {a : α} {b : β}

/--
@isnad1 id=heq.2h4v.s4.b1d3d2315609 from=seed src=0 shape=1daf48be vocab=df1b483c
-/
lemma heq_of_eq_cast (e : β = α) : a = cast e b → a ≍ b := by rintro rfl; simp

lemma eq_cast_iff_heq : a = cast e b ↔ a ≍ b := ⟨heq_of_eq_cast _, fun h ↦ by cases h; rfl⟩

/--
@isnad1 id=iff.0h4v.s5.00d18bc16efe from=seed src=0 shape=9a5a3253 vocab=df1b483c
-/
lemma heq_iff_exists_eq_cast :
    a ≍ b ↔ ∃ (h : β = α), a = cast h b :=
  ⟨fun h ↦ ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩,
    by rintro ⟨rfl, h⟩; rw [h, cast_eq]⟩

/--
@isnad1 id=iff.0h4v.s5.eaac479b1338 from=seed src=0 shape=61909dd4 vocab=df1b483c
-/
lemma heq_iff_exists_cast_eq :
    a ≍ b ↔ ∃ (h : α = β), cast h a = b := by
  simp only [heq_comm (a := a), heq_iff_exists_eq_cast, eq_comm]

end Equality

/-! ### Declarations about quantifiers -/
section Quantifiers
section Dependent

variable {α : Sort*} {β : α → Sort*} {γ : ∀ a, β a → Sort*}

/--
@isnad1 id=var.0h8v.s5.4d0d1919dcc8 from=seed src=0 shape=4d0d1919 vocab=e3b0c442
-/
theorem forall₂_imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∀ a b, p a b) → ∀ a b, q a b :=
  forall_imp fun i ↦ forall_imp <| h i

/--
@isnad1 id=var.0h10v.s6.b80b4fc0bc31 from=seed src=0 shape=b80b4fc0 vocab=e3b0c442
-/
theorem forall₃_imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∀ a b c, p a b c) → ∀ a b c, q a b c :=
  forall_imp fun a ↦ forall₂_imp <| h a

/--
@isnad1 id=ex.1h5v.s6.3af109e02942 from=seed src=0 shape=462da425 vocab=e3b0c442
-/
theorem Exists₂.imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∃ a b, p a b) → ∃ a b, q a b :=
  Exists.imp fun a ↦ Exists.imp <| h a

/--
@isnad1 id=ex.1h6v.s6.2550eac1731c from=seed src=0 shape=5660df3b vocab=e3b0c442
-/
theorem Exists₃.imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∃ a b c, p a b c) → ∃ a b c, q a b c :=
  Exists.imp fun a ↦ Exists₂.imp <| h a

end Dependent

variable {α β : Sort*} {p : α → Prop}

/--
@isnad1 id=iff.0h3v.s4.dbb3f088482f from=seed src=0 shape=44821f2c vocab=e3b0c442
-/
@[deprecated (since := "2026-03-25")] alias forall_swap := forall_comm

/--
@isnad1 id=iff.0h5v.s5.52209a56daf0 from=seed src=0 shape=207a65bd vocab=e3b0c442
-/
theorem forall₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := ⟨swap₂, swap₂⟩

/--
@isnad1 id=iff.0h5v.s5.52209a56daf0 from=seed src=0 shape=207a65bd vocab=e3b0c442
-/
@[deprecated (since := "2026-03-25")] alias forall₂_swap := forall₂_comm

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_comm`.
@isnad1 id=iff.0h3v.s4.75dcc70bf120 from=seed src=0 shape=8ef9c265 vocab=e3b0c442
-/
theorem imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ ∀ x, p → q x :=
  forall_comm

/--
@isnad1 id=iff.0h2v.s4.cce3b5e29b9d from=seed src=0 shape=6071b139 vocab=e3b0c442
-/
lemma imp_forall_iff_forall (A : Prop) (B : A → Prop) : (A → ∀ h : A, B h) ↔ ∀ h : A, B h := by
  by_cases h : A <;> simp [h]

/--
@isnad1 id=iff.0h3v.s5.4008bede6065 from=seed src=0 shape=71eb5011 vocab=e3b0c442
-/
@[deprecated (since := "2026-03-25")] alias exists_swap := exists_comm

/--
@isnad1 id=iff.0h4v.s5.ecb923d88634 from=seed src=0 shape=48a88157 vocab=e3b0c442
-/
theorem exists_and_exists_comm {P : α → Prop} {Q : β → Prop} :
    (∃ a, P a) ∧ (∃ b, Q b) ↔ ∃ a b, P a ∧ Q b :=
  ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨a, b, ⟨ha, hb⟩⟩, fun ⟨a, b, ⟨ha, hb⟩⟩ ↦ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

export Classical (not_forall)

/--
@isnad1 id=iff.0h2v.s4.af437e58f3cb from=seed src=0 shape=7e895b65 vocab=e3b0c442
-/
theorem not_forall_not : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  open scoped Classical in Decidable.not_forall_not

export Classical (not_exists_not)

/--
@isnad1 id=or.0h2v.s4.dc3b42df6681 from=seed src=0 shape=6cff65eb vocab=e3b0c442
-/
lemma forall_or_exists_not (P : α → Prop) : (∀ a, P a) ∨ ∃ a, ¬P a := by
  rw [← not_forall]; exact em _

/--
@isnad1 id=or.0h2v.s4.044482838ded from=seed src=0 shape=3c4f6e81 vocab=e3b0c442
-/
lemma exists_or_forall_not (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬P a := by
  rw [← not_exists]; exact em _

/--
@isnad1 id=iff.0h3v.s4.f3463aab7586 from=seed src=0 shape=c165782b vocab=b65656d3
-/
theorem forall_imp_iff_exists_imp {α : Sort*} {p : α → Prop} {b : Prop} [ha : Nonempty α] :
    (∀ x, p x) → b ↔ ∃ x, p x → b := by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h ↦ not_forall_not.1 fun h' ↦ ?_, fun ⟨x, hx⟩ h ↦ hx (h x)⟩
  exact if hb : b then h' a fun _ ↦ hb else hb <| h fun x ↦ (Classical.not_imp.1 (h' x)).1

/--
@isnad1 id=iff.0h1v.s2.d16869ca57c5 from=seed src=0 shape=36947310 vocab=e3b0c442
-/
@[mfld_simps]
theorem forall_true_iff : (α → True) ↔ True := imp_true_iff _

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
/--
@isnad1 id=iff.1h2v.s4.459ed71c87d3 from=seed src=0 shape=31919a11 vocab=e3b0c442
-/
theorem forall_true_iff' (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
  iff_true_intro fun _ ↦ of_iff_true (h _)

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
/--
@isnad1 id=iff.0h2v.s3.d9e930c8b3b5 from=seed src=0 shape=b18903a0 vocab=e3b0c442
-/
theorem forall₂_true_iff {β : α → Sort*} : (∀ a, β a → True) ↔ True := by simp

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
/--
@isnad1 id=iff.0h3v.s4.8a74d8c3aff7 from=seed src=0 shape=7a859eee vocab=e3b0c442
-/
theorem forall₃_true_iff {β : α → Sort*} {γ : ∀ a, β a → Sort*} :
    (∀ (a) (b : β a), γ a b → True) ↔ True := by simp

/--
@isnad1 id=iff.0h3v.s4.1bde15149ac1 from=seed src=0 shape=d8ec9687 vocab=2142619d
-/
theorem Decidable.and_forall_ne [DecidableEq α] (a : α) {p : α → Prop} :
    (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]

/--
@isnad1 id=iff.0h3v.s4.7272e08bab73 from=seed src=0 shape=2766d00a vocab=e3b0c442
-/
theorem and_forall_ne (a : α) : (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b :=
  open scoped Classical in Decidable.and_forall_ne a

/--
@isnad1 id=or.1h4v.s4.0af1dd1bcc61 from=seed src=0 shape=1aa5a283 vocab=e3b0c442
-/
theorem Ne.ne_or_ne {x y : α} (z : α) (h : x ≠ y) : x ≠ z ∨ y ≠ z :=
  not_and_or.1 <| mt (and_imp.2 (· ▸ ·)) h.symm

/--
@isnad1 id=ex.0h4v.s4.2294226e6a19 from=seed src=0 shape=90dec19a vocab=e3b0c442
-/
@[simp]
theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a := ⟨a', rfl⟩

/--
@isnad1 id=ex.0h6v.s5.bac08842e948 from=seed src=0 shape=774013ce vocab=e3b0c442
-/
@[simp]
lemma exists_apply_eq_apply2 {α β γ} {f : α → β → γ} {a : α} {b : β} : ∃ x y, f x y = f a b :=
  ⟨a, b, rfl⟩

/--
@isnad1 id=ex.0h6v.s5.df45e71493f9 from=seed src=0 shape=41ea1b77 vocab=e3b0c442
-/
@[simp]
lemma exists_apply_eq_apply2' {α β γ} {f : α → β → γ} {a : α} {b : β} : ∃ x y, f a b = f x y :=
  ⟨a, b, rfl⟩

/--
@isnad1 id=ex.0h8v.s5.b0652a092c49 from=seed src=0 shape=3c5f76c2 vocab=e3b0c442
-/
@[simp]
lemma exists_apply_eq_apply3 {α β γ δ} {f : α → β → γ → δ} {a : α} {b : β} {c : γ} :
    ∃ x y z, f x y z = f a b c :=
  ⟨a, b, c, rfl⟩

/--
@isnad1 id=ex.0h8v.s5.ae3f93771813 from=seed src=0 shape=c44ff13d vocab=e3b0c442
-/
@[simp]
lemma exists_apply_eq_apply3' {α β γ δ} {f : α → β → γ → δ} {a : α} {b : β} {c : γ} :
    ∃ x y z, f a b c = f x y z :=
  ⟨a, b, c, rfl⟩

/--
The constant function witnesses that
there exists a function sending a given term to a given term.

This is sometimes useful in `simp` to discharge side conditions.
@isnad1 id=ex.0h4v.s4.956e608197dd from=seed src=0 shape=0ab516db vocab=e3b0c442
-/
theorem exists_apply_eq (a : α) (b : β) : ∃ f : α → β, f a = b := ⟨fun _ ↦ b, rfl⟩

/--
@isnad1 id=iff.0h5v.s5.eaf0fdddce4f from=seed src=0 shape=7e9617e7 vocab=e3b0c442
-/
@[simp] theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ ↦ ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ ↦ ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

/--
@isnad1 id=iff.0h4v.s5.47cfcd37e1a0 from=seed src=0 shape=a63a7d2b vocab=e3b0c442
-/
@[simp] theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
    (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
  ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ ↦ ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ ↦ ⟨f a, ⟨a, rfl⟩, ha⟩⟩

/--
@isnad1 id=iff.0h7v.s6.323b57c45feb from=seed src=0 shape=94cd8a40 vocab=e3b0c442
-/
@[simp] theorem exists_exists_and_exists_and_eq_and {α β γ : Type*}
    {f : α → β → γ} {p : α → Prop} {q : β → Prop} {r : γ → Prop} :
    (∃ c, (∃ a, p a ∧ ∃ b, q b ∧ f a b = c) ∧ r c) ↔ ∃ a, p a ∧ ∃ b, q b ∧ r (f a b) :=
  ⟨fun ⟨_, ⟨a, ha, b, hb, hab⟩, hc⟩ ↦ ⟨a, ha, b, hb, hab.symm ▸ hc⟩,
    fun ⟨a, ha, b, hb, hab⟩ ↦ ⟨f a b, ⟨a, ha, b, hb, rfl⟩, hab⟩⟩

/--
@isnad1 id=iff.0h5v.s5.22ad092e735a from=seed src=0 shape=042aedd7 vocab=e3b0c442
-/
@[simp] theorem exists_exists_exists_and_eq {α β γ : Type*}
    {f : α → β → γ} {p : γ → Prop} :
    (∃ c, (∃ a, ∃ b, f a b = c) ∧ p c) ↔ ∃ a, ∃ b, p (f a b) :=
  ⟨fun ⟨_, ⟨a, b, hab⟩, hc⟩ ↦ ⟨a, b, hab.symm ▸ hc⟩,
    fun ⟨a, b, hab⟩ ↦ ⟨f a b, ⟨a, b, rfl⟩, hab⟩⟩

/--
@isnad1 id=iff.0h4v.s5.a615c92157bb from=seed src=0 shape=fa4e3eed vocab=e3b0c442
-/
theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ a b, f a = b → p b) ↔ ∀ a, p (f a) := by simp

/--
@isnad1 id=iff.0h4v.s5.80371411e1bc from=seed src=0 shape=702b03b5 vocab=e3b0c442
-/
theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ a b, b = f a → p b) ↔ ∀ a, p (f a) := by simp

/--
@isnad1 id=iff.0h5v.s6.cb4392ddfb94 from=seed src=0 shape=708864ce vocab=e3b0c442
-/
theorem exists₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

/--
@isnad1 id=iff.0h3v.s5.bdf685dcb4d6 from=seed src=0 shape=283d234d vocab=d9c5367d
-/
theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ ↦ ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ ↦ ⟨⟨hp, hq⟩, H⟩⟩

/--
@isnad1 id=or.1h4v.s4.efc3c5cbdcaf from=seed src=0 shape=74c8cef2 vocab=e3b0c442
-/
theorem forall_or_of_or_forall {α : Sort*} {p : α → Prop} {b : Prop} (h : b ∨ ∀ x, p x) (x : α) :
    b ∨ p x :=
  h.imp_right fun h₂ ↦ h₂ x

-- See Note [decidable namespace]
/--
@isnad1 id=iff.0h3v.s4.634b69f9d8f5 from=seed src=0 shape=d030ecce vocab=4aa5ae2c
-/
protected theorem Decidable.forall_or_left {q : Prop} {p : α → Prop} [Decidable q] :
    (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  ⟨fun h ↦ if hq : q then Or.inl hq else
    Or.inr fun x ↦ (h x).resolve_left hq, forall_or_of_or_forall⟩

/--
@isnad1 id=iff.0h3v.s4.8f3e70bac320 from=seed src=0 shape=56fd4123 vocab=e3b0c442
-/
theorem forall_or_left {q} {p : α → Prop} : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  open scoped Classical in Decidable.forall_or_left

-- See Note [decidable namespace]
/--
@isnad1 id=iff.0h3v.s4.ebd6cf55d7ae from=seed src=0 shape=d3041b13 vocab=4aa5ae2c
-/
protected theorem Decidable.forall_or_right {q} {p : α → Prop} [Decidable q] :
    (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q := by simp [or_comm, Decidable.forall_or_left]

/--
@isnad1 id=iff.0h3v.s4.10c1a969158f from=seed src=0 shape=dc1954bb vocab=e3b0c442
-/
theorem forall_or_right {q} {p : α → Prop} : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  open scoped Classical in Decidable.forall_or_right

/--
@isnad1 id=iff.0h3v.s4.fb31661fcc8f from=seed src=0 shape=ce95d453 vocab=d9c5367d
-/
@[simp]
theorem forall_and_index {p q : Prop} {r : p ∧ q → Prop} :
    (∀ h : p ∧ q, r h) ↔ ∀ (hp : p) (hq : q), r ⟨hp, hq⟩ :=
  ⟨fun h hp hq ↦ h ⟨hp, hq⟩, fun h h1 ↦ h h1.1 h1.2⟩

/--
@isnad1 id=iff.0h3v.s4.3bfbae3b0d9d from=seed src=0 shape=35672dc7 vocab=8776a278
-/
theorem forall_and_index' {p q : Prop} {r : p → q → Prop} :
    (∀ (hp : p) (hq : q), r hp hq) ↔ ∀ h : p ∧ q, r h.1 h.2 :=
  (forall_and_index (r := fun h => r h.1 h.2)).symm

/--
@isnad1 id=var.1h2v.s3.b0a9114cc797 from=seed src=0 shape=0be5e070 vocab=e3b0c442
-/
theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h

/--
@isnad1 id=var.1h2v.s3.a63fc7def9d1 from=seed src=0 shape=b516986e vocab=13ba8b66
-/
theorem Exists.snd {b : Prop} {p : b → Prop} : ∀ h : Exists p, p h.fst
  | ⟨_, h⟩ => h

/--
@isnad1 id=iff.0h1v.s4.1c7fc0f1cee1 from=seed src=0 shape=39538981 vocab=e3b0c442
-/
theorem Prop.exists_iff {p : Prop → Prop} : (∃ h, p h) ↔ p False ∨ p True :=
  ⟨fun ⟨h₁, h₂⟩ ↦ by_cases (fun H : h₁ ↦ .inr <| by simpa only [H] using h₂)
    (fun H ↦ .inl <| by simpa only [H] using h₂), fun h ↦ h.elim (.intro _) (.intro _)⟩

/--
@isnad1 id=iff.0h1v.s4.4b27853cc488 from=seed src=0 shape=cc7895d2 vocab=e3b0c442
-/
theorem Prop.forall_iff {p : Prop → Prop} : (∀ h, p h) ↔ p False ∧ p True :=
  ⟨fun H ↦ ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h ↦ by by_cases H : h <;> simpa only [H]⟩

/--
@isnad1 id=iff.0h3v.s4.67f2c2ee4c73 from=seed src=0 shape=c5bfb2f2 vocab=e3b0c442
-/
theorem exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
  ⟨Exists.fst, fun H ↦ ⟨H, h H⟩⟩

/--
@isnad1 id=not.1h2v.s4.bb8481529aa7 from=seed src=0 shape=943da41f vocab=e3b0c442
-/
theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ h' : p, q h' :=
  mt Exists.fst

/-! See `IsEmpty.exists_iff` for the `False` version of `exists_true_left`. -/

/--
@isnad1 id=iff.2h4v.s5.bf1b3aae6e3f from=seed src=0 shape=054fa82f vocab=ff01181e
-/
theorem forall_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 ↦ (hq _).1 (h1 (hp.2 h2)), fun h1 h2 ↦ (hq _).2 (h1 (hp.1 h2))⟩

/--
@isnad1 id=eq.2h4v.s5.a334a32be14f from=seed src=0 shape=35d56780 vocab=ff01181e
-/
theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq hp)

/--
@isnad1 id=eq.2h4v.s4.840670bb9e66 from=seed src=0 shape=abe47350 vocab=e3b0c442
-/
lemma imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)

/--
@isnad1 id=eq.2h4v.s4.0dc9d9a9b9a3 from=seed src=0 shape=6045b177 vocab=e3b0c442
-/
lemma imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c → b = d) : (a → b) = (c → d) :=
  propext (imp_congr_ctx h₁.to_iff fun hc ↦ (h₂ hc).to_iff)

lemma eq_true_intro {a : Prop} (h : a) : a = True := propext (iff_true_intro h)

lemma eq_false_intro {a : Prop} (h : ¬a) : a = False := propext (iff_false_intro h)

-- FIXME: `alias` creates `def Iff.eq := propext` instead of `lemma Iff.eq := propext`
alias Iff.eq := propext

/--
@isnad1 id=eq.0h2v.s3.a582bec3e089 from=seed src=0 shape=992bfa65 vocab=e3b0c442
-/
lemma iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := propext ⟨propext, Eq.to_iff⟩

-- They were not used in Lean 3 and there are already lemmas with those names in Lean 4

/-- See `IsEmpty.forall_iff` for the `False` version.
@isnad1 id=iff.0h1v.s3.5c52b985a544 from=seed src=0 shape=0bad438e vocab=b89f9d1b
-/
@[simp] theorem forall_true_left (p : True → Prop) : (∀ x, p x) ↔ p True.intro :=
  forall_prop_of_true _

/--
@isnad1 id=iff.0h2v.s4.34569a7248c0 from=seed src=0 shape=8464cb2b vocab=bd373721
-/
@[simp]
lemma Subsingleton.forall₂_iff {ι : Sort*} [Subsingleton ι] (P : ι → ι → Prop) :
    (∀ i j, P i j) ↔ (∀ i, P i i) := by
  refine forall_congr' fun i ↦ ?_
  have : Nonempty ι := ⟨i⟩
  simp [Subsingleton.elim _ i]

end Quantifiers

/-! ### Classical lemmas -/

namespace Classical

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `Classical.propDecidable`. -/
@[instance_reducible]
noncomputable def dec (p : Prop) : Decidable p := by infer_instance

variable {α : Sort*}

/-- Any predicate `p` is decidable classically. -/
@[instance_reducible]
noncomputable def decPred (p : α → Prop) : DecidablePred p := by infer_instance

/-- Any relation `p` is decidable classically. -/
@[instance_reducible]
noncomputable def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance

/-- Any type `α` has decidable equality classically. -/
@[instance_reducible]
noncomputable def decEq (α : Sort*) : DecidableEq α := by infer_instance

/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
noncomputable def existsCases {α C : Sort*} {p : α → Prop} (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

/--
@isnad1 id=var.1h4v.s5.18943930e494 from=seed src=0 shape=d211049c vocab=81e08635
-/
theorem some_spec₂ {α : Sort*} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

/-- A version of `byContradiction` that uses types instead of propositions. -/
protected noncomputable def byContradiction' {α : Sort*} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h ↦ (H fun a ↦ h ⟨a⟩).elim

/-- `Classical.byContradiction'` is equivalent to lean's axiom `Classical.choice`. -/
def choice_of_byContradiction' {α : Sort*} (contra : ¬(α → False) → α) : Nonempty α → α :=
  fun H ↦ contra H.elim

-- This can be removed after https://github.com/leanprover/lean4/pull/11316
-- arrives in a release candidate.
grind_pattern Exists.choose_spec => P.choose

/--
@isnad1 id=eq.0h2v.s4.e60378934d65 from=seed src=0 shape=89b4ba28 vocab=1e8173a4
-/
@[simp] lemma choose_eq (a : α) : @Exists.choose _ (· = a) ⟨a, rfl⟩ = a := @choose_spec _ (· = a) _

/--
@isnad1 id=eq.0h2v.s4.48043070d83c from=seed src=0 shape=d6a91280 vocab=1e8173a4
-/
@[simp]
lemma choose_eq' (a : α) : @Exists.choose _ (a = ·) ⟨a, rfl⟩ = a :=
  (@choose_spec _ (a = ·) _).symm

/--
@isnad1 id=ex.1h3v.s5.d0444d9c8a11 from=seed src=0 shape=69e720d1 vocab=e3b0c442
-/
alias axiom_of_choice := axiomOfChoice -- TODO: remove? rename in core?
/--
@isnad1 id=var.0h4v.s3.630ed044c8ad from=seed src=0 shape=fc4e2dd6 vocab=e3b0c442
-/
alias by_cases := byCases -- TODO: remove? rename in core?
/--
@isnad1 id=var.1h1v.s3.fa73f61d2499 from=seed src=0 shape=36c77bf5 vocab=e3b0c442
-/
alias by_contradiction := byContradiction -- TODO: remove? rename in core?

-- The remaining theorems in this section were ported from Lean 3,
-- but are currently unused in Mathlib, so have been deprecated.
-- If any are being used downstream, please remove the deprecation.

/--
@isnad1 id=or.0h1v.s3.4b1f92fe0cd5 from=seed src=0 shape=c91dcabb vocab=e3b0c442
-/
alias prop_complete := propComplete -- TODO: remove? rename in core?

end Classical

/-- This function has the same type as `Exists.recOn`, and can be used to case on an equality,
but `Exists.recOn` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
noncomputable def Exists.classicalRecOn {α : Sort*} {p : α → Prop} (h : ∃ a, p a)
    {C : Sort*} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)

/-! ### Declarations about bounded quantifiers -/
section BoundedQuantifiers

variable {α : Sort*} {r p q : α → Prop} {P Q : ∀ x, p x → Prop}

/--
@isnad1 id=iff.0h3v.s5.767f96c6d91b from=seed src=0 shape=bc425133 vocab=e3b0c442
-/
theorem bex_def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩⟩

/--
@isnad1 id=var.1h5v.s5.cb642aad8588 from=seed src=0 shape=2254c4f4 vocab=e3b0c442
-/
theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂

/--
@isnad1 id=ex.0h6v.s5.979d4c2b16df from=seed src=0 shape=5d28946a vocab=e3b0c442
-/
theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩

/--
@isnad1 id=var.0h8v.s5.613139f48f8f from=seed src=0 shape=613139f4 vocab=e3b0c442
-/
theorem BAll.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _

/--
@isnad1 id=ex.1h5v.s6.6a0fbe881661 from=seed src=0 shape=ef34653d vocab=e3b0c442
-/
theorem BEx.imp_right (H : ∀ x h, P x h → Q x h) : (∃ x h, P x h) → ∃ x h, Q x h
  | ⟨_, _, h'⟩ => ⟨_, _, H _ _ h'⟩

/--
@isnad1 id=var.0h8v.s5.2d4d59419b30 from=seed src=0 shape=2d4d5941 vocab=e3b0c442
-/
theorem BAll.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h

/--
@isnad1 id=ex.1h5v.s5.316878b0fd89 from=seed src=0 shape=1a4f4c15 vocab=e3b0c442
-/
theorem BEx.imp_left (H : ∀ x, p x → q x) : (∃ (x : _) (_ : p x), r x) → ∃ (x : _) (_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩

/--
@isnad1 id=ex.1h4v.s5.692f69aa390d from=seed src=0 shape=685675a5 vocab=e3b0c442
-/
theorem exists_mem_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩

/--
@isnad1 id=ex.1h3v.s5.e3a6b8ca5e93 from=seed src=0 shape=0bc7f4c4 vocab=e3b0c442
-/
theorem exists_of_exists_mem : (∃ (x : _) (_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩


/--
@isnad1 id=iff.0h3v.s5.f1979d3666a7 from=seed src=0 shape=b7e4c800 vocab=e3b0c442
-/
theorem not_exists_mem : (¬∃ x h, P x h) ↔ ∀ x h, ¬P x h := exists₂_imp

/--
@isnad1 id=not.1h3v.s5.338f4cf19f31 from=seed src=0 shape=017b12c3 vocab=e3b0c442
-/
theorem not_forall₂_of_exists₂_not : (∃ x h, ¬P x h) → ¬∀ x h, P x h
  | ⟨x, h, hp⟩, al => hp <| al x h

-- See Note [decidable namespace]
/--
@isnad1 id=iff.0h3v.s6.057f2887fe77 from=seed src=0 shape=0023a913 vocab=4aa5ae2c
-/
protected theorem Decidable.not_forall₂ [Decidable (∃ x h, ¬P x h)] [∀ x h, Decidable (P x h)] :
    (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h ↦ nx.decidable_imp_symm
    fun h' ↦ ⟨x, h, h'⟩, not_forall₂_of_exists₂_not⟩

/--
@isnad1 id=iff.0h3v.s5.7dc7c0af2983 from=seed src=0 shape=6fed0f5d vocab=e3b0c442
-/
theorem not_forall₂ : (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  open scoped Classical in Decidable.not_forall₂

/--
@isnad1 id=iff.0h4v.s5.6a8fd31bb63c from=seed src=0 shape=829342e7 vocab=e3b0c442
-/
theorem forall₂_and : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ ∀ x h, Q x h :=
  Iff.trans (forall_congr' fun _ ↦ forall_and) forall_and

/--
@isnad1 id=iff.0h3v.s4.5f2af3d35f72 from=seed src=0 shape=f487155e vocab=b65656d3
-/
theorem forall_and_left [Nonempty α] (q : Prop) (p : α → Prop) :
    (∀ x, q ∧ p x) ↔ (q ∧ ∀ x, p x) := by rw [forall_and, forall_const]

/--
@isnad1 id=iff.0h3v.s4.076a25218bfb from=seed src=0 shape=a46fe027 vocab=b65656d3
-/
theorem forall_and_right [Nonempty α] (p : α → Prop) (q : Prop) :
    (∀ x, p x ∧ q) ↔ (∀ x, p x) ∧ q := by rw [forall_and, forall_const]

/--
@isnad1 id=iff.0h4v.s6.49f23c90081b from=seed src=0 shape=6e6e1b82 vocab=e3b0c442
-/
theorem exists_mem_or : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ ∃ x h, Q x h :=
  Iff.trans (exists_congr fun _ ↦ exists_or) exists_or

/--
@isnad1 id=iff.0h4v.s5.b10754850ede from=seed src=0 shape=068d48bb vocab=e3b0c442
-/
theorem forall₂_or_left : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ ∀ x, q x → r x :=
  Iff.trans (forall_congr' fun _ ↦ or_imp) forall_and

/--
@isnad1 id=iff.0h4v.s6.e0993d9d9079 from=seed src=0 shape=3730411d vocab=e3b0c442
-/
theorem exists_mem_or_left :
    (∃ (x : _) (_ : p x ∨ q x), r x) ↔ (∃ (x : _) (_ : p x), r x) ∨ ∃ (x : _) (_ : q x), r x := by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x ↦ or_and_right) exists_or

end BoundedQuantifiers

section ite

variable {α : Sort*} {σ : α → Sort*} {P Q R : Prop} [Decidable P]
  {a b c : α} {A : P → α} {B : ¬P → α}

/--
@isnad1 id=iff.0h5v.s5.473ef19bb953 from=seed src=0 shape=6aa405dd vocab=b35639d5
-/
theorem dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]

/--
@isnad1 id=iff.0h5v.s5.a378512750a9 from=seed src=0 shape=7a5619e0 vocab=af84458f
-/
theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  dite_eq_iff.trans <| by rw [exists_prop, exists_prop]

theorem eq_ite_iff : a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c :=
  eq_comm.trans <| ite_eq_iff.trans <| (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)

/--
@isnad1 id=iff.0h5v.s5.a9afaa0f9180 from=seed src=0 shape=73e6f8a8 vocab=b35639d5
-/
theorem dite_eq_iff' : dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he ↦ ⟨fun h ↦ (dite_eq_left h).symm.trans he, fun h ↦ (dite_eq_right h).symm.trans he⟩,
    fun he ↦ (em P).elim (fun h ↦ (dite_eq_left h).trans <| he.1 h) fun h ↦
      (dite_eq_right h).trans <| he.2 h⟩

/--
@isnad1 id=iff.0h5v.s5.2b9ffb091e57 from=seed src=0 shape=0c46aadd vocab=af84458f
-/
theorem ite_eq_iff' : ite P a b = c ↔ (P → a = c) ∧ (¬P → b = c) := dite_eq_iff'

/--
@isnad1 id=iff.0h4v.s5.093f6505c980 from=seed src=0 shape=93de4e68 vocab=b35639d5
-/
theorem dite_ne_left_iff : dite P (fun _ ↦ a) B ≠ a ↔ ∃ h, a ≠ B h := by
  grind

/--
@isnad1 id=iff.0h4v.s5.5e0300775f5b from=seed src=0 shape=32fcd466 vocab=b35639d5
-/
theorem dite_ne_right_iff : (dite P A fun _ ↦ b) ≠ b ↔ ∃ h, A h ≠ b := by
  simp only [Ne, dite_eq_right_iff, not_forall]

/--
@isnad1 id=iff.0h4v.s4.bd36fbcf0d77 from=seed src=0 shape=a0b200a9 vocab=af84458f
-/
theorem ite_ne_left_iff : ite P a b ≠ a ↔ ¬P ∧ a ≠ b :=
  dite_ne_left_iff.trans <| by rw [exists_prop]

/--
@isnad1 id=iff.0h4v.s4.7c47ab1821a5 from=seed src=0 shape=258d6930 vocab=af84458f
-/
theorem ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b :=
  dite_ne_right_iff.trans <| by rw [exists_prop]

/--
@isnad1 id=iff.1h4v.s5.3a73aff12d6d from=seed src=0 shape=4ada2c5d vocab=b35639d5
-/
protected theorem Ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B = a ↔ P :=
  dite_eq_left_iff.trans ⟨fun H ↦ of_not_not fun h' ↦ h h' (H h').symm, fun h H ↦ (H h).elim⟩

/--
@isnad1 id=iff.1h4v.s5.b76ed0e8ab33 from=seed src=0 shape=31b71bb1 vocab=b35639d5
-/
protected theorem Ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) = b ↔ ¬P :=
  dite_eq_right_iff.trans ⟨fun H h' ↦ h h' (H h'), fun h' H ↦ (h' H).elim⟩

/--
@isnad1 id=iff.1h4v.s4.bb4a8ca265f1 from=seed src=0 shape=ff63fa52 vocab=af84458f
-/
protected theorem Ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ ↦ h

/--
@isnad1 id=iff.1h4v.s4.c0884a29b79a from=seed src=0 shape=cd6c0b0d vocab=af84458f
-/
protected theorem Ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ ↦ h

/--
@isnad1 id=iff.1h4v.s5.ed5586bce443 from=seed src=0 shape=db13b2d5 vocab=b35639d5
-/
protected theorem Ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B ≠ a ↔ ¬P :=
  dite_ne_left_iff.trans <| exists_iff_of_forall h

/--
@isnad1 id=iff.1h4v.s5.8bb198aef56e from=seed src=0 shape=ee655ac3 vocab=b35639d5
-/
protected theorem Ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) ≠ b ↔ P :=
  dite_ne_right_iff.trans <| exists_iff_of_forall h

/--
@isnad1 id=iff.1h4v.s4.d06bc3f5a057 from=seed src=0 shape=dced5307 vocab=af84458f
-/
protected theorem Ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ ↦ h

/--
@isnad1 id=iff.1h4v.s4.3f4fe7138acc from=seed src=0 shape=cc79ccbf vocab=af84458f
-/
protected theorem Ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P :=
  Ne.dite_ne_right_iff fun _ ↦ h

variable (P Q a b)

/--
@isnad1 id=or.0h4v.s5.0d9a5914cc28 from=seed src=0 shape=c8bed219 vocab=b35639d5
-/
theorem dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
  if h : _ then .inl ⟨h, dite_eq_left h⟩ else .inr ⟨h, dite_eq_right h⟩

/--
@isnad1 id=or.0h4v.s4.c9c358b768fa from=seed src=0 shape=6fc3349f vocab=af84458f
-/
theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  if h : _ then .inl (ite_eq_left h) else .inr (ite_eq_right h)

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches.
@isnad1 id=eq.0h9v.s6.c647a854ca46 from=seed src=0 shape=82cf737a vocab=b35639d5
-/
theorem apply_dite₂ {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P]
    (a : P → α) (b : ¬P → α) (c : P → β) (d : ¬P → β) :
    f (dite P a b) (dite P c d) = dite P (fun h ↦ f (a h) (c h)) fun h ↦ f (b h) (d h) := by
  by_cases h : P <;> simp [h]

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches.
@isnad1 id=eq.0h9v.s5.8f26705663ce from=seed src=0 shape=4207e676 vocab=af84458f
-/
theorem apply_ite₂ {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) fun _ ↦ d

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`.
@isnad1 id=eq.0h6v.s6.1ee194053d10 from=seed src=0 shape=954f728e vocab=b35639d5
-/
theorem dite_apply (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h ↦ f h a) fun h ↦ g h a := by by_cases h : P <;> simp [h]

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`.
@isnad1 id=eq.0h6v.s5.37aca8e642a3 from=seed src=0 shape=38293c7a vocab=af84458f
-/
theorem ite_apply (f g : ∀ a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ ↦ f) (fun _ ↦ g) a

/--
@isnad1 id=eq.0h8v.s5.e0df4523177f from=seed src=0 shape=c193ca3b vocab=af84458f
-/
theorem apply_ite_left {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P]
    (x y : α) (z : β) : f (if P then x else y) z = if P then f x z else f y z := by grind

section
variable [Decidable Q]

/--
@isnad1 id=eq.0h5v.s5.5c033a4af587 from=seed src=0 shape=3a3da119 vocab=af84458f
-/
theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/--
@isnad1 id=eq.0h5v.s5.0ee9a18fdb8c from=seed src=0 shape=de1cdb08 vocab=af84458f
-/
theorem ite_or : ite (P ∨ Q) a b = ite P a (ite Q a b) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/--
@isnad1 id=eq.1h6v.s6.f481a320cbd4 from=seed src=0 shape=dba87f2c vocab=b35639d5
-/
theorem dite_dite_comm {B : Q → α} {C : ¬P → ¬Q → α} (h : P → ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) =
     if q : Q then B q else if p : P then A p else C p q := by
  grind

/--
@isnad1 id=eq.1h6v.s5.98b8dc462ac2 from=seed src=0 shape=83e6075e vocab=af84458f
-/
theorem ite_ite_comm (h : P → ¬Q) :
    (if P then a else if Q then b else c) =
     if Q then b else if P then a else c :=
  dite_dite_comm P Q h

end

variable {P Q}

/--
@isnad1 id=iff.0h3v.s4.fea3524089fa from=seed src=0 shape=fca4f2e8 vocab=af84458f
-/
theorem ite_prop_iff_or : (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R) := by
  by_cases p : P <;> simp [p]

/--
@isnad1 id=iff.0h3v.s5.0e96338504c5 from=seed src=0 shape=04106b46 vocab=b35639d5
-/
theorem dite_prop_iff_or {Q : P → Prop} {R : ¬P → Prop} :
    dite P Q R ↔ (∃ p, Q p) ∨ (∃ p, R p) := by
  by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]

-- TODO make this a simp lemma in a future PR
/--
@isnad1 id=iff.0h3v.s4.e2f4f16ced52 from=seed src=0 shape=0db28c2a vocab=af84458f
-/
theorem ite_prop_iff_and : (if P then Q else R) ↔ ((P → Q) ∧ (¬P → R)) := by
  by_cases p : P <;> simp [p]

/--
@isnad1 id=iff.0h3v.s5.a0950724fab3 from=seed src=0 shape=8656eb37 vocab=b35639d5
-/
theorem dite_prop_iff_and {Q : P → Prop} {R : ¬P → Prop} :
    dite P Q R ↔ (∀ h, Q h) ∧ (∀ h, R h) := by
  by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]

section congr

variable [Decidable Q] {x y u v : α}

/--
@isnad1 id=eq.3h7v.s5.df7646a489bb from=seed src=0 shape=4d276c9c vocab=af84458f
-/
theorem if_ctx_congr (h_c : P ↔ Q) (h_t : Q → x = u) (h_e : ¬Q → y = v) : ite P x y = ite Q u v :=
  ite_congr h_c.eq h_t h_e

/--
@isnad1 id=eq.3h7v.s5.06d809cec145 from=seed src=0 shape=60d112e9 vocab=af84458f
-/
theorem if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y = ite Q u v :=
  if_ctx_congr h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

end congr

/--
@isnad1 id=injectiv.3h5v.s6.10fbeeaddc0e from=seed src=0 shape=2b102924 vocab=3c7a0f99
-/
theorem Function.Injective.ite {α β : Sort*} {p : β → Prop} [DecidablePred p] {g : β → α}
    (hg : g.Injective) {f : β → α} (hf : f.Injective) (h : ∀ x y, g x = f y → x = y) :
    (fun x ↦ if p x then g x else f x).Injective :=
  fun x y _ ↦ by rcases em (p x) with (hx | hx) <;> rcases em (p y) with (hy | hy) <;> grind

end ite

/-! ### Membership -/

/--
@isnad1 id=ne.2h5v.s5.37e53a2c545a from=seed src=0 shape=10ebbfca vocab=80addd8f
-/
alias Membership.mem.ne_of_notMem := ne_of_mem_of_not_mem
/--
@isnad1 id=ne.2h5v.s5.e747cc15a851 from=seed src=0 shape=54c99d34 vocab=80addd8f
-/
alias Membership.mem.ne_of_notMem' := ne_of_mem_of_not_mem'

section Membership

variable {α β : Type*} [Membership α β] {p : Prop} [Decidable p]

/--
@isnad1 id=iff.0h6v.s6.0eebce7b4f48 from=seed src=0 shape=15d011a9 vocab=4e3730aa
-/
theorem mem_dite {a : α} {s : p → β} {t : ¬p → β} :
    (a ∈ if h : p then s h else t h) ↔ (∀ h, a ∈ s h) ∧ (∀ h, a ∈ t h) := by
  by_cases h : p <;> simp [h]

/--
@isnad1 id=iff.0h6v.s6.438de6b1930f from=seed src=0 shape=0ae4c6f8 vocab=4e3730aa
-/
theorem dite_mem {a : p → α} {b : ¬p → α} {s : β} :
    (if h : p then a h else b h) ∈ s ↔ (∀ h, a h ∈ s) ∧ (∀ h, b h ∈ s) := by
  by_cases h : p <;> simp [h]

/--
@isnad1 id=iff.0h6v.s5.acf2ccaa6cdc from=seed src=0 shape=68fed242 vocab=d8d9fded
-/
theorem mem_ite {a : α} {s t : β} : (a ∈ if p then s else t) ↔ (p → a ∈ s) ∧ (¬p → a ∈ t) :=
  mem_dite

/--
@isnad1 id=iff.0h6v.s5.9b6e31de36e4 from=seed src=0 shape=30b7f6c9 vocab=d8d9fded
-/
theorem ite_mem {a b : α} {s : β} : (if p then a else b) ∈ s ↔ (p → a ∈ s) ∧ (¬p → b ∈ s) :=
  dite_mem

end Membership

/--
@isnad1 id=not.1h3v.s4.199f0d4a90d5 from=seed src=0 shape=81a880ac vocab=ea90dce8
-/
theorem not_beq_of_ne {α : Type*} [BEq α] [LawfulBEq α] {a b : α} (ne : a ≠ b) : ¬(a == b) :=
  fun h => ne (eq_of_beq h)

/--
@isnad1 id=eq.0h3v.s5.1d11b06e6298 from=seed src=0 shape=6756f5ce vocab=d39c3457
-/
alias beq_eq_decide := Bool.beq_eq_decide_eq

/--
@isnad1 id=iff.0h6v.s5.b9ff85ff4b6e from=seed src=0 shape=3e259b15 vocab=1b46d1cc
-/
@[simp] lemma beq_eq_beq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
    {b₁ b₂ : β} : (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := by rw [Bool.eq_iff_iff]; simp

/--
@isnad1 id=eq.1h3v.s4.1a2411701998 from=seed src=0 shape=ca02c19a vocab=b920bcee
-/
@[ext]
theorem beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    (h : ∀ x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) :
    inst1 = inst2 := by
  have ⟨beq1⟩ := inst1
  congr
  funext x y
  exact h x y

set_option linter.overlappingInstances false in
/--
@isnad1 id=eq.0h3v.s4.47b15aec8afd from=seed src=0 shape=5184cb33 vocab=4ffe5e76
-/
theorem lawful_beq_subsingleton {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  ext
  simp
