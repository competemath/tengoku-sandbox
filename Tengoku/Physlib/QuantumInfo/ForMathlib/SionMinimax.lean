/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

@[simp]
theorem Set.image2_flip {α β γ : Type*} {f : α → β → γ} (s : Set α) (t : Set β) :
    image2 (flip f) t s = image2 f s t := by
  grind [image2, flip]

section ciSup

variable {ι α : Type*} [ConditionallyCompleteLattice α] {f g : ι → α} {a : α}

variable [Nonempty ι]

end ciSup

variable {α : Type*} [TopologicalSpace α] {β : Type*} [Preorder β] {f g : α → β} {x : α}
  {s t : Set α} {y z : β} {γ : Type*} [LinearOrder γ]

section sion_minimax
/-!
Following https://projecteuclid.org/journals/kodai-mathematical-journal/volume-11/issue-1/Elementary-proof-for-Sions-minimax-theorem/10.2996/kmj/1138038812.full, with some corrections. There are two errors in Lemma 2 and the main theorem: an incorrect step that
`(∀ x, a < f x) → (a < ⨅ x, f x)`. This is repaired by taking an extra `exists_between` to get `a < b < ⨅ ...`, concluding that
`(∀ x, b < f x) → (b ≤ ⨅ x, f x)` and so `(a < ⨅ x, f x)`.
-/

variable  {M : Type*} [NormedAddCommGroup M]
  {N : Type*}
  {f : M → N → ℝ} {S : Set M} {T : Set N}
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hS₁ : IsCompact S) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

include hfc₂ hS₁ hS₃ in

variable [Module ℝ M] [ContinuousSMul ℝ M]
variable [AddCommGroup N] [TopologicalSpace N] [SequentialSpace N] [T2Space N] [ContinuousAdd N] [Module ℝ N] [ContinuousSMul ℝ N]
variable
  (hfc₁ : ∀ x, x ∈ S → UpperSemicontinuousOn (f x) T)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hfq₁ : ∀ x, x ∈ S → QuasiconcaveOn ℝ T (f x))
  (hT₂ : Convex ℝ T) (hS₂ : Convex ℝ S)

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hT₂ hS₃ in

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ in

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
