-- Tengoku.EquationalTheories.ManuallyProved.Equation1729.Edit: verified translations of equational_theories/ManuallyProved/Equation1729/Edit.lean (4 theorems)
import Tengoku.Seed.Data.Fintype.Basic
import Tengoku.Seed.Logic.Embedding.Basic
import Init.Classical
import Init.Prelude
import Tengoku.EquationalTheories.Deps.Equations
import Tengoku.EquationalTheories.Deps.Magma

set_option linter.all false

-- left unwrapped: this module opens an outside namespace block
open EquationalTheories

/-!
Sets up API for the `Function.Embedding.edit` tool, which takes a function `f : X → Y` and
updates it via an arbitrary embedding `ι : X' ↪ X` and a new function `f' : X' → Y` by
redefining `f (ι x')` to `f' x'` for all `x' : X'`.
-/

namespace Function.Embedding

-- This is for convenience
open Classical

def attains {X' X : Type*} (ι : X' ↪ X) (x : X) : Prop := ∃ x' : X', ι x' = x

def avoids {X' X : Type*} (ι : X' ↪ X) (x : X) : Prop := ∀ x' : X', ι x' ≠ x

lemma attains_image {X' X : Type*} (ι : X' ↪ X) (x' : X') : ι.attains (ι x') := ⟨_, rfl⟩

noncomputable def range_finset {X' X : Type*} (ι : X' ↪ X) [Fintype X'] : Finset X :=
  Finset.image ι Finset.univ

@[simp]
lemma in_range_iff_attains {X' X : Type*} (ι : X' ↪ X) [Fintype X'] (x : X) :
    x ∈ ι.range_finset ↔ ι.attains x := by
  simp [attains, range_finset]

lemma attains_in_range {X' X : Type*} (ι : X' ↪ X) [Fintype X'] (x' : X') :
    ι x' ∈ ι.range_finset
:=
  (ι.in_range_iff_attains ..).mpr <| ι.attains_image ..

lemma avoids_iff_not_attains {X' X : Type*} (ι : X' ↪ X) (x : X) : ι.avoids x ↔ ¬ι.attains x := by
  simp [avoids, ne_eq, attains, not_exists]

lemma avoids_iff_not_in_range {X' X : Type*} (ι : X' ↪ X) [Fintype X'] (x : X) :
    ι.avoids x ↔ x ∉ ι.range_finset
:= by
  rw [ι.avoids_iff_not_attains, in_range_iff_attains]

noncomputable def edit {X X' Y : Type*} (ι : X' ↪ X) (f : X → Y) (f' : X' → Y) (x : X) : Y :=
  if h : ι.attains x then f' h.choose else f x

lemma edit_of_attains {X X' Y : Type*} (ι : X' ↪ X) (f : X → Y) (f' : X' → Y) (x' : X') :
    ι.edit f f' (ι x') = f' x'
:= by
  simp [edit, ι.attains_image]

lemma edit_of_avoids {X X' Y : Type*} (ι : X' ↪ X) (f : X → Y) (f' : X' → Y) {x : X}
    (h : ι.avoids x) : ι.edit f f' x = f x
:= by
  simp_all [edit, ι.avoids_iff_not_attains]

end Function.Embedding
