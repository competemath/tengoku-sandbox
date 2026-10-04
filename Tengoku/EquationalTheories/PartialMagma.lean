-- Tengoku.EquationalTheories.PartialMagma: verified translations of equational_theories/PartialMagma.lean (3 theorems)
import Tengoku.Seed.Data.Finset.Basic
import Tengoku.Seed.Data.Set.Basic
import Tengoku.Seed.Data.Set.Finite.Lattice
import Tengoku.Seed.Data.Countable.Defs
import Tengoku.Seed.Data.Sum.Basic
import Tengoku.Seed.SetTheory.Cardinal.Arithmetic
import Tengoku.EquationalTheories.Deps.Equations
import Tengoku.EquationalTheories.Deps.Magma

set_option linter.all false

namespace EquationalTheories

/-!
  This file is part of the framework for the greedy construction of magmas, see
  https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#greedy-section

  We want to encapsule the following construction: suppose we have a partial magma defined
  on `ℕ` for which `a ◇ b` is not defined for a given pair `a b : ℕ`, but we can extend our
  partial mamga to a larger type `ℕ ⊕ F` such that `a ◇ b` becomes defined. Then by an appropriate
  identification of `ℕ` and `ℕ ⊕ F`, we can in fact find an extension that is defined on `ℕ`.

  For this, we model a partial magma on a type `α` by an element of `PreExtension α := α → α → Set α`
  For a given equation, we are only interested in partial magmas satisfying some laws.
  We encapsulate this in a class `ExtensionRules`. For each greedy construction, we give
  an instance of `ExtensionRules`. Depending on this instance, we define the class `ExtensionBase`
  that collects our extension problem. For each diffierent case in a greedy construction, we extend
  `ExtensionBase` reflecting additional properties that `a` and `b` should satisfy (for example,
  we often treat the cases `a = b` and `a ≠ b` differently). For each such extension problem,
  we manually define a term of `FreshSolution`.

  Given a fresh solution `E'`, we show in this file that `E'.adjoin` is an extension of the original partial magma
  defined over `ℕ`.
-/

namespace PartialMagma

abbrev PreExtension (α : Type) := α → α → Set α

abbrev Equiv.movePreExtension {α β : Type} (e : α ≃ β) (E : PreExtension β) : PreExtension α :=
  fun a b => { c | e c ∈ E (e a) (e b) }

class ExtensionRules where
  laws : ∀ {α : Type}, PreExtension α → Prop
  laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : laws E) : laws (Equiv.movePreExtension e E)

structure PreExtension.OK [r : ExtensionRules] {α : Type} (E : PreExtension α) : Prop where
  finite : Set.Finite {x : (α × α) × α | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  laws : ExtensionRules.laws E

def Equiv.movePreExtensionOK [ExtensionRules] {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : E.OK) :
  (Equiv.movePreExtension e E).OK where
  finite := by
    apply ok.finite.of_equiv
    constructor
    case toFun =>
      refine fun ⟨((a,b),c),h⟩ => ⟨((e.symm a, e.symm b),e.symm c),?_⟩
      simp_all
    case invFun =>
      refine fun ⟨((a,b),c),h⟩ => ⟨((e a, e b),e c),?_⟩
      simp_all
    case left_inv =>
      refine fun ⟨((a,b),c),h⟩ => ?_
      simp_all
    case right_inv =>
      refine fun ⟨((a,b),c),h⟩ => ?_
      simp_all
  func {x y} z z_mem z' z'_mem := by
    have := ok.func z_mem z'_mem
    simpa
  laws := ExtensionRules.laws_equiv e E ok.laws

open ExtensionRules

abbrev Extension (α : Type) [ExtensionRules] := {E : PreExtension α // E.OK}

class ExtensionBase [ExtensionRules]  where
  E : PreExtension ℕ
  ok : E.OK
  a : ℕ
  b : ℕ
  not_def {c} : c ∉ E a b

namespace ExtensionBase

variable [ExtensionRules] [ExtensionBase]

-- Not show how to call this
structure FreshSolution (F : Type) (E' : PreExtension (ℕ ⊕ F)) : Prop where
  base {a b c} : c ∈ E a b → (.inl c) ∈ E' (.inl a) (.inl b)
  ok : PreExtension.OK E' (α := (ℕ ⊕ F))
  ab_def : (E' (.inl a) (.inl b)).Nonempty

abbrev FreshExtension (F : Type) := {E' : PreExtension (ℕ ⊕ F) // FreshSolution F E'}

scoped infix:80 " ◯ " => E

noncomputable def dom : Finset ℕ :=
  insert a <| insert b <| ok.finite.toFinset.biUnion fun ((a, b), c) => {a, b, c}

theorem dom_a : a ∈ dom
:= Finset.mem_insert_self ..

theorem dom_b : b ∈ dom
:= Finset.mem_insert_of_mem <| Finset.mem_insert_self ..

noncomputable def dom_bound := dom.sup id + 1

theorem lt_dom_bound {x} (h : x ∈ dom) : x < dom_bound
:= Nat.lt_succ_iff.2 (dom.le_sup (f := id) h)

end ExtensionBase
end PartialMagma

end EquationalTheories
