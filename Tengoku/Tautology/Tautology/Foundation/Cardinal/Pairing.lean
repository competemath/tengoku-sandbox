import Tengoku.Tautology.Tautology.Foundation.Cardinal.Countable
import Init.Data.Nat.Lemmas

/-!
# The diagonal enumeration of pairs

`Nat × Nat` is countable, and this file proves it by writing the enumeration
down. `diagonalEnum` walks the antidiagonals: it starts at `(0, 0)`, steps
from `(a + 1, b)` to `(a, b + 1)` along a diagonal, and jumps from `(0, b)` to
`(b + 1, 0)` when the diagonal runs out. `triangular` records where each
diagonal begins, and `diagonalEnum_start_and_within` is the pair of facts that
makes the recursion usable -- the walk is at `(s, 0)` at the `s`-th triangular
number, and stays on that diagonal for the following `s` steps.

Defining the enumeration rather than proving abstract existence is what lets
everything downstream be explicit: `productEnum` composes two enumerations with
this one, and the countable unions of `Tautology.Foundation.Cardinal.Union`
flatten a doubly indexed family through the same map.

## Position in the development

Above `Tautology.Foundation.Cardinal.Countable`, and the engine under
`Tautology.Foundation.Cardinal.Union`, `Tautology.Foundation.Cardinal.Sum` and
`Tautology.Foundation.Cardinal.Arithmetic` -- each of which reduces its own
countability claim to this one.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- The `s`-th triangular number `0 + 1 + ... + s`, by recursion. The walk is
at `(s, 0)` exactly at index `triangular s`, and that alignment is what the
whole file runs on. -/
def triangular : Nat -> Nat
  | 0 => 0
  | n + 1 => triangular n + n + 1

/-- The diagonal walk, one step per index: from `(a + 1, b)` to `(a, b + 1)`
along an antidiagonal, and from `(0, b)` to `(b + 1, 0)` onto the next one.
Structural recursion on the index, reading the previous position. -/
def diagonalEnum : Nat -> Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
      match diagonalEnum n with
      | (0, b) => (b + 1, 0)
      | (a + 1, b) => (a, b + 1)

theorem triangular_succ (n : Nat) :
    triangular (n + 1) = triangular n + n + 1 := rfl

/-- The induction that tames the walk: at index `triangular s` it sits at
`(s, 0)`, and for `k <= s` the next `k` steps land at `(s - k, k)`. Every
later use of the walk extracts a position through this pair of facts. -/
theorem diagonalEnum_start_and_within (s : Nat) :
    And
      (diagonalEnum (triangular s) = (s, 0))
      (forall k : Nat,
        k <= s ->
          diagonalEnum (triangular s + k) = (s - k, k)) := by
  induction s with
  | zero =>
      constructor
      · simp [triangular, diagonalEnum]
      · intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        simp [triangular, diagonalEnum]
  | succ s ih =>
      have hend : diagonalEnum (triangular s + s) = (s - s, s) :=
        ih.right s (Nat.le_refl s)
      have hzero : s - s = 0 := by omega
      have hstart :
          diagonalEnum (triangular (s + 1)) = (s + 1, 0) := by
        have htri :
            triangular (s + 1) = (triangular s + s) + 1 := by
          simp [triangular]
        rw [htri]
        change
          (match diagonalEnum (triangular s + s) with
            | (0, b) => (b + 1, 0)
            | (a + 1, b) => (a, b + 1)) =
            (s + 1, 0)
        rw [hend, hzero]
      constructor
      · exact hstart
      · intro k
        induction k with
        | zero =>
            intro _hk
            simpa using hstart
        | succ k ihk =>
            intro hk
            have hkprev : k <= s + 1 := by omega
            have hprev :
                diagonalEnum (triangular (s + 1) + k) =
                  (s + 1 - k, k) :=
              ihk hkprev
            have hstep :
                triangular (s + 1) + (k + 1) =
                  (triangular (s + 1) + k) + 1 := by omega
            have hfirst : s + 1 - k = (s - k) + 1 := by omega
            have htarget : s + 1 - (k + 1) = s - k := by omega
            rw [hstep]
            change
              (match diagonalEnum (triangular (s + 1) + k) with
                | (0, b) => (b + 1, 0)
                | (a + 1, b) => (a, b + 1)) =
                (s + 1 - (k + 1), k + 1)
            rw [hprev, hfirst, htarget]

theorem diagonalEnum_tri_add
    (s k : Nat) (hk : k <= s) :
    diagonalEnum (triangular s + k) = (s - k, k) :=
  (diagonalEnum_start_and_within s).right k hk

/-- The walk read as an enumeration: every index is occupied, so the walk
itself lists all pairs of naturals. -/
def natPairEnum (n : Nat) : Option (Nat × Nat) :=
  some (diagonalEnum n)

/-- Every pair `(a, b)` is reached at the explicit index
`triangular (a + b) + b`, the `b`-th step along the `(a + b)`-th
antidiagonal. -/
theorem enumerable_nat_prod_nat :
    Enumerable (Nat × Nat) := by
  refine Exists.intro natPairEnum ?_
  intro p
  cases p with
  | mk a b =>
      refine Exists.intro (triangular (a + b) + b) ?_
      unfold natPairEnum
      have hb : b <= a + b := by omega
      have hdiag := diagonalEnum_tri_add (a + b) b hb
      rw [hdiag]
      have hfirst : a + b - b = a := by omega
      rw [hfirst]

/-- Two partial enumerations paired through the walk: index `n` offers the
pair sitting at the coordinates of `diagonalEnum n`, and nothing when either
side is `none`. Since each point is offered at some index, every pair is
offered somewhere on some antidiagonal. -/
def productEnum {alpha : Type u} {beta : Type v}
    (ea : Nat -> Option alpha) (eb : Nat -> Option beta) :
    Nat -> Option (alpha × beta) :=
  fun n =>
    let p := diagonalEnum n
    match ea p.fst, eb p.snd with
    | some a, some b => some (a, b)
    | _, _ => none

private theorem exists_productEnum_pair
    {alpha : Type u} {beta : Type v}
    (ea : Nat -> Option alpha) (eb : Nat -> Option beta)
    {a : alpha} {b : beta}
    (ha : Exists (fun i : Nat => ea i = some a))
    (hb : Exists (fun j : Nat => eb j = some b)) :
    Exists (fun n : Nat => productEnum ea eb n = some (a, b)) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨triangular (i + j) + j, ?_⟩
  unfold productEnum
  rw [diagonalEnum_tri_add (i + j) j (by omega)]
  simp [hi, hj]

theorem enumerable_prod
    {alpha : Type u} {beta : Type v}
    (ha : Enumerable alpha) (hb : Enumerable beta) :
    Enumerable (alpha × beta) := by
  cases ha with
  | intro ea hea =>
      cases hb with
      | intro eb heb =>
          refine Exists.intro (productEnum ea eb) ?_
          intro p
          cases p with
          | mk a b =>
              exact exists_productEnum_pair ea eb (hea a) (heb b)

/-- The product of two sets as a predicate on pairs: membership asks both
components and is therefore a conjunction, splitting componentwise. -/
def SetProd {alpha : Type u} {beta : Type v}
    (S : alpha -> Prop) (T : beta -> Prop) : Prod alpha beta -> Prop :=
  fun p => And (S p.fst) (T p.snd)

theorem countableSet_prod
    {alpha : Type u} {beta : Type v}
    {S : alpha -> Prop} {T : beta -> Prop}
    (hS : CountableSet S) (hT : CountableSet T) :
    CountableSet (SetProd S T) := by
  cases hS with
  | intro ea hea =>
      cases hT with
      | intro eb heb =>
          refine Exists.intro (productEnum ea eb) ?_
          intro p hp
          cases p with
          | mk a b =>
              exact exists_productEnum_pair ea eb
                (hea a hp.left) (heb b hp.right)

end Cardinal
end Foundation
end Tautology
