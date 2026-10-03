import Tengoku.Tautology.Tautology.Foundation.Cardinal.Pairing

/-!
# A countable union of countable sets is countable

The proof is the flattening the previous module was built for. A countable
family of countable sets gives a doubly indexed enumeration -- one index
choosing the set, the other choosing the point -- and the diagonal walk of
`Tautology.Foundation.Cardinal.Pairing` turns that into a single index.
`countableUnionEnumFrom` and `indexedUnionEnumFrom` are the two forms of that
composite, for a union indexed by `Nat` and one indexed by an arbitrary
countable type.

`binaryUnionFamily` then handles the finite case by the same machinery rather
than by a separate argument: a union of two sets is presented as a family
indexed by `Nat` that repeats after the first two entries, and
`countableSet_union` falls out.

## The choice this file does not make

Note what is *not* here: no enumeration is chosen for each member of the
family behind the reader's back. The hypothesis is a family of enumerations
already given, so the flattening is a construction rather than an appeal to
countable choice. Where a choice is genuinely needed the caller makes it
before arriving here.

## Position in the development

Above `Tautology.Foundation.Cardinal.Pairing`, below
`Tautology.Foundation.Cardinal.Sum`.

Worth knowing before hunting for consumers: what leaves this file is the
*definition*. `Tautology.RealNegligibility.NullSet` imports this module
directly and keeps `CountableUnion` as a forwarding alias, which is how a null
set comes to be defined by a countable cover at all. The countability theorems
proved here currently have no consumer outside the subtree -- they are the
justification that the definition behaves, not a service anyone calls.

Note also that `IndexedUnion` is declared both here and in
`Tautology.Foundation.SetPred`. The two are unrelated, and a grep for the bare
name will mix them.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- The union of a family of sets indexed by `Nat`: membership is an `Exists`
over the index. -/
def CountableUnion {alpha : Type u}
    (S : Nat -> alpha -> Prop) : alpha -> Prop :=
  fun x => Exists (fun n : Nat => S n x)

/-- The same union for a family indexed by an arbitrary type `iota`. The name
is shared with an unrelated declaration in `Tautology.Foundation.SetPred`, so
references to this one should stay qualified. -/
def IndexedUnion {iota : Type u} {alpha : Type v}
    (S : iota -> alpha -> Prop) : alpha -> Prop :=
  fun x => Exists (fun i : iota => S i x)

/-- A union of two sets dressed up as a `Nat`-indexed family: index `0` is
`S`, every later index is `T`. The binary case can then ride the
countable-union machinery instead of a separate argument. -/
def binaryUnionFamily {alpha : Type u}
    (S T : alpha -> Prop) : Nat -> alpha -> Prop
  | 0 => S
  | _ + 1 => T

/-- A doubly indexed enumeration flattened through the diagonal walk: index
`m` offers whatever `e` offers at the pair `diagonalEnum m`. -/
def countableUnionEnumFrom {alpha : Type u}
    (e : Nat -> Nat -> Option alpha) :
    Nat -> Option alpha :=
  fun m =>
    let p := diagonalEnum m
    e p.fst p.snd

/-- The same flattening with the set index decoded first, from an enumeration
of `iota`; a `none` at the decoding stage offers nothing. -/
def indexedUnionEnumFrom
    {iota : Type u} {alpha : Type v}
    (ei : Nat -> Option iota)
    (e : iota -> Nat -> Option alpha) :
    Nat -> Option alpha :=
  fun m =>
    let p := diagonalEnum m
    match ei p.fst with
    | none => none
    | some i => e i p.snd

/-- A countable union of countable sets is countable: the doubly indexed
enumeration is flattened through the walk. The per-set enumerations are
chosen inside the proof, by `Classical.choose` from the existence
hypotheses. -/
theorem countableSet_countableUnion {alpha : Type u}
    {S : Nat -> alpha -> Prop}
    (hS : forall n : Nat, CountableSet (S n)) :
    CountableSet (CountableUnion S) := by
  classical
  let e : Nat -> Nat -> Option alpha :=
    fun n => Classical.choose (hS n)
  have he :
      forall n : Nat, Enumerates (e n) (S n) := by
    intro n
    exact Classical.choose_spec (hS n)
  refine Exists.intro (countableUnionEnumFrom e) ?_
  intro x hx
  cases hx with
  | intro n hn =>
      cases he n x hn with
      | intro k hk =>
          refine Exists.intro (triangular (n + k) + k) ?_
          unfold countableUnionEnumFrom
          have hk_le : k <= n + k := by omega
          have hdiag := diagonalEnum_tri_add (n + k) k hk_le
          rw [hdiag]
          have hfirst : n + k - k = n := by omega
          rw [hfirst]
          exact hk

/-- The same for a family indexed by any countable type: decode the index
through its enumeration, then flatten exactly as in the `Nat`-indexed case. -/
theorem countableSet_indexedUnion
    {iota : Type u} {alpha : Type v}
    {S : iota -> alpha -> Prop}
    (hi : Enumerable iota)
    (hS : forall i : iota, CountableSet (S i)) :
    CountableSet (IndexedUnion S) := by
  classical
  cases hi with
  | intro ei hei =>
      let e : iota -> Nat -> Option alpha :=
        fun i => Classical.choose (hS i)
      have he :
          forall i : iota, Enumerates (e i) (S i) := by
        intro i
        exact Classical.choose_spec (hS i)
      refine Exists.intro (indexedUnionEnumFrom ei e) ?_
      intro x hx
      cases hx with
      | intro i hiS =>
          cases hei i with
          | intro r hr =>
              cases he i x hiS with
              | intro k hk =>
                  refine Exists.intro (triangular (r + k) + k) ?_
                  unfold indexedUnionEnumFrom
                  have hk_le : k <= r + k := by omega
                  have hdiag := diagonalEnum_tri_add (r + k) k hk_le
                  rw [hdiag]
                  have hfirst : r + k - k = r := by omega
                  rw [hfirst]
                  simp [hr, hk]

theorem binaryUnionFamily_countable
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : CountableSet S) (hT : CountableSet T) :
    forall n : Nat, CountableSet (binaryUnionFamily S T n) := by
  intro n
  cases n with
  | zero => exact hS
  | succ _ => exact hT

theorem binaryUnionFamily_covers
    {alpha : Type u} {S T : alpha -> Prop}
    {x : alpha}
    (h : SetUnion S T x) :
    CountableUnion (binaryUnionFamily S T) x := by
  cases h with
  | inl hx =>
      exact Exists.intro 0 hx
  | inr hx =>
      exact Exists.intro 1 hx

theorem countableSet_union
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : CountableSet S) (hT : CountableSet T) :
    CountableSet (SetUnion S T) := by
  have hUnion :
      CountableSet (CountableUnion (binaryUnionFamily S T)) :=
    countableSet_countableUnion (binaryUnionFamily_countable hS hT)
  exact countableSet_mono hUnion
    (fun _ hx => binaryUnionFamily_covers hx)

theorem countableSet_union_left
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : CountableSet S) (hT : ListFinite T) :
    CountableSet (SetUnion S T) :=
  countableSet_union hS (countableSet_of_listFinite hT)

theorem countableSet_union_right
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : ListFinite S) (hT : CountableSet T) :
    CountableSet (SetUnion S T) :=
  countableSet_union (countableSet_of_listFinite hS) hT

end Cardinal
end Foundation
end Tautology
