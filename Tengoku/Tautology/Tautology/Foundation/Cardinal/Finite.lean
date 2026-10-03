import Tengoku.Tautology.Tautology.Foundation.Cardinal.Maps
import Init.Data.Nat.Lemmas

/-!
# Two notions of finiteness, and the bridges between them

`ListFinite S` says some list contains every element of `S`; `DedekindFinite
alpha` says no injection of the type into itself misses a point. They are
different definitions with different uses, and the file keeps both rather than
picking one: the list form is what a covering or partition argument produces
naturally, while the Dedekind form is the one that survives having no
decidable equality.

The corresponding infinitude predicates are stated positively rather than as
negations. `ListInfinite S` says that *for every* list some element of `S`
escapes it, which is a usable witness-producing statement, whereas
`Not (ListFinite S)` is not. The two are of course equivalent, and
`listInfinite_iff_not_listFinite` is that bridge -- one of several in the
second half of the file, all serving to let an argument phrase itself in
whichever form is convenient and cross over when it must.

## `natListBound`, the trick the file turns on

To show `Nat` is infinite one must exhibit, for an arbitrary list of naturals,
a natural not on it. `natListBound` walks the list and returns a number
strictly larger than everything in it, by summing the entries and adding one.
That is all `listInfiniteType_nat` needs, and it avoids any appeal to
decidable membership or to sorting. `dedekindInfinite_nat` covers the same
ground in the other notion, via the successor map, which is injective and
misses zero.

## Position in the development

Above `Tautology.Foundation.Cardinal.Maps` and below
`Tautology.Foundation.Cardinal.Countable`, which builds enumerability on top of
these predicates.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- Inclusion of predicates: every point satisfying `S` satisfies `T`. This is
the subset relation of the predicate-as-set representation, and it stays
weaker than equality of the predicates. -/
def SetSubset {alpha : Type u} (S T : alpha -> Prop) : Prop :=
  forall x : alpha, S x -> T x

/-- The singleton of `a`, as the predicate `x = a` with `x` on the left, so
that a membership hypothesis rewrites by `rw` directly. -/
def SingletonSet {alpha : Type u} (a : alpha) : alpha -> Prop :=
  fun x => x = a

/-- Union as a disjunction of the predicates: membership splits into the two
sides by `cases`. -/
def SetUnion {alpha : Type u} (S T : alpha -> Prop) : alpha -> Prop :=
  fun x => Or (S x) (T x)

/-- Intersection as a conjunction of the predicates: membership carries both
components. -/
def SetInter {alpha : Type u} (S T : alpha -> Prop) : alpha -> Prop :=
  fun x => And (S x) (T x)

/-- Every point of `S` appears on the list. The list may repeat entries and
carry points outside `S`: this is coverage, not an exact enumeration. -/
def ListedBy {alpha : Type u} (xs : List alpha) (S : alpha -> Prop) : Prop :=
  forall x : alpha, S x -> List.Mem x xs

/-- Finiteness in the list form: some list covers `S`. Kept alongside the
Dedekind form because covering arguments produce a list directly. -/
def ListFinite {alpha : Type u} (S : alpha -> Prop) : Prop :=
  Exists (fun xs : List alpha => ListedBy xs S)

/-- Infinitude with a witness: every list misses some point of `S`. This is
the usable form, rather than the negation of `ListFinite`, and the two are
bridged by `listInfinite_iff_not_listFinite`. -/
def ListInfinite {alpha : Type u} (S : alpha -> Prop) : Prop :=
  forall xs : List alpha,
    Exists (fun x : alpha => And (S x) (Not (List.Mem x xs)))

/-- The type-level form of `ListFinite`: one list contains every point of
`alpha`. -/
def ListFiniteType (alpha : Type u) : Prop :=
  Exists (fun xs : List alpha => forall x : alpha, List.Mem x xs)

/-- The type-level form of `ListInfinite`: every list of points of `alpha`
misses a point. -/
def ListInfiniteType (alpha : Type u) : Prop :=
  forall xs : List alpha, Exists (fun x : alpha => Not (List.Mem x xs))

/-- Dedekind infinitude: some injective self-map of `alpha` that is not onto.
No decidability is involved anywhere in this notion. -/
def DedekindInfinite (alpha : Type u) : Prop :=
  Exists (fun f : alpha -> alpha =>
    And (Injective f) (Not (Surjective f)))

/-- The negation of `DedekindInfinite`: every injective self-map of `alpha`
is onto. -/
def DedekindFinite (alpha : Type u) : Prop :=
  Not (DedekindInfinite alpha)

/-- Infinitude of a set, read as infinitude of its subtype: the injective
non-surjective self-map lives on `{x : alpha // S x}`, not on `alpha`. -/
def DedekindInfiniteSet {alpha : Type u} (S : alpha -> Prop) : Prop :=
  DedekindInfinite {x : alpha // S x}

/-- Finiteness of a set in the same reading: the subtype `{x : alpha // S x}`
is Dedekind finite. -/
def DedekindFiniteSet {alpha : Type u} (S : alpha -> Prop) : Prop :=
  DedekindFinite {x : alpha // S x}

/-- A natural number strictly above every entry of the list: the head plus
the bound of the tail plus one, by recursion down the list. No appeal to
decidable membership or to sorting is needed. -/
def natListBound : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natListBound xs + 1

/-- Every entry of the list lies strictly below the bound. The proof is the
recursion that `natListBound` is, with `omega` closing each step. -/
theorem mem_lt_natListBound {n : Nat} :
    forall xs : List Nat,
      List.Mem n xs -> n < natListBound xs
  | [], h => nomatch h
  | x :: xs, h => by
      cases h with
      | head =>
          dsimp [natListBound]
          omega
      | tail _ htail =>
          have hlt := mem_lt_natListBound xs htail
          dsimp [natListBound]
          omega

/-- The first infinitude fact of the library: `Nat` has a point beyond any
list, witnessed by `natListBound xs`, which cannot lie on `xs` without being
strictly below itself. -/
theorem listInfiniteType_nat :
    ListInfiniteType Nat := by
  intro xs
  refine Exists.intro (natListBound xs) ?_
  intro hmem
  have hlt := mem_lt_natListBound xs hmem
  exact (Nat.lt_irrefl (natListBound xs)) hlt

theorem nat_succ_injective :
    Injective Nat.succ := by
  intro x y h
  exact Nat.succ.inj h

theorem nat_succ_not_surjective :
    Not (Surjective Nat.succ) := by
  intro hsurj
  cases hsurj 0 with
  | intro n hn =>
      cases n <;> cases hn

/-- `Nat` is infinite in the Dedekind sense too, witnessed by successor:
injective, and it misses `0`. The two notions of infinitude thus both hold
here, though the file proves no equivalence between them in general. -/
theorem dedekindInfinite_nat :
    DedekindInfinite Nat :=
  Exists.intro Nat.succ
    (And.intro nat_succ_injective nat_succ_not_surjective)

theorem listFinite_empty {alpha : Type u} :
    ListFinite (fun _ : alpha => False) :=
  Exists.intro [] (fun _ h => False.elim h)

theorem listFinite_singleton {alpha : Type u} (a : alpha) :
    ListFinite (SingletonSet a) := by
  refine Exists.intro [a] ?_
  intro x hx
  rw [hx]
  exact List.Mem.head []

theorem listFinite_mono
    {alpha : Type u} {S T : alpha -> Prop}
    (hT : ListFinite T)
    (hST : SetSubset S T) :
    ListFinite S := by
  cases hT with
  | intro xs hxs =>
      exact Exists.intro xs (fun x hx => hxs x (hST x hx))

theorem listFinite_union
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : ListFinite S) (hT : ListFinite T) :
    ListFinite (SetUnion S T) := by
  cases hS with
  | intro xs hxs =>
      cases hT with
      | intro ys hys =>
          refine Exists.intro (xs ++ ys) ?_
          intro x hx
          cases hx with
          | inl hxS =>
              exact List.mem_append_left ys (hxs x hxS)
          | inr hxT =>
              exact List.mem_append_right xs (hys x hxT)

theorem listFinite_inter_left
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : ListFinite S) :
    ListFinite (SetInter S T) :=
  listFinite_mono hS (fun _ hx => hx.left)

theorem listFinite_inter_right
    {alpha : Type u} {S T : alpha -> Prop}
    (hT : ListFinite T) :
    ListFinite (SetInter S T) :=
  listFinite_mono hT (fun _ hx => hx.right)

theorem listFinite_univ_iff_listFiniteType {alpha : Type u} :
    ListFinite (fun _ : alpha => True) <-> ListFiniteType alpha := by
  constructor
  · intro h
    cases h with
    | intro xs hxs =>
        exact Exists.intro xs (fun x => hxs x True.intro)
  · intro h
    cases h with
    | intro xs hxs =>
        exact Exists.intro xs (fun x _ => hxs x)

theorem listInfinite_univ_iff_listInfiniteType {alpha : Type u} :
    ListInfinite (fun _ : alpha => True) <-> ListInfiniteType alpha := by
  constructor
  · intro h xs
    cases h xs with
    | intro x hx =>
        exact Exists.intro x hx.right
  · intro h xs
    cases h xs with
    | intro x hx =>
        exact Exists.intro x (And.intro True.intro hx)

/-- The passage from the negation to the witness form, and the one genuinely
classical step in this bridge: either some point of `S` escapes the given
list, or every point lies on it and that list is a `ListFinite` witness. -/
theorem listInfinite_of_not_listFinite
    {alpha : Type u} {S : alpha -> Prop}
    (h : Not (ListFinite S)) :
    ListInfinite S := by
  classical
  intro xs
  by_cases hxs : Exists (fun x : alpha => And (S x) (Not (List.Mem x xs)))
  · exact hxs
  · have hcover : ListedBy xs S := by
      intro x hxS
      by_cases hmem : List.Mem x xs
      · exact hmem
      · exact False.elim (hxs (Exists.intro x (And.intro hxS hmem)))
    exact False.elim (h (Exists.intro xs hcover))

theorem not_listFinite_of_listInfinite
    {alpha : Type u} {S : alpha -> Prop}
    (h : ListInfinite S) :
    Not (ListFinite S) := by
  intro hfin
  cases hfin with
  | intro xs hxs =>
      cases h xs with
      | intro x hx =>
          exact hx.right (hxs x hx.left)

/-- The bridge between the two infinitude forms, matching `ListInfinite`
with the negation of `ListFinite`. One direction is immediate; the other is
the classical argument above. -/
theorem listInfinite_iff_not_listFinite
    {alpha : Type u} {S : alpha -> Prop} :
    ListInfinite S <-> Not (ListFinite S) :=
  Iff.intro
    not_listFinite_of_listInfinite
    listInfinite_of_not_listFinite

theorem not_listFiniteType_of_listInfiniteType
    {alpha : Type u}
    (h : ListInfiniteType alpha) :
    Not (ListFiniteType alpha) := by
  intro hfin
  have hInf : ListInfinite (fun _ : alpha => True) :=
    (listInfinite_univ_iff_listInfiniteType).mpr h
  have hFin : ListFinite (fun _ : alpha => True) :=
    (listFinite_univ_iff_listFiniteType).mpr hfin
  exact (not_listFinite_of_listInfinite hInf) hFin

theorem listInfiniteType_of_not_listFiniteType
    {alpha : Type u}
    (h : Not (ListFiniteType alpha)) :
    ListInfiniteType alpha := by
  have hnot : Not (ListFinite (fun _ : alpha => True)) := by
    intro hfin
    exact h ((listFinite_univ_iff_listFiniteType).mp hfin)
  exact (listInfinite_univ_iff_listInfiniteType).mp
    (listInfinite_of_not_listFinite hnot)

theorem listInfiniteType_iff_not_listFiniteType
    {alpha : Type u} :
    ListInfiniteType alpha <-> Not (ListFiniteType alpha) :=
  Iff.intro
    not_listFiniteType_of_listInfiniteType
    listInfiniteType_of_not_listFiniteType

theorem not_listFiniteType_nat :
    Not (ListFiniteType Nat) :=
  not_listFiniteType_of_listInfiniteType listInfiniteType_nat

end Cardinal
end Foundation
end Tautology
