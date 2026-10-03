import Tengoku.Tautology.Tautology.Foundation.Cardinal.Finite

/-!
# Countability, by partial enumerations

An enumeration here is a map `Nat -> Option alpha`, not `Nat -> alpha`, and
that choice runs through the whole file. Allowing `none` means the empty type
and every finite set are enumerable without special pleading, a set may be
listed with gaps and repetitions, and no nonemptiness hypothesis has to be
carried around. `Enumerates e S` asks only that every element of `S` be hit
somewhere; nothing is claimed about what `e` does elsewhere, so an enumeration
of a subset never has to be trimmed.

On that base sit `CountableSet`, `AtMostCountable`, `CountablyInfinite` (at
most countable and infinite, in the list sense of
`Tautology.Foundation.Cardinal.Finite`), and the negations `Uncountable` and
`UncountableSet`.

## The interface uncountability is proved through

`uncountable_of_every_option_enum_misses` says that if every candidate
enumeration misses some element then the type is uncountable, and its set
counterpart says the same for a subset. This is the shape a diagonal argument
naturally produces -- given an enumeration, construct a missed point -- so it
is what `Tautology.Foundation.Cardinal.Cantor` and the real-number
uncountability proof in `RealCardinality` both go through. Proving
`Not Enumerable` directly is never necessary.

## Position in the development

Above `Tautology.Foundation.Cardinal.Finite`, and the base for
`Tautology.Foundation.Cardinal.Pairing`, which makes products countable, and
for `Tautology.Foundation.Cardinal.Cantor`. Outside the subtree,
`Tautology.RealBootstrap.InternalCountable` uses it for countability of the
internal rationals -- that module was moved down into `RealBootstrap` during
the batch 3 restructuring precisely because it needs nothing above this level.

## Role

Implementation.
-/

namespace Tautology
namespace Foundation
namespace Cardinal

/-- Push a map through an option: `none` passes through untouched and
`some x` becomes `some (f x)`. Composing an enumeration with `OptionMap f` is
how enumerability travels along `f`. -/
def OptionMap {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) : Option alpha -> Option beta
  | none => none
  | some x => some (f x)

/-- `e` reaches every point of `S` at some index. No condition is imposed
elsewhere, so gaps and repetitions are free and an enumeration of a subset
never has to be trimmed. -/
def Enumerates {alpha : Type u}
    (e : Nat -> Option alpha) (S : alpha -> Prop) : Prop :=
  forall x : alpha, S x -> Exists (fun n : Nat => e n = some x)

/-- A type is enumerable when one partial enumeration reaches all of its
points; this is `CountableSet` of the always-true predicate, spelled out. -/
def Enumerable (alpha : Type u) : Prop :=
  Exists (fun e : Nat -> Option alpha =>
    forall x : alpha, Exists (fun n : Nat => e n = some x))

/-- A set is countable when some partial enumeration reaches all of its
points. Equivalent to enumerability of the subtype, by
`enumerable_subtype_of_countableSet` and its converse. -/
def CountableSet {alpha : Type u} (S : alpha -> Prop) : Prop :=
  Exists (fun e : Nat -> Option alpha => Enumerates e S)

/-- A second reading of `Enumerable`, named to sit beside
`CountablyInfinite`; it is the same predicate, not a weaker one. -/
def AtMostCountable (alpha : Type u) : Prop :=
  Enumerable alpha

/-- The matching second reading of `CountableSet` for sets. -/
def AtMostCountableSet {alpha : Type u} (S : alpha -> Prop) : Prop :=
  CountableSet S

/-- Exactly countable: enumerable, and infinite in the list sense of
`Tautology.Foundation.Cardinal.Finite`. -/
def CountablyInfinite (alpha : Type u) : Prop :=
  And (AtMostCountable alpha) (ListInfiniteType alpha)

/-- Exactly countable as a set: a partial enumeration of `S`, and every list
misses a point of `S`. -/
def CountablyInfiniteSet {alpha : Type u} (S : alpha -> Prop) : Prop :=
  And (AtMostCountableSet S) (ListInfinite S)

/-- The direct image as a predicate: `y` belongs when it is the value of some
point of `S`, with the equation oriented `y = f x`. -/
def Image {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (S : alpha -> Prop) : beta -> Prop :=
  fun y => Exists (fun x : alpha => And (S x) (y = f x))

/-- The bare negation of enumerability. Proofs do not handle this directly:
they enter through `uncountable_of_every_option_enum_misses`. -/
def Uncountable (alpha : Type u) : Prop :=
  Not (Enumerable alpha)

/-- The set form: no partial enumeration reaches all of `S`. Diagonal
arguments enter through `uncountableSet_of_every_option_enum_misses`. -/
def UncountableSet {alpha : Type u} (S : alpha -> Prop) : Prop :=
  Not (CountableSet S)

/-- Uncountability checked by missed points: if every candidate enumeration
misses some point, no enumeration exists. A diagonal argument produces
exactly this hypothesis, which is why the uncountability results all enter
here. -/
theorem uncountable_of_every_option_enum_misses
    {alpha : Type u}
    (h :
      forall e : Nat -> Option alpha,
        Exists (fun x : alpha =>
          forall n : Nat, Not (e n = some x))) :
    Uncountable alpha := by
  intro henum
  cases henum with
  | intro e he =>
      cases h e with
      | intro x hx =>
          cases he x with
          | intro n hn =>
              exact hx n hn

/-- The same entry point for a set, with the missed point required to belong
to `S` itself. -/
theorem uncountableSet_of_every_option_enum_misses
    {alpha : Type u} {S : alpha -> Prop}
    (h :
      forall e : Nat -> Option alpha,
        Exists (fun x : alpha =>
          And (S x) (forall n : Nat, Not (e n = some x)))) :
    UncountableSet S := by
  intro henum
  cases henum with
  | intro e he =>
      cases h e with
      | intro x hx =>
          cases he x hx.left with
          | intro n hn =>
              exact hx.right n hn

/-- A list read as an enumeration: the head at index `0`, the tail shifted by
one, and `none` past the end. -/
def listEnum {alpha : Type u} : List alpha -> Nat -> Option alpha
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listEnum xs n

/-- An ambient enumeration filtered to the subtype: a hit `some x` survives
as a subtype element when `S x` holds and becomes `none` otherwise. Deciding
`S x` is what makes this `noncomputable`. -/
noncomputable def subtypeEnumOfAmbientEnum
    {alpha : Type u}
    (S : alpha -> Prop)
    (e : Nat -> Option alpha) :
    Nat -> Option {x : alpha // S x} := by
  classical
  exact fun n =>
    match e n with
    | none => none
    | some x =>
        if hx : S x then
          some ({ val := x, property := hx } : {x : alpha // S x})
        else
          none

theorem listEnum_mem {alpha : Type u} {x : alpha} :
    forall xs : List alpha,
      List.Mem x xs ->
        Exists (fun n : Nat => listEnum xs n = some x)
  | [], h => nomatch h
  | y :: ys, h => by
      cases h with
      | head =>
          exact Exists.intro 0 rfl
      | tail _ htail =>
          cases listEnum_mem ys htail with
          | intro n hn =>
              exact Exists.intro (n + 1) hn

theorem enumerable_of_listFiniteType
    {alpha : Type u}
    (h : ListFiniteType alpha) :
    Enumerable alpha := by
  cases h with
  | intro xs hxs =>
      exact Exists.intro (listEnum xs)
        (fun x => listEnum_mem xs (hxs x))

theorem countableSet_of_listFinite
    {alpha : Type u} {S : alpha -> Prop}
    (h : ListFinite S) :
    CountableSet S := by
  cases h with
  | intro xs hxs =>
      refine Exists.intro (listEnum xs) ?_
      intro x hx
      exact listEnum_mem xs (hxs x hx)

theorem countableSet_singleton {alpha : Type u} (a : alpha) :
    CountableSet (SingletonSet a) :=
  countableSet_of_listFinite (listFinite_singleton a)

theorem countableSet_empty {alpha : Type u} :
    CountableSet (fun _ : alpha => False) :=
  Exists.intro (fun _ : Nat => none)
    (fun _ h => False.elim h)

theorem enumerable_nat : Enumerable Nat :=
  Exists.intro (fun n : Nat => some n)
    (fun n => Exists.intro n rfl)

theorem atMostCountable_nat : AtMostCountable Nat :=
  enumerable_nat

theorem countablyInfinite_nat : CountablyInfinite Nat :=
  And.intro atMostCountable_nat listInfiniteType_nat

/-- Witnessed by the enumeration that is `none` everywhere; an empty type is
enumerable precisely because `none` is allowed. -/
theorem enumerable_empty :
    Enumerable Empty := by
  exact Exists.intro (fun _ : Nat => none)
    (fun x => Empty.elim x)

/-- The constant enumeration hits the only point at index `0`, the finite
case at its smallest. -/
theorem enumerable_punit :
    Enumerable PUnit := by
  exact Exists.intro (fun _ : Nat => some PUnit.unit)
    (fun x => by cases x; exact Exists.intro 0 rfl)

theorem enumerable_of_surjective
    {alpha : Type u} {beta : Type v}
    (h : Enumerable alpha)
    {f : alpha -> beta}
    (hf : Surjective f) :
    Enumerable beta := by
  cases h with
  | intro e he =>
      refine Exists.intro (fun n : Nat => OptionMap f (e n)) ?_
      intro y
      cases hf y with
      | intro x hx =>
          cases he x with
          | intro n hn =>
              refine Exists.intro n ?_
              change OptionMap f (e n) = some y
              simp [OptionMap, hn, hx]

theorem enumerable_of_cardGE_nat
    {alpha : Type u}
    (h : CardGE Nat alpha) :
    Enumerable alpha := by
  cases h with
  | intro f hf =>
      exact enumerable_of_surjective enumerable_nat hf

/-- The enumeration read off an injection into `Nat`: index `n` offers the
point that maps to `n`, located by choice, or `none` when no point does. -/
noncomputable def inverseNatEnumOfInjection
    {alpha : Type u}
    (f : alpha -> Nat) : Nat -> Option alpha := by
  classical
  exact fun n =>
    if h : Exists (fun x : alpha => f x = n) then
      some (Classical.choose h)
    else
      none

/-- At the index `f x` the chosen point is `x` itself. Injectivity is what
the proof uses: it makes the preimage unique, so the choice cannot disagree. -/
theorem inverseNatEnumOfInjection_spec
    {alpha : Type u}
    {f : alpha -> Nat}
    (hf : Injective f) (x : alpha) :
    inverseNatEnumOfInjection f (f x) = some x := by
  classical
  unfold inverseNatEnumOfInjection
  have hmem : Exists (fun y : alpha => f y = f x) :=
    Exists.intro x rfl
  simp [hmem, hf (Classical.choose_spec hmem)]

theorem enumerable_of_cardLE_nat
    {alpha : Type u}
    (h : CardLE alpha Nat) :
    Enumerable alpha := by
  cases h with
  | intro f hf =>
      refine Exists.intro (inverseNatEnumOfInjection f) ?_
      intro x
      exact Exists.intro (f x)
        (inverseNatEnumOfInjection_spec hf x)

/-- A partial enumeration made total: `none` is replaced by one fixed point
of `alpha`, supplied by `[Nonempty alpha]`. This is the bridge from
enumerability to a surjection from `Nat`. -/
noncomputable def totalEnumOfOptionEnum
    {alpha : Type u}
    [Nonempty alpha]
    (e : Nat -> Option alpha) : Nat -> alpha := by
  classical
  exact fun n =>
    match e n with
    | some x => x
    | none => Classical.choice inferInstance

/-- Where the partial enumeration is defined, the filled one returns the same
point; the fixed point appears only on `none`. -/
theorem totalEnumOfOptionEnum_spec
    {alpha : Type u}
    [Nonempty alpha]
    {e : Nat -> Option alpha}
    {n : Nat} {x : alpha}
    (h : e n = some x) :
    totalEnumOfOptionEnum e n = x := by
  classical
  unfold totalEnumOfOptionEnum
  rw [h]

theorem cardGE_nat_of_enumerable
    {alpha : Type u}
    [Nonempty alpha]
    (h : Enumerable alpha) :
    CardGE Nat alpha := by
  cases h with
  | intro e he =>
      refine Exists.intro (totalEnumOfOptionEnum e) ?_
      intro x
      cases he x with
      | intro n hn =>
          exact Exists.intro n (totalEnumOfOptionEnum_spec hn)

theorem enumerable_subtype_of_enumerable
    {alpha : Type u}
    (h : Enumerable alpha)
    (S : alpha -> Prop) :
    CountableSet S := by
  cases h with
  | intro e he =>
      exact Exists.intro e (fun x _ => he x)

theorem countableSet_of_enumerable_subtype
    {alpha : Type u} {S : alpha -> Prop}
    (h : Enumerable {x : alpha // S x}) :
    CountableSet S := by
  cases h with
  | intro e he =>
      refine Exists.intro (fun n => OptionMap Subtype.val (e n)) ?_
      intro x hx
      cases he ({ val := x, property := hx } : {x : alpha // S x}) with
      | intro n hn =>
          refine Exists.intro n ?_
          change OptionMap Subtype.val (e n) = some x
          simp [OptionMap, hn]

/-- The direction of the subtype bridge that costs something: enumerating the
subtype needs the ambient enumeration filtered through the predicate,
`subtypeEnumOfAmbientEnum`, and that filtering is a choice. -/
theorem enumerable_subtype_of_countableSet
    {alpha : Type u} {S : alpha -> Prop}
    (h : CountableSet S) :
    Enumerable {x : alpha // S x} := by
  classical
  cases h with
  | intro e he =>
      refine Exists.intro (subtypeEnumOfAmbientEnum S e) ?_
      intro x
      cases x with
      | mk val property =>
          cases he val property with
          | intro n hn =>
              refine Exists.intro n ?_
              unfold subtypeEnumOfAmbientEnum
              rw [hn]
              simp [property]

theorem countableSet_of_subtype_cardLE_nat
    {alpha : Type u} {S : alpha -> Prop}
    (h : CardLE {x : alpha // S x} Nat) :
    CountableSet S :=
  countableSet_of_enumerable_subtype (enumerable_of_cardLE_nat h)

theorem countableSet_univ_of_enumerable
    {alpha : Type u}
    (h : Enumerable alpha) :
    CountableSet (fun _ : alpha => True) := by
  cases h with
  | intro e he =>
      exact Exists.intro e (fun x _ => he x)

theorem enumerable_of_countableSet_univ
    {alpha : Type u}
    (h : CountableSet (fun _ : alpha => True)) :
    Enumerable alpha := by
  cases h with
  | intro e he =>
      exact Exists.intro e (fun x => he x True.intro)

theorem countableSet_mono
    {alpha : Type u} {S T : alpha -> Prop}
    (hT : CountableSet T)
    (hST : forall x : alpha, S x -> T x) :
    CountableSet S := by
  cases hT with
  | intro e he =>
      exact Exists.intro e (fun x hx => he x (hST x hx))

/-- The engine of `countableSet_of_injective_code`: scan an enumeration of
the code set and, for each code hit, return the `S`-point carrying it,
located by choice. -/
noncomputable def preimageEnumOfCountableCode
    {alpha beta : Type}
    (S : alpha -> Prop)
    (code : alpha -> beta)
    (e : Nat -> Option beta) : Nat -> Option alpha := by
  classical
  exact fun n =>
    match e n with
    | none => none
    | some q =>
        if h : Exists (fun x : alpha => And (S x) (code x = q)) then
          some (Classical.choose h)
        else
          none

/-- Countability transports along an injective code: if the points of `S`
code into a countable `T` with distinct points getting distinct codes, then
`S` is countable. The proof scans an enumeration of the codes and decodes
each hit through the injection. -/
theorem countableSet_of_injective_code
    {alpha beta : Type}
    {S : alpha -> Prop} {T : beta -> Prop}
    {code : alpha -> beta}
    (hT : CountableSet T)
    (hmap : forall x : alpha, S x -> T (code x))
    (hinj :
      forall x y : alpha,
        S x -> S y -> code x = code y -> x = y) :
    CountableSet S := by
  classical
  cases hT with
  | intro e he =>
      refine Exists.intro (preimageEnumOfCountableCode S code e) ?_
      intro x hx
      cases he (code x) (hmap x hx) with
      | intro n hn =>
          refine Exists.intro n ?_
          unfold preimageEnumOfCountableCode
          rw [hn]
          let hex :
              Exists
                (fun y : alpha => And (S y) (code y = code x)) :=
            Exists.intro x (And.intro hx rfl)
          change
            (if h : Exists
                (fun y : alpha => And (S y) (code y = code x)) then
              some (Classical.choose h)
            else
              none) = some x
          by_cases h :
              Exists
                (fun y : alpha => And (S y) (code y = code x))
          · have hchoose := Classical.choose_spec h
            have hchosen_eq :
                Classical.choose h = x :=
              hinj (Classical.choose h) x
                hchoose.left hx hchoose.right
            simp [h, hchosen_eq]
          · exact False.elim (h hex)

theorem countableSet_inter_left
    {alpha : Type u} {S T : alpha -> Prop}
    (hS : CountableSet S) :
    CountableSet (SetInter S T) :=
  countableSet_mono hS (fun _ hx => hx.left)

theorem countableSet_inter_right
    {alpha : Type u} {S T : alpha -> Prop}
    (hT : CountableSet T) :
    CountableSet (SetInter S T) :=
  countableSet_mono hT (fun _ hx => hx.right)

theorem countableSet_image
    {alpha : Type u} {beta : Type v}
    {S : alpha -> Prop}
    (hS : CountableSet S)
    (f : alpha -> beta) :
    CountableSet (Image f S) := by
  cases hS with
  | intro e he =>
      refine Exists.intro (fun n => OptionMap f (e n)) ?_
      intro y hy
      cases hy with
      | intro x hx =>
          cases he x hx.left with
          | intro n hn =>
              refine Exists.intro n ?_
              change OptionMap f (e n) = some y
              simp [OptionMap, hn, hx.right]

theorem countableSet_image_of_enumerable
    {alpha : Type u} {beta : Type v}
    (h : Enumerable alpha)
    (f : alpha -> beta) :
    CountableSet (Image f (fun _ : alpha => True)) :=
  countableSet_image (countableSet_univ_of_enumerable h) f

end Cardinal
end Foundation
end Tautology
