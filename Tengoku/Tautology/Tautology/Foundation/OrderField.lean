module

public import Init

/-!
# Bundled structures instead of typeclasses

The axioms, and the idiom the whole library is written in.

`IsOrderedFieldBaseLike` is an ordinary structure holding the operations of an
ordered field together with its axioms;
`IsDedekindCompleteOrderedFieldBaseLike` pairs one with a completeness field.
There is no `class` here and none anywhere in this library above the backend:
abstraction is carried by **passing a bundle as an explicit argument**, in the
shape `(F : IsOrderedFieldBaseLike alpha)`, and the derived theory is developed
in `namespace IsOrderedFieldBaseLike` so that it reads as `F.add_comm`,
`F.le_trans`, and so on.

## Why, and what it costs

The project's thesis is that mathematics is a collection of small worlds each
with its own conventions, joined by explicit interfaces rather than by one
global convention. Typeclasses assume the opposite -- a single coherent
assignment of structure to type, resolved by search. Writing the bundles out by
hand keeps every use of an axiom visible in the term, and keeps two different
ordered-field structures on the same carrier from ever being confused.

The cost is real and shows up everywhere above: every definition carries an `F`
or a `C`, hypotheses are threaded by hand, and the derived theorems in
`namespace IsOrderedFieldBaseLike` are not "misfiled" -- that namespace *is*
where results about a bundle belong. A reader who expects instance resolution
will find explicit arguments instead; that is the design, not an omission.

Note also the two-level split. A statement that needs only the ordered-field
axioms lives under `IsOrderedFieldBaseLike`; one that needs completeness lives
under `IsDedekindCompleteOrderedFieldBaseLike` and takes `C`, reaching the
field through `C.field`. Throughout the library that namespace switch is the
marker for "completeness is used here", and it is worth reading as such.

## Why this file is declared `module` when its neighbours are not

It uses the Lean 4 module system -- `module`, `public import`, `public def` --
and so has to mark its declarations public explicitly. That is unusual here: of
the 67 files in the library declaring `module`, 65 are the sealed backend
subtree under `RealBasic/ModuleBackend/`, and the only two outside it are this
file and `Tautology.Nat.Least`. The other fourteen modules of `Foundation` are
ordinary.

The reason is mechanical rather than architectural. A `module` may only
`public import` another `module`, and the sealed backends -- which must reach
`IsDedekindCompleteOrderedFieldBaseLike` in order to prove anything -- need
this file. So it had to be declared that way for them to use it at all. No
sealing of this file's own contents is intended or achieved; everything in it
is public.

## Position and role

Foundation module, and the base of the entire development: everything in
`RealBootstrap` and above is stated over these two structures. Its direct
consumers are `Tautology.RealBootstrap.Base`, `Tautology.RealBasic.ValveRoom`,
and three modules of the backend subtree -- `ModuleBackend.Interface`,
`ModuleBackend.Cauchy.Field` and `ModuleBackend.Eudoxus.Order`. The words this
header uses in a sense particular to this library -- region, route, waist,
valve, facade, and the three kinds of aggregation module -- are each defined
once, in the header of the root module `Tautology`. This region has no umbrella
to carry that pointer, so the modules that use the vocabulary carry it
themselves.

-/

namespace Tautology

/-- `u` bounds `S` above: every point of `S` is at most `u`, under the
relation passed in explicitly rather than through notation. -/
public def IsUpperBound {alpha : Type} (le : alpha -> alpha -> Prop)
    (S : alpha -> Prop) (u : alpha) : Prop :=
  forall x, S x -> le x u

/-- A least upper bound of `S`: an upper bound that every upper bound of `S`
lies above. The two conjuncts are an exhibit and a comparison, the shape a
completeness proof produces. -/
public def IsLeastUpperBound {alpha : Type} (le : alpha -> alpha -> Prop)
    (S : alpha -> Prop) (s : alpha) : Prop :=
  And (IsUpperBound le S s) (forall u, IsUpperBound le S u -> le s u)

/-- A linear order as a bundle: the relation together with reflexivity,
transitivity, antisymmetry and totality as ordinary fields. -/
public structure IsLinearOrderLike (alpha : Type) where
  le : alpha -> alpha -> Prop
  refl : forall x, le x x
  trans : forall {x y z}, le x y -> le y z -> le x z
  antisymm : forall {x y}, le x y -> le y x -> x = y
  total : forall x y, Or (le x y) (le y x)

/-- Dedekind completeness of a relation: every inhabited set with some upper
bound has a least upper bound. Inhabitation and boundedness are both demanded,
since an empty or unbounded set has no supremum to exhibit. -/
public structure IsDedekindComplete (alpha : Type)
    (le : alpha -> alpha -> Prop) where
  exists_lub :
    forall S : alpha -> Prop,
      Exists S ->
      Exists (IsUpperBound le S) ->
      Exists (fun s => IsLeastUpperBound le S s)

/-- A complete linear order: a linear-order bundle paired with completeness
of its own relation. It packages the order-theoretic half on its own, with no
field structure in play. -/
public structure IsDedekindCompleteLinearOrderLike (alpha : Type) where
  order : IsLinearOrderLike alpha
  complete : IsDedekindComplete alpha order.le

/-- An ordered field as one bundle: the operations and the relation as
fields, then the arithmetic equations, the order laws, and the two laws
mixing order with algebra, `add_le_add_right` and `mul_nonneg`. `inv` is
total by decree -- `inv_zero` reads `inv zero = zero` -- and
`mul_inv_cancel` demands only that its argument differ from `zero`, so no
partial inverse is ever carried. `zero_ne_one` is the single nondegeneracy
requirement. -/
public structure IsOrderedFieldBaseLike (alpha : Type) where
  zero : alpha
  one : alpha
  add : alpha -> alpha -> alpha
  neg : alpha -> alpha
  mul : alpha -> alpha -> alpha
  inv : alpha -> alpha
  le : alpha -> alpha -> Prop
  le_refl : forall x, le x x
  le_trans : forall {x y z}, le x y -> le y z -> le x z
  le_antisymm : forall {x y}, le x y -> le y x -> x = y
  le_total : forall x y, Or (le x y) (le y x)
  zero_ne_one : Not (zero = one)
  add_comm : forall x y, add x y = add y x
  add_assoc : forall x y z, add (add x y) z = add x (add y z)
  add_zero : forall x, add x zero = x
  add_neg : forall x, add x (neg x) = zero
  add_le_add_right : forall {x y}, le x y -> forall z, le (add x z) (add y z)
  mul_comm : forall x y, mul x y = mul y x
  mul_assoc : forall x y z, mul (mul x y) z = mul x (mul y z)
  mul_one : forall x, mul x one = x
  mul_add : forall x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_inv_cancel : forall {x}, Not (x = zero) -> mul x (inv x) = one
  mul_nonneg : forall {x y}, le zero x -> le zero y -> le zero (mul x y)
  inv_zero : inv zero = zero

/-- A complete ordered field: an ordered-field bundle paired with
completeness of its own order, the field reached as `C.field`. This is the
interface each of the three constructions behind the valve room discharges on
its own carrier. -/
public structure IsDedekindCompleteOrderedFieldBaseLike (alpha : Type) where
  field : IsOrderedFieldBaseLike alpha
  complete : IsDedekindComplete alpha field.le

end Tautology
