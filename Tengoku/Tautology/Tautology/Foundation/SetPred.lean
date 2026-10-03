/-!
# Sets, as predicates

A set over `alpha` is a function `alpha -> Prop` and nothing else. There is no
`Set` type in this library, no membership relation, and no set-theoretic
foundation underneath; `x` belongs to `A` when `A x` holds, which is
definitional unfolding rather than a lemma. Everything here is the vocabulary
that follows from that decision -- inclusion, extensional equality, the
booleans on sets, singletons and pairs, disjointness, and unions and
intersections over an index type.

The decision pays at every use site. Membership proofs are the proofs of the
predicate itself, so `intro x hx` opens any inclusion and `exact hx.left`
closes a projection out of an intersection; the long chains of `have` that
this library is written in never have to unfold a membership. The cost is that
sets carry no extra structure, which is why `Subset` and `Same` are separate
notions and why the file needs the next paragraph.

## `Same` versus `=`, and where `propext` gets used

`Same A B` is pointwise `Iff`, which is what the definitions above naturally
produce. Actual equality of the two functions is stronger, and `eq_of_same`
bridges them by `funext` and `propext`. It is one of only seven files in the
library that invoke `propext` directly -- the others are
`Tautology.Foundation.Cardinal.Continuum`,
`Tautology.RealCardinality.ContinuumLower`,
`Tautology.RealBasic.ModuleBackend.Dedekind.Basic`,
`Tautology.RealBasic.ModuleBackend.Eudoxus.Order`,
`Tautology.RealBasic.ModuleBackend.Cauchy.Order` and
`Tautology.RealDerivative.Convexity` -- and it is the reason `propext` shows up
in the axiom footprint of results far above this one. Most consumers should
prefer `Same` and never need the bridge.

## Position in the development

Bottom of the dependency order, with no imports at all. Only
`Tautology.RealTopology.SetOps` imports it directly, but the vocabulary spreads
far past that: `SetPred.`-qualified names appear about 360 times across ten
regions, most heavily in `RealTopology` and `RealConnectedness`, which are
written almost entirely in it. This is the standard case of a module whose
direct import count says nothing about its reach.

## Role

Implementation.
The words this header uses in a sense particular to this library -- region,
route, waist, valve, facade, and the three kinds of aggregation module -- are
each defined once, in the header of the root module `Tautology`. This region
has no umbrella to carry that pointer, so the modules that use the vocabulary
carry it themselves.

-/

namespace Tautology
namespace SetPred

/-- Inclusion, read pointwise: every point of `A` is a point of `B`. The
directed half of `Same`, with no converse claimed. -/
def Subset {alpha : Type u} (A B : alpha -> Prop) : Prop :=
  forall x : alpha, A x -> B x

/-- Extensional equality, read pointwise: `A x` and `B x` are equivalent at
every point. The definitions naturally produce this rather than `=`, and it is
the preferred form; `eq_of_same` crosses to literal equality only where an
equation is required. -/
def Same {alpha : Type u} (A B : alpha -> Prop) : Prop :=
  forall x : alpha, A x <-> B x

/-- The empty set: `False` at every point, so a proof of membership is a
contradiction in hand. -/
def Empty {alpha : Type u} : alpha -> Prop :=
  fun _ => False

/-- The full set: `True` at every point, so membership carries no information
about the point. -/
def Universal {alpha : Type u} : alpha -> Prop :=
  fun _ => True

/-- Some point satisfies `A`. Written as a bare `Exists` over the predicate,
so classical choice applies to a proof of it directly. -/
def Nonempty {alpha : Type u} (A : alpha -> Prop) : Prop :=
  Exists (fun x : alpha => A x)

/-- Complement: `x` belongs when `A x` fails, so membership in one side
refutes membership in the other. -/
def Compl {alpha : Type u} (A : alpha -> Prop) : alpha -> Prop :=
  fun x => Not (A x)

/-- Intersection, a conjunction pointwise: `x` belongs when it belongs to
both `A` and `B`. -/
def Inter {alpha : Type u} (A B : alpha -> Prop) : alpha -> Prop :=
  fun x => And (A x) (B x)

/-- Union, a disjunction pointwise: `x` belongs when it belongs to either
`A` or `B`. -/
def Union {alpha : Type u} (A B : alpha -> Prop) : alpha -> Prop :=
  fun x => Or (A x) (B x)

/-- Difference: `x` belongs when it belongs to `A` and not to `B`, a
conjunction whose second conjunct is a refutation. -/
def Diff {alpha : Type u} (A B : alpha -> Prop) : alpha -> Prop :=
  fun x => And (A x) (Not (B x))

/-- The one-point set at `a`: membership is the equation `x = a`, so `a`
itself belongs by `rfl`. -/
def Singleton {alpha : Type u} (a : alpha) : alpha -> Prop :=
  fun x => x = a

/-- The two-point set at `a` and `b`: membership is `x = a` or `x = b`. -/
def Pair {alpha : Type u} (a b : alpha) : alpha -> Prop :=
  fun x => Or (x = a) (x = b)

/-- Disjointness: no point satisfies both `A` and `B`, stated as two
membership hypotheses concluding `False`. -/
def Disjoint {alpha : Type u} (A B : alpha -> Prop) : Prop :=
  forall x : alpha, A x -> B x -> False

/-- Union of an indexed family over an arbitrary type `iota`: `x` belongs
when some `i` has `A i x`. Over an empty index type nothing can belong, there
being no witness to produce. -/
def IndexedUnion {iota : Type v} {alpha : Type u}
    (A : iota -> alpha -> Prop) : alpha -> Prop :=
  fun x => Exists (fun i : iota => A i x)

/-- Intersection of an indexed family over an arbitrary type `iota`: `x`
belongs when every `i` has `A i x`. Over an empty index type every point
belongs, the condition being vacuous -- the dual reading of `IndexedUnion`. -/
def IndexedInter {iota : Type v} {alpha : Type u}
    (A : iota -> alpha -> Prop) : alpha -> Prop :=
  fun x => forall i : iota, A i x

theorem subset_refl {alpha : Type u} (A : alpha -> Prop) :
    Subset A A := by
  intro x hx
  exact hx

theorem subset_trans {alpha : Type u} {A B C : alpha -> Prop}
    (hAB : Subset A B) (hBC : Subset B C) :
    Subset A C := by
  intro x hx
  exact hBC x (hAB x hx)

theorem same_refl {alpha : Type u} (A : alpha -> Prop) :
    Same A A := by
  intro x
  exact Iff.rfl

theorem same_symm {alpha : Type u} {A B : alpha -> Prop}
    (h : Same A B) :
    Same B A := by
  intro x
  exact Iff.symm (h x)

theorem same_trans {alpha : Type u} {A B C : alpha -> Prop}
    (hAB : Same A B) (hBC : Same B C) :
    Same A C := by
  intro x
  exact Iff.trans (hAB x) (hBC x)

/-- Upgrades pointwise equivalence to literal equality of the two functions,
by `funext` and `propext` at each point. The one bridge between the two
notions; prefer `Same` and cross only where an equation between sets is
unavoidable. -/
theorem eq_of_same {alpha : Type u} {A B : alpha -> Prop}
    (h : Same A B) :
    A = B := by
  funext x
  exact propext (h x)

theorem inter_subset_left {alpha : Type u} (A B : alpha -> Prop) :
    Subset (Inter A B) A := by
  intro x hx
  exact hx.left

theorem inter_subset_right {alpha : Type u} (A B : alpha -> Prop) :
    Subset (Inter A B) B := by
  intro x hx
  exact hx.right

theorem subset_inter {alpha : Type u} {A B C : alpha -> Prop}
    (hAB : Subset A B) (hAC : Subset A C) :
    Subset A (Inter B C) := by
  intro x hx
  exact And.intro (hAB x hx) (hAC x hx)

theorem subset_union_left {alpha : Type u} (A B : alpha -> Prop) :
    Subset A (Union A B) := by
  intro x hx
  exact Or.inl hx

theorem subset_union_right {alpha : Type u} (A B : alpha -> Prop) :
    Subset B (Union A B) := by
  intro x hx
  exact Or.inr hx

theorem union_subset {alpha : Type u} {A B C : alpha -> Prop}
    (hAC : Subset A C) (hBC : Subset B C) :
    Subset (Union A B) C := by
  intro x hx
  cases hx with
  | inl hA => exact hAC x hA
  | inr hB => exact hBC x hB

end SetPred
end Tautology
