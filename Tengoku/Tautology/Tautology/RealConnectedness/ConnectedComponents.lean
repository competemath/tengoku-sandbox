import Tengoku.Tautology.Tautology.RealConnectedness.Connected
import Tengoku.Tautology.Tautology.RealTopology.RationalBasis

/-!
# Connected components, and the countable decomposition of an open set

Components are defined pointwise rather than as a union: `y` lies in the
component of `x` in `S` when some connected subset of `S` contains both. From
that definition the file proves the component is an interval set and hence
connected, that two components are equal or disjoint, that it is maximal among
connected subsets containing the point, and -- the result the region exists for
-- that an open set is exactly the union of the components of the internal
rationals it contains, a union indexed by a countable parameter set.

## Why pointwise, and where completeness enters

The library has no general topological theorem that a union of connected sets
sharing a point is connected. The route here goes through
`Tautology.RealConnectedness.Connected` instead: two witnesses through a common
base point glue into an interval set (`intervalSet_union_of_common`), and
interval sets are connected over a complete field. So "the component is
connected" is a completeness fact in this development, not a formal consequence
of the definition.

Completeness is spent in three places: turning the component's interval-ness
into connectedness, showing the component of a point in an open set is open
(via connectedness of open intervals), and finding an internal rational inside
a nonempty open set, which comes from `Tautology.RealTopology.RationalBasis`.
The countability of the parameter alphabet itself is *not* one of them: that
the internal rationals are countable holds over any ordered field and lives in
`Tautology.RealBootstrap.InternalCountable`. The file's namespace split records
exactly this line -- `intervalSet_union_of_common` is the one declaration that
needs no completeness.

## Reading the cover record

`InternalRatComponentCover` bundles what the decomposition promises: the
parameter set is countable, every member sits inside the open set, is open,
connected and an interval set, distinct parameters give members that are equal
or disjoint, and the members exhaust the set. "Equal or disjoint" rather than
"disjoint" is not sloppiness -- the map from a rational to its component is far
from injective, since every rational inside one component names that same
component.

## Position and role

Implementation module. It builds on `Tautology.RealConnectedness.Connected` and
`Tautology.RealTopology.RationalBasis`;
`Tautology.RealConnectedness.OpenDecomposition` repackages its main theorem,
and `Tautology.RealTheory.Topology` specialises the results to the selected
carrier. Stated throughout over an arbitrary ordered field or an arbitrary
Dedekind-complete one, never over the constructed real line.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Two interval sets that share a point have an interval set as their union:
comparing the in-between point with the common point decides which of the two
collects it. Ordered-field algebra only; no completeness enters. -/
theorem intervalSet_union_of_common {A B : alpha -> Prop} {x : alpha}
    (hA : IsIntervalSet F A)
    (hB : IsIntervalSet F B)
    (hxA : A x) (hxB : B x) :
    IsIntervalSet F (SetPred.Union A B) := by
  intro a y b ha hb hy
  cases ha with
  | inl haA =>
      cases hb with
      | inl hbA =>
          exact Or.inl (hA a y b haA hbA hy)
      | inr hbB =>
          by_cases hyx : F.le y x
          · exact Or.inl (hA a y x haA hxA (And.intro hy.left hyx))
          · have hxy : F.le x y := by
              cases F.le_total x y with
              | inl h => exact h
              | inr h => exact False.elim (hyx h)
            exact Or.inr (hB x y b hxB hbB (And.intro hxy hy.right))
  | inr haB =>
      cases hb with
      | inl hbA =>
          by_cases hyx : F.le y x
          · exact Or.inr (hB a y x haB hxB (And.intro hy.left hyx))
          · have hxy : F.le x y := by
              cases F.le_total x y with
              | inl h => exact h
              | inr h => exact False.elim (hyx h)
            exact Or.inl (hA x y b hxA hbA (And.intro hxy hy.right))
      | inr hbB =>
          exact Or.inr (hB a y b haB hbB hy)

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The connected component of `x` in `S`: `y` belongs to it when some
connected subset of `S` contains both `x` and `y`. Membership is stated by an
existential rather than by unioning a family of sets, and the definition
itself uses only field-level vocabulary; every completeness-dependent fact
about it is a theorem below. -/
def ConnectedComponentAt (S : alpha -> Prop) (x : alpha) : alpha -> Prop :=
  fun y =>
    Exists
      (fun K : alpha -> Prop =>
        And (SetPred.Subset K S)
          (And ((F C).IsConnected K)
            (And (K x) (K y))))

/-- `K` is a maximal connected subset of `S`: connected, nonempty, contained
in `S`, and absorbing every connected subset of `S` that contains it.
Maximality is phrased as mutual inclusion because that is the shape both the
construction of a component and the comparison of two maximal sets consume. -/
def IsMaximalConnectedIn (S K : alpha -> Prop) : Prop :=
  And (SetPred.Subset K S)
    (And ((F C).IsConnected K)
      (And (SetPred.Nonempty K)
        (forall L : alpha -> Prop,
          SetPred.Subset L S ->
            (F C).IsConnected L ->
              SetPred.Subset K L -> SetPred.Subset L K)))

/-- `K` is a connected component of `S` when it is the component of one of the
points of `S`. An existential over base points rather than a list of
properties: being a component is exactly being a component-at, so every
property of `K` is read off `ConnectedComponentAt`. -/
def IsConnectedComponentIn (S K : alpha -> Prop) : Prop :=
  Exists
    (fun x : alpha =>
      And (S x) (SetPred.Same K (ConnectedComponentAt C S x)))

/-- The parameter set for the rational indexing of components: the internal
rationals `q` that lie in `U` themselves. Restricting to points of `U` makes
every parameter name a nonempty component, and the set stays countable as a
subset of the internal rationals. -/
def InternalRatComponentParam (U : alpha -> Prop) (q : alpha) : Prop :=
  And ((F C).InternalRat q) (U q)

/-- The component of `U` at the internal rational `q`, with `q` exposed as an
argument. The name records the intended reading: `q` ranges over internal
rationals, which is what makes the family of all such components countable. -/
def InternalRatComponent (U : alpha -> Prop) (q : alpha) :
    alpha -> Prop :=
  ConnectedComponentAt C U q

/-- The component decomposition of an open set `U`, indexed by a countable
set `J` of internal rationals of `U`: each member is an open, connected
interval subset of `U`, two members are either the same set or disjoint, and
the members cover `U`. The disjunction rather than plain disjointness
reflects that two parameters may sit in one component and then name it
twice. -/
def InternalRatComponentCover
    (U J : alpha -> Prop) : Prop :=
  And (Foundation.Cardinal.CountableSet J)
    (And (forall q : alpha, J q -> InternalRatComponentParam C U q)
      (And (forall q : alpha, J q ->
          SetPred.Subset (InternalRatComponent C U q) U)
        (And (forall q : alpha, J q ->
            (F C).IsOpen (InternalRatComponent C U q))
          (And (forall q : alpha, J q ->
              (F C).IsConnected (InternalRatComponent C U q))
            (And (forall q : alpha, J q ->
                (F C).IsIntervalSet (InternalRatComponent C U q))
              (And (forall q r : alpha, J q -> J r ->
                  Or
                    (SetPred.Same
                      (InternalRatComponent C U q)
                      (InternalRatComponent C U r))
                    (SetPred.Disjoint
                      (InternalRatComponent C U q)
                      (InternalRatComponent C U r)))
                (forall y : alpha,
                  U y <->
                    Exists
                      (fun q : alpha =>
                        And (J q) (InternalRatComponent C U q y)))))))))

/-- A component is contained in its ambient set: the connected witness
inside the existential already is. -/
theorem componentAt_subset {S : alpha -> Prop} {x : alpha} :
    SetPred.Subset (ConnectedComponentAt C S x) S := by
  intro y hy
  cases hy with
  | intro K hK =>
      exact hK.left y hK.right.right.right

/-- The base point lies in its own component, witnessed by the singleton. A
point outside `S` admits no witness, so its component is empty. -/
theorem componentAt_mem_base {S : alpha -> Prop} {x : alpha}
    (hx : S x) :
    ConnectedComponentAt C S x x := by
  refine Exists.intro (SetPred.Singleton x) ?_
  refine And.intro ?_ ?_
  · intro y hy
    rw [hy]
    exact hx
  · refine And.intro (connected_singleton C x) ?_
    exact And.intro rfl rfl

/-- Component membership is symmetric in its two points: the witness carries
both, so exchanging them changes nothing. -/
theorem componentAt_symm {S : alpha -> Prop} {x y : alpha}
    (hxy : ConnectedComponentAt C S x y) :
    ConnectedComponentAt C S y x := by
  cases hxy with
  | intro K hK =>
      exact Exists.intro K
        (And.intro hK.left
          (And.intro hK.right.left
            (And.intro hK.right.right.right hK.right.right.left)))

/-- Every connected subset of `S` containing `x` is contained in the
component of `x`: the component collects exactly those witnesses. This is
the maximality engine behind `componentAt_maximal`. -/
theorem subset_componentAt_of_connected {S K : alpha -> Prop} {x : alpha}
    (hKS : SetPred.Subset K S)
    (hKconn : (F C).IsConnected K)
    (hxK : K x) :
    SetPred.Subset K (ConnectedComponentAt C S x) := by
  intro y hy
  exact Exists.intro K
    (And.intro hKS
      (And.intro hKconn (And.intro hxK hy)))

/-- The component of any point of any set is an interval set: two witnesses
through two points with a third in between are united through their common
base point by `intervalSet_union_of_common`. This is the step that gives
components their geometry. -/
theorem componentAt_intervalSet {S : alpha -> Prop} {x : alpha} :
    (F C).IsIntervalSet (ConnectedComponentAt C S x) := by
  intro a y b ha hb hy
  cases ha with
  | intro A hA =>
      cases hb with
      | intro B hB =>
          let D : alpha -> Prop := SetPred.Union A B
          have hAinterval : (F C).IsIntervalSet A :=
            IsOrderedFieldBaseLike.intervalSet_of_connected (F C)
              hA.right.left
          have hBinterval : (F C).IsIntervalSet B :=
            IsOrderedFieldBaseLike.intervalSet_of_connected (F C)
              hB.right.left
          have hDinterval : (F C).IsIntervalSet D :=
            IsOrderedFieldBaseLike.intervalSet_union_of_common (F C)
              hAinterval hBinterval
              hA.right.right.left hB.right.right.left
          have hDconn : (F C).IsConnected D :=
            connected_of_intervalSet C hDinterval
          have hDS : SetPred.Subset D S := by
            intro z hz
            cases hz with
            | inl hzA => exact hA.left z hzA
            | inr hzB => exact hB.left z hzB
          have hxD : D x := Or.inl hA.right.right.left
          have hyD : D y :=
            hDinterval a y b
              (Or.inl hA.right.right.right)
              (Or.inr hB.right.right.right) hy
          exact Exists.intro D
            (And.intro hDS (And.intro hDconn (And.intro hxD hyD)))

/-- The component of `x` is connected. The route is through interval sets
and then `connected_of_intervalSet`, which is where Dedekind completeness
enters the theory of components. -/
theorem componentAt_connected {S : alpha -> Prop} {x : alpha} :
    (F C).IsConnected (ConnectedComponentAt C S x) :=
  connected_of_intervalSet C (componentAt_intervalSet C)

/-- Two points of one component have the same component, so a component can
be re-based at any of its points. -/
theorem componentAt_same_of_mem {S : alpha -> Prop} {x y : alpha}
    (hxy : ConnectedComponentAt C S x y) :
    SetPred.Same
      (ConnectedComponentAt C S x)
      (ConnectedComponentAt C S y) := by
  have hyx : ConnectedComponentAt C S y x :=
    componentAt_symm C hxy
  intro z
  constructor
  · intro hz
    exact
      subset_componentAt_of_connected C
        (componentAt_subset C)
        (componentAt_connected C)
        hxy z hz
  · intro hz
    exact
      subset_componentAt_of_connected C
        (componentAt_subset C)
        (componentAt_connected C)
        hyx z hz

/-- Components that share a point are the same component, by re-basing at
that point. -/
theorem componentAt_same_of_inter {S : alpha -> Prop} {x y : alpha}
    (hinter :
      SetPred.Nonempty
        (SetPred.Inter
          (ConnectedComponentAt C S x)
          (ConnectedComponentAt C S y))) :
    SetPred.Same
      (ConnectedComponentAt C S x)
      (ConnectedComponentAt C S y) := by
  cases hinter with
  | intro z hz =>
      have hxz :
          SetPred.Same
            (ConnectedComponentAt C S x)
            (ConnectedComponentAt C S z) :=
        componentAt_same_of_mem C hz.left
      have hyz :
          SetPred.Same
            (ConnectedComponentAt C S y)
            (ConnectedComponentAt C S z) :=
        componentAt_same_of_mem C hz.right
      exact SetPred.same_trans hxz (SetPred.same_symm hyz)

/-- Two components either coincide or are disjoint, the case split being on
whether they meet. Coincidence is stated as `SetPred.Same` because
components are pointwise predicates, not terms of a quotient. -/
theorem componentAt_same_or_disjoint
    {S : alpha -> Prop} (x y : alpha) :
    Or
      (SetPred.Same
        (ConnectedComponentAt C S x)
        (ConnectedComponentAt C S y))
      (SetPred.Disjoint
        (ConnectedComponentAt C S x)
        (ConnectedComponentAt C S y)) := by
  by_cases h :
      SetPred.Nonempty
        (SetPred.Inter
          (ConnectedComponentAt C S x)
          (ConnectedComponentAt C S y))
  · exact Or.inl (componentAt_same_of_inter C h)
  · refine Or.inr ?_
    intro z hzX hzY
    exact h (Exists.intro z (And.intro hzX hzY))

/-- The component of a point of `S` is a maximal connected subset of `S`. The
hypothesis `S x` is what makes the component nonempty; the component of a
point outside `S` is empty and not maximal. -/
theorem componentAt_maximal {S : alpha -> Prop} {x : alpha}
    (hx : S x) :
    IsMaximalConnectedIn C S (ConnectedComponentAt C S x) := by
  refine And.intro (componentAt_subset C) ?_
  refine And.intro (componentAt_connected C) ?_
  refine And.intro (Exists.intro x (componentAt_mem_base C hx)) ?_
  intro L hLS hLconn hcompL
  have hxL : L x := hcompL x (componentAt_mem_base C hx)
  exact subset_componentAt_of_connected C hLS hLconn hxL

/-- The component of a point of `S` is a connected component in the
existential sense, with the point itself as witness. -/
theorem connectedComponentAt_is_component {S : alpha -> Prop} {x : alpha}
    (hx : S x) :
    IsConnectedComponentIn C S (ConnectedComponentAt C S x) :=
  Exists.intro x (And.intro hx (SetPred.same_refl _))

/-- A connected component of `S` is contained in `S`, read off the
representing base point. -/
theorem connectedComponent_subset {S K : alpha -> Prop}
    (hK : IsConnectedComponentIn C S K) :
    SetPred.Subset K S := by
  cases hK with
  | intro x hx =>
      intro y hyK
      exact componentAt_subset C y ((hx.right y).mp hyK)

/-- A connected component in the existential sense is connected; the
interval-set property of the representing component transports along the
`Same`. -/
theorem connectedComponent_connected {S K : alpha -> Prop}
    (hK : IsConnectedComponentIn C S K) :
    (F C).IsConnected K := by
  cases hK with
  | intro x hx =>
      apply connected_of_intervalSet C
      intro a y b ha hb hy
      have ha' : ConnectedComponentAt C S x a := (hx.right a).mp ha
      have hb' : ConnectedComponentAt C S x b := (hx.right b).mp hb
      exact (hx.right y).mpr
        ((componentAt_intervalSet C) a y b ha' hb' hy)

/-- A connected component is nonempty: its base point belongs to it. -/
theorem connectedComponent_nonempty {S K : alpha -> Prop}
    (hK : IsConnectedComponentIn C S K) :
    SetPred.Nonempty K := by
  cases hK with
  | intro x hx =>
      exact Exists.intro x ((hx.right x).mpr (componentAt_mem_base C hx.left))

/-- A connected component in the existential sense is maximal, obtained by
re-basing the maximality of components-at. -/
theorem connectedComponent_maximal {S K : alpha -> Prop}
    (hK : IsConnectedComponentIn C S K) :
    IsMaximalConnectedIn C S K := by
  cases hK with
  | intro x hx =>
      have hmax := componentAt_maximal C hx.left
      refine And.intro (connectedComponent_subset C (Exists.intro x hx)) ?_
      refine And.intro (connectedComponent_connected C (Exists.intro x hx)) ?_
      refine And.intro (connectedComponent_nonempty C (Exists.intro x hx)) ?_
      intro L hLS hLconn hKL
      have hcompL :
          SetPred.Subset (ConnectedComponentAt C S x) L := by
        intro y hy
        exact hKL y ((hx.right y).mpr hy)
      have hLcomp : SetPred.Subset L (ConnectedComponentAt C S x) :=
        hmax.right.right.right L hLS hLconn hcompL
      intro y hyL
      exact (hx.right y).mpr (hLcomp y hyL)

/-- In an open set, every component is open: around any of its points there
is an open interval inside `U`, that interval is connected, and it is
therefore already part of the component. Completeness enters through the
connectedness of open intervals. -/
theorem componentAt_open_of_open {U : alpha -> Prop} {x : alpha}
    (hUopen : (F C).IsOpen U) :
    (F C).IsOpen (ConnectedComponentAt C U x) := by
  intro y hy
  have hyU : U y := componentAt_subset C y hy
  have hsame :
      SetPred.Same
        (ConnectedComponentAt C U x)
        (ConnectedComponentAt C U y) :=
    componentAt_same_of_mem C hy
  cases hUopen y hyU with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          refine Exists.intro left ?_
          refine Exists.intro right ?_
          refine And.intro hright.left ?_
          refine And.intro hright.right.left ?_
          intro z hz
          have hintervalConn : (F C).IsConnected ((F C).OpenInterval left right) :=
            connected_openInterval C left right
          have hintervalSub : SetPred.Subset ((F C).OpenInterval left right) U :=
            hright.right.right
          have hyInterval : (F C).OpenInterval left right y :=
            And.intro hright.left hright.right.left
          have hzCompY : ConnectedComponentAt C U y z :=
            subset_componentAt_of_connected C hintervalSub hintervalConn
              hyInterval z hz
          exact (hsame z).mpr hzCompY

/-- The rational parameter set is countable, being a subset of the internal
rationals -- a fact of ordered fields, with no completeness in it. -/
theorem internalRatComponentParam_countable {U : alpha -> Prop} :
    Foundation.Cardinal.CountableSet
      (InternalRatComponentParam C U) :=
  Foundation.Cardinal.countableSet_mono
    ((F C).internalRat_countable)
    (fun _ hq => hq.left)

/-- The component of a rational parameter stays inside `U`; the cover record
cites this field separately so its entries each name what they use. -/
theorem internalRatComponent_subset {U : alpha -> Prop} {q : alpha} :
    SetPred.Subset (InternalRatComponent C U q) U :=
  componentAt_subset C

/-- The component of a rational parameter is connected, `componentAt_connected`
with the parameter exposed. -/
theorem internalRatComponent_connected {U : alpha -> Prop} {q : alpha} :
    (F C).IsConnected (InternalRatComponent C U q) :=
  componentAt_connected C

/-- The component of a rational parameter is an interval set,
`componentAt_intervalSet` with the parameter exposed. -/
theorem internalRatComponent_intervalSet {U : alpha -> Prop} {q : alpha} :
    (F C).IsIntervalSet (InternalRatComponent C U q) :=
  componentAt_intervalSet C

/-- The component of a rational parameter of an open set is open; openness of
the ambient set is the only hypothesis, as in `componentAt_open_of_open`. -/
theorem internalRatComponent_open_of_open {U : alpha -> Prop} {q : alpha}
    (hUopen : (F C).IsOpen U) :
    (F C).IsOpen (InternalRatComponent C U q) :=
  componentAt_open_of_open C hUopen

/-- Components of two rational parameters are either the same set or
disjoint, the field of the cover record that the decomposition inherits. -/
theorem internalRatComponents_same_or_disjoint
    {U : alpha -> Prop} (q r : alpha) :
    Or
      (SetPred.Same
        (InternalRatComponent C U q)
        (InternalRatComponent C U r))
      (SetPred.Disjoint
        (InternalRatComponent C U q)
        (InternalRatComponent C U r)) :=
  componentAt_same_or_disjoint C q r

/-- Every point of an open set shares its component with an internal rational:
the component is open and nonempty, and every nonempty open set contains an
internal rational (`Tautology.RealTopology.RationalBasis`). This bridge is what
lets the countability of the internal rationals bound the number of components.
-/
theorem componentAt_has_internalRat_of_open
    {U : alpha -> Prop} {x : alpha}
    (hUopen : (F C).IsOpen U)
    (hx : U x) :
    Exists
      (fun q : alpha =>
        And (InternalRatComponentParam C U q)
          (SetPred.Same
            (ConnectedComponentAt C U x)
            (ConnectedComponentAt C U q))) := by
  have hcomponentOpen :
      (F C).IsOpen (ConnectedComponentAt C U x) :=
    componentAt_open_of_open C hUopen
  have hcomponentNonempty :
      Exists (fun y : alpha => ConnectedComponentAt C U x y) :=
    Exists.intro x (componentAt_mem_base C hx)
  cases exists_internalRat_mem_of_open_nonempty C
      hcomponentOpen hcomponentNonempty with
  | intro q hq =>
      have hqU : U q := componentAt_subset C q hq.right
      exact Exists.intro q
        (And.intro
          (And.intro hq.left hqU)
          (componentAt_same_of_mem C hq.right))

/-- An open set is exactly the union of the components of its internal
rational points. One direction is the containment of components in `U`; the
other re-bases the component of any point at a rational supplied by
`componentAt_has_internalRat_of_open`. -/
theorem open_eq_internalRatComponent_union
    {U : alpha -> Prop}
    (hUopen : (F C).IsOpen U) :
    forall y : alpha,
      U y <->
        Exists
          (fun q : alpha =>
            And (InternalRatComponentParam C U q)
              (InternalRatComponent C U q y)) := by
  intro y
  constructor
  · intro hy
    cases componentAt_has_internalRat_of_open C hUopen hy with
    | intro q hq =>
        have hyComponentY : ConnectedComponentAt C U y y :=
          componentAt_mem_base C hy
        have hyComponentQ :
            ConnectedComponentAt C U q y :=
          (hq.right y).mp hyComponentY
        exact Exists.intro q
          (And.intro hq.left hyComponentQ)
  · intro hy
    cases hy with
    | intro q hq =>
        exact componentAt_subset C y hq.right

/-- Every open set admits the component decomposition: take the parameters
to be the internal rationals of `U` themselves. `OpenDecomposition` turns
this record into a countable family of pairwise disjoint open intervals. -/
theorem open_internalRatComponentCover
    {U : alpha -> Prop}
    (hUopen : (F C).IsOpen U) :
    Exists (fun J : alpha -> Prop =>
      InternalRatComponentCover C U J) := by
  refine Exists.intro (InternalRatComponentParam C U) ?_
  refine And.intro (internalRatComponentParam_countable C) ?_
  refine And.intro (fun q hq => hq) ?_
  refine And.intro (fun q _ => internalRatComponent_subset C) ?_
  refine And.intro (fun q _ => internalRatComponent_open_of_open C hUopen) ?_
  refine And.intro (fun q _ => internalRatComponent_connected C) ?_
  refine And.intro (fun q _ => internalRatComponent_intervalSet C) ?_
  refine And.intro
    (fun q r _ _ => internalRatComponents_same_or_disjoint C q r) ?_
  exact open_eq_internalRatComponent_union C hUopen

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
