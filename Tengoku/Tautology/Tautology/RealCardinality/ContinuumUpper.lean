import Tengoku.Tautology.Tautology.Foundation.Cardinal.Continuum
import Tengoku.Tautology.Tautology.RealTopology.RationalBasis

/-!
# At most continuum many points

The upper half of the cardinality computation: a Dedekind-complete ordered
field injects into the binary sequences, so it has at most continuum many
points.

A point is coded by the set of internal-rational open intervals containing it.
Two distinct points are separated by such an interval because the internal
rationals are dense, so the code is injective; and since the alphabet of
intervals is countable, a subset of it is a bit sequence. The bound is the
composite of those two steps.

## Why the alphabet comes from the topology

`InternalRatIntervalParam` and its countability are not defined here but in
`Tautology.RealTopology.RationalBasis`, where they serve as the countable base
of the order topology. Reusing them is the only reason this region depends on
`RealTopology` at all. That dependency used to run both ways: the countability
of the internal rationals themselves once lived in this region and was pulled
back down to `Tautology.RealBootstrap.InternalCountable` precisely to break the
cycle, so the edge is now one-directional.

## Position and role

Implementation module. The two definitions make sense over any ordered field
and the alphabet is countable there too; completeness is needed only for the
density step that separates points, and hence for injectivity and the bound
itself. `continuumUpperBound` is consumed by `Continuum` in this region and by
`Tautology.RealTheory.Cardinality`, which specialises it to the selected
carrier.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The type of ordered pairs of internal rationals `p.fst < p.snd`, taken
as a subtype. This is the countable alphabet of intervals that the
upper-bound argument codes points with; it is countable already over any
ordered field, since the internal rationals are. -/
abbrev InternalRatIntervalSubtype : Type :=
  {p : Prod alpha alpha // InternalRatIntervalParam F p}

/-- The neighbourhood code of `x`: the set of internal-rational open
intervals containing `x`. The code is defined over any ordered field, but
it is injective only once the internal rationals are dense, which is where
Dedekind completeness enters the upper-bound argument. -/
def intervalNeighborhoodCode (x : alpha) :
    InternalRatIntervalSubtype F -> Prop :=
  fun p => OpenInterval F p.val.fst p.val.snd x

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

theorem exists_internalRat_interval_separating {x y : alpha}
    (hxy : C.field.lt x y) :
    Exists (fun p : Prod alpha alpha =>
      And (C.field.InternalRatIntervalParam p)
        (And
          (C.field.OpenInterval p.fst p.snd x)
          (Not (C.field.OpenInterval p.fst p.snd y)))) := by
  let F := C.field
  have hleft_gap : F.lt (F.sub x F.one) x :=
    IsOrderedFieldBaseLike.sub_lt_self_of_pos F
      (IsOrderedFieldBaseLike.zero_lt_one F)
  cases exists_internalRat_between C hleft_gap with
  | intro l hl =>
      cases exists_internalRat_between C hxy with
      | intro r hr =>
          refine Exists.intro (l, r) ?_
          have hlr : F.lt l r :=
            IsOrderedFieldBaseLike.lt_trans F
              hl.right.right hr.right.left
          exact And.intro
            (And.intro hl.left (And.intro hr.left hlr))
            (And.intro
              (And.intro hl.right.right hr.right.left)
              (by
                intro hy
                exact
                  (IsOrderedFieldBaseLike.lt_asymm F hr.right.right)
                    hy.right))

/-- Distinct points get distinct codes: given `x < y`, density of the internal
rationals produces an interval containing `x` but not `y`, so the two codes
differ on that interval. -/
theorem intervalNeighborhoodCode_injective :
    Foundation.Cardinal.Injective
      (C.field.intervalNeighborhoodCode) := by
  intro x y hxycode
  let F := C.field
  by_cases hle_xy : F.le x y
  · by_cases hle_yx : F.le y x
    · exact F.le_antisymm hle_xy hle_yx
    · have hlt_xy : F.lt x y :=
        IsOrderedFieldBaseLike.lt_of_le_of_not_le F hle_xy hle_yx
      cases exists_internalRat_interval_separating C hlt_xy with
      | intro p hp =>
          let ps : F.InternalRatIntervalSubtype := ⟨p, hp.left⟩
          have hxmem : F.intervalNeighborhoodCode x ps :=
            hp.right.left
          have hymem_not : Not (F.intervalNeighborhoodCode y ps) :=
            hp.right.right
          have hpoint := congrFun hxycode ps
          rw [hpoint] at hxmem
          exact False.elim (hymem_not hxmem)
  · cases F.le_total x y with
    | inl hle_xy' =>
        exact False.elim (hle_xy hle_xy')
    | inr hle_yx =>
        have hlt_yx : F.lt y x :=
          IsOrderedFieldBaseLike.lt_of_le_of_not_le F hle_yx hle_xy
        cases exists_internalRat_interval_separating C hlt_yx with
        | intro p hp =>
            let ps : F.InternalRatIntervalSubtype := ⟨p, hp.left⟩
            have hymem : F.intervalNeighborhoodCode y ps :=
              hp.right.left
            have hxmem_not : Not (F.intervalNeighborhoodCode x ps) :=
              hp.right.right
            have hpoint := congrFun hxycode ps
            rw [<- hpoint] at hymem
            exact False.elim (hxmem_not hymem)

/-- Any Dedekind-complete ordered field injects into the binary sequences,
and therefore has at most continuum many points. A point is coded by the
set of internal-rational intervals containing it; the code separates points
because the internal rationals are dense, and it can be read off as a bit
sequence because the alphabet of intervals is countable. Completeness is
used only for the density step. -/
theorem continuumUpperBound
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha) :
    Foundation.Cardinal.ContinuumUpperBound alpha := by
  let F := C.field
  have hparam_count :
      Foundation.Cardinal.CountableSet
        (F.InternalRatIntervalParam) :=
    F.internalRatIntervalParam_countable
  have hparam_enum :
      Foundation.Cardinal.Enumerable (F.InternalRatIntervalSubtype) :=
    Foundation.Cardinal.enumerable_subtype_of_countableSet hparam_count
  have hcode :
      Foundation.Cardinal.CardLE
        alpha (F.InternalRatIntervalSubtype -> Prop) :=
    Exists.intro F.intervalNeighborhoodCode
      (intervalNeighborhoodCode_injective C)
  have hpowerset :
      Foundation.Cardinal.CardLE
        (F.InternalRatIntervalSubtype -> Prop)
        Foundation.Cardinal.BinarySequences :=
    Foundation.Cardinal.powerset_cardLE_binarySequences_of_enumerable
      hparam_enum
  exact Foundation.Cardinal.cardLE_trans hcode hpowerset

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
