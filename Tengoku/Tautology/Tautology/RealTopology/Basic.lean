import Tengoku.Tautology.Tautology.RealBootstrap.Abs
import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra
import Tengoku.Tautology.Tautology.Foundation.Cardinal

/-!
# Order metric, open sets, and covers

The first definitions of the region: the metric `dist x y = |x - y|` induced by
the order, the open interval as a pointwise predicate, the openness predicate
itself, and the covering vocabulary (`Covers`, `Subcover`, `CountableSubcover`)
that `Tautology.RealTopology.Lindelof` will act on.

Two shape decisions are worth reading off the definitions rather than guessing.
`IsOpen` demands an interval witness -- a pair of endpoints straddling the
point, with the whole interval inside the set -- and not a radius, even though
`OpenBall` is defined here; no theorem in the library connects the two, and
`OpenBall` has no consumers. And a subcover is presented by a predicate on the
index type rather than by re-indexing, which lets countability be a property of
that predicate alone.

The five metric facts (`dist_self`, `dist_comm`, `dist_nonneg`,
`dist_pos_of_ne`, `dist_triangle`) are one-line restatements of the
absolute-value laws of `Tautology.RealBootstrap.Abs`; nothing here is proved
about the metric that is not already an absolute-value fact.

## Position and role

Implementation module, the base of `RealTopology`. Stated over an arbitrary
ordered field `(F : IsOrderedFieldBaseLike alpha)`; completeness plays no part
here, and `CountableSubcover` is only a piece of vocabulary until
`Tautology.RealTopology.Lindelof` produces one.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The metric induced by the order: the distance from `x` to `y` is
`|x - y|`, a value of the field itself. Everything proved about it below is
a restatement of an absolute-value law. -/
noncomputable def dist (x y : alpha) : alpha :=
  abs F (F.sub x y)

/-- The open ball of radius `radius` centred at `center`: the points whose
distance to `center` is strictly below `radius`. The radius-shaped
neighbourhood, sitting next to `OpenInterval`; the openness predicate below
is stated through intervals, not through balls. -/
noncomputable def OpenBall (center radius : alpha) : alpha -> Prop :=
  fun x => F.lt (dist F x center) radius

theorem dist_self (x : alpha) :
    dist F x x = F.zero := by
  unfold dist
  exact abs_sub_self F x

theorem dist_comm (x y : alpha) :
    dist F x y = dist F y x := by
  unfold dist
  exact abs_sub_comm F x y

theorem dist_nonneg (x y : alpha) :
    F.le F.zero (dist F x y) := by
  unfold dist
  exact abs_nonneg F (F.sub x y)

theorem dist_pos_of_ne {x y : alpha}
    (hxy : Not (x = y)) :
    F.lt F.zero (dist F x y) := by
  unfold dist
  apply abs_pos_of_ne_zero F
  intro hsub
  exact hxy (eq_of_sub_eq_zero F hsub)

theorem dist_triangle (x y z : alpha) :
    F.le (dist F x z) (F.add (dist F x y) (dist F y z)) := by
  unfold dist
  have h :=
    abs_add_le_abs_add_abs F (F.sub x y) (F.sub y z)
  rwa [sub_add_sub_cancel F x y z] at h

/-- The open interval `(left, right)` as a pointwise predicate on the field,
`left < x < right`. It is empty whenever `right ≤ left`. -/
def OpenInterval (left right : alpha) : alpha -> Prop :=
  fun x => And (F.lt left x) (F.lt x right)

/-- A set is open when every point of it lies in some open interval that is
contained in the set. The witness demanded is a pair of endpoints with
`left < x < right`, not a radius, and it may depend on the point. -/
def IsOpen (U : alpha -> Prop) : Prop :=
  forall x : alpha,
    U x ->
      Exists (fun left : alpha =>
        Exists (fun right : alpha =>
          And (F.lt left x)
            (And (F.lt x right)
              (forall y : alpha, OpenInterval F left right y -> U y))))

/-- The family `U` covers `S`: every point of `S` lies in at least one of
its members. The index type is arbitrary, so this says nothing about the
size or shape of the family. -/
def Covers {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop) : Prop :=
  forall x : alpha, S x -> Exists (fun i : iota => U i x)

/-- The subfamily of `U` picked out by the index predicate `J` still covers
`S`. A subcover is presented by marking indices rather than by re-indexing
or listing, which keeps countability a property of `J` alone. -/
def Subcover {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop)
    (J : iota -> Prop) : Prop :=
  forall x : alpha, S x -> Exists (fun i : iota => And (J i) (U i x))

/-- `S` admits a countable subcover from `U`: some `J`, countable in the sense
of `Foundation.Cardinal.CountableSet`, with `Subcover U S J`. This is the
conclusion that the Lindelöf theorem of `Tautology.RealTopology.Lindelof`
extracts from a plain `Covers`; the definition itself stays at the
ordered-field level, while that extraction is where Dedekind completeness
enters. -/
def CountableSubcover {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop) : Prop :=
  Exists (fun J : iota -> Prop =>
    And (Foundation.Cardinal.CountableSet J) (Subcover U S J))

end IsOrderedFieldBaseLike
end Tautology
