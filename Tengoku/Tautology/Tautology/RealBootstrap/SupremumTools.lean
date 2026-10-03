import Tengoku.Tautology.Tautology.RealBootstrap.Lattice
import Tengoku.Tautology.Tautology.RealBootstrap.Supremum

/-!
# Bounds under monotonicity, singletons and pairs

Ten small facts that let bounds be computed rather than re-derived: bounds
inherit along set inclusion, extrema of a set that contains its own bound,
suprema of singletons, and suprema of pairs as the binary maximum.

Nothing here uses completeness -- these are statements about *given* bounds, so
they hold in any ordered field. They are the reason arguments upstream can push
a supremum through a small set manipulation without going back to the
definition.

## Position and role

Implementation module over an arbitrary ordered field, sitting on
`Tautology.RealBootstrap.Supremum` and `Tautology.RealBootstrap.Lattice`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem upperBound_mono {S T : alpha -> Prop} {u : alpha}
    (hST : forall x : alpha, S x -> T x)
    (hu : IsUpperBound F.le T u) :
    IsUpperBound F.le S u := by
  intro x hx
  exact hu x (hST x hx)

theorem lowerBound_mono {S T : alpha -> Prop} {l : alpha}
    (hST : forall x : alpha, S x -> T x)
    (hl : IsLowerBound F.le T l) :
    IsLowerBound F.le S l := by
  intro x hx
  exact hl x (hST x hx)

theorem lub_mono {S T : alpha -> Prop} {s t : alpha}
    (hST : forall x : alpha, S x -> T x)
    (hs : IsLeastUpperBound F.le S s)
    (ht : IsLeastUpperBound F.le T t) :
    F.le s t :=
  hs.right t (upperBound_mono F hST ht.left)

/-- Inclusion of `S` in `T` forces the greatest lower bound of `T` below that
of `S`: enlarging a set can only lower its infimum. The direction is
reversed from the suprema of `lub_mono` above, which run the expected way. -/
theorem glb_mono {S T : alpha -> Prop} {s t : alpha}
    (hST : forall x : alpha, S x -> T x)
    (hs : IsGreatestLowerBound F.le S s)
    (ht : IsGreatestLowerBound F.le T t) :
    F.le t s :=
  hs.right t (lowerBound_mono F hST ht.left)

theorem lub_of_greatest {S : alpha -> Prop} {m : alpha}
    (hm : S m)
    (hmax : forall x : alpha, S x -> F.le x m) :
    IsLeastUpperBound F.le S m := by
  constructor
  · exact hmax
  · intro u hu
    exact hu m hm

theorem glb_of_least {S : alpha -> Prop} {m : alpha}
    (hm : S m)
    (hmin : forall x : alpha, S x -> F.le m x) :
    IsGreatestLowerBound F.le S m := by
  constructor
  · exact hmin
  · intro l hl
    exact hl m hm

theorem lub_singleton (x : alpha) :
    IsLeastUpperBound F.le (fun y : alpha => y = x) x := by
  apply lub_of_greatest F
  · rfl
  · intro y hy
    rw [hy]
    exact F.le_refl x

theorem glb_singleton (x : alpha) :
    IsGreatestLowerBound F.le (fun y : alpha => y = x) x := by
  apply glb_of_least F
  · rfl
  · intro y hy
    rw [hy]
    exact F.le_refl x

/-- The least upper bound of the two-point set `{x, y}` is the binary maximum
`max2`, so the case-defined lattice maximum and the order-theoretic supremum
agree on pairs. -/
theorem lub_pair_max2 (x y : alpha) :
    IsLeastUpperBound F.le
      (fun z : alpha => Or (z = x) (z = y))
      (max2 F x y) := by
  apply lub_of_greatest F
  · unfold max2
    by_cases hxy : F.le x y
    · simp [hxy]
    · simp [hxy]
  · intro z hz
    cases hz with
    | inl hx =>
        rw [hx]
        exact le_max2_left F x y
    | inr hy =>
        rw [hy]
        exact le_max2_right F x y

/-- The mirror of `lub_pair_max2`: the greatest lower bound of a two-point
set is the binary minimum `min2`. -/
theorem glb_pair_min2 (x y : alpha) :
    IsGreatestLowerBound F.le
      (fun z : alpha => Or (z = x) (z = y))
      (min2 F x y) := by
  apply glb_of_least F
  · unfold min2
    by_cases hxy : F.le x y
    · simp [hxy]
    · simp [hxy]
  · intro z hz
    cases hz with
    | inl hx =>
        rw [hx]
        exact min2_le_left F x y
    | inr hy =>
        rw [hy]
        exact min2_le_right F x y

end IsOrderedFieldBaseLike
end Tautology
