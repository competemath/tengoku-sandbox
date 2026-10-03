import Tengoku.Tautology.Tautology.RealBootstrap.StrictOrder

/-!
# Least upper bounds, greatest lower bounds, and where completeness enters

Two layers in one file. The ordered-field layer adds the lower-bound half of
the vocabulary to the upper-bound half that `Foundation` already provides, and
proves what bounds satisfy in any ordered field: uniqueness, the defining
inequalities, and the approximation property that anything below a least upper
bound is below some member of the set.

The complete-field layer is two theorems, and they are the narrowest point in
the whole library. `exists_lub` unwraps the bundle's completeness field;
`exists_glb` is *derived* from it, by taking the least upper bound of the set
of lower bounds. Everything in this library that uses completeness -- the
Archimedean property, the whole completeness route graph of
`RealSequence/Principles/`, compactness, connectedness, the integral -- reaches
it through one of these two.

That asymmetry is worth carrying: the bundle assumes suprema only, so every
symmetric-looking statement about infima in this library is symmetric only
after `exists_glb`.

## Position and role

Implementation module. The ordered-field half is available everywhere; the
complete half is the interface to the valve room's completeness.
-/

namespace Tautology

/-- A lower bound of `S` under an arbitrary binary relation: l lies below
every member. The mirror of `Foundation.OrderField.IsUpperBound`, which is
imported from the Foundation level; the lower-bound half of the vocabulary
is defined here. -/
def IsLowerBound {alpha : Type}
    (le : alpha -> alpha -> Prop) (S : alpha -> Prop) (l : alpha) :
    Prop :=
  forall x, S x -> le l x

/-- The infimum side of the order vocabulary: a lower bound that dominates
every other lower bound, over an arbitrary binary relation. The mirror of
`Foundation.OrderField.IsLeastUpperBound`. -/
def IsGreatestLowerBound {alpha : Type}
    (le : alpha -> alpha -> Prop) (S : alpha -> Prop) (s : alpha) :
    Prop :=
  And (IsLowerBound le S s)
    (forall l, IsLowerBound le S l -> le l s)

namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem exists_lt_of_not_lowerBound
    {S : alpha -> Prop} {x : alpha}
    (hx : Not (IsLowerBound F.le S x)) :
    Exists (fun y : alpha => And (S y) (F.lt y x)) := by
  classical
  by_cases h :
      Exists (fun y : alpha => And (S y) (F.lt y x))
  · exact h
  · have hlower : IsLowerBound F.le S x := by
      intro y hy
      by_cases hxy : F.le x y
      · exact hxy
      · cases F.le_total y x with
        | inl hyx =>
            exact False.elim
              (h (Exists.intro y
                (And.intro hy (lt_of_le_of_not_le F hyx hxy))))
        | inr hxy' => exact False.elim (hxy hxy')
    exact False.elim (hx hlower)

theorem exists_gt_of_not_upperBound
    {S : alpha -> Prop} {x : alpha}
    (hx : Not (IsUpperBound F.le S x)) :
    Exists (fun y : alpha => And (S y) (F.lt x y)) := by
  classical
  by_cases h :
      Exists (fun y : alpha => And (S y) (F.lt x y))
  · exact h
  · have hupper : IsUpperBound F.le S x := by
      intro y hy
      by_cases hyx : F.le y x
      · exact hyx
      · cases F.le_total x y with
        | inl hxy =>
            exact False.elim
              (h (Exists.intro y
                (And.intro hy (lt_of_le_of_not_le F hxy hyx))))
        | inr hyx' => exact False.elim (hyx hyx')
    exact False.elim (hx hupper)

theorem lub_unique {S : alpha -> Prop} {s t : alpha}
    (hs : IsLeastUpperBound F.le S s)
    (ht : IsLeastUpperBound F.le S t) :
    s = t :=
  F.le_antisymm (hs.right t ht.left) (ht.right s hs.left)

theorem le_lub_of_mem {S : alpha -> Prop} {s x : alpha}
    (hs : IsLeastUpperBound F.le S s)
    (hx : S x) :
    F.le x s :=
  hs.left x hx

theorem lub_le_of_upper {S : alpha -> Prop} {s u : alpha}
    (hs : IsLeastUpperBound F.le S s)
    (hu : IsUpperBound F.le S u) :
    F.le s u :=
  hs.right u hu

/-- The approximation property of a least upper bound: anything strictly below
it is strictly below some member of the set. Stated in this contrapositive form
because that is how it is used -- to produce a witness from a failed bound --
and proved classically rather than by an epsilon. -/
theorem exists_lt_of_lt_lub {S : alpha -> Prop} {s t : alpha}
    (hs : IsLeastUpperBound F.le S s)
    (hts : F.lt t s) :
    Exists (fun x => And (S x) (F.lt t x)) := by
  by_cases hex : Exists (fun x => And (S x) (F.lt t x))
  · exact hex
  · have htUpper : IsUpperBound F.le S t := by
      intro x hxS
      by_cases hxt : F.le x t
      · exact hxt
      · cases F.le_total t x with
        | inl htx =>
            have htxlt : F.lt t x := lt_of_le_of_not_le F htx hxt
            exact False.elim
              (hex (Exists.intro x (And.intro hxS htxlt)))
        | inr hxt' =>
            exact hxt'
    have hst : F.le s t := hs.right t htUpper
    exact False.elim ((not_le_of_lt F hts) hst)

theorem glb_unique {S : alpha -> Prop} {s t : alpha}
    (hs : IsGreatestLowerBound F.le S s)
    (ht : IsGreatestLowerBound F.le S t) :
    s = t :=
  F.le_antisymm (ht.right s hs.left) (hs.right t ht.left)

theorem glb_le_of_mem {S : alpha -> Prop} {s x : alpha}
    (hs : IsGreatestLowerBound F.le S s)
    (hx : S x) :
    F.le s x :=
  hs.left x hx

theorem le_glb_of_lower {S : alpha -> Prop} {s l : alpha}
    (hs : IsGreatestLowerBound F.le S s)
    (hl : IsLowerBound F.le S l) :
    F.le l s :=
  hs.right l hl

/-- The approximation property on the infimum side: anything strictly above a
greatest lower bound is strictly above some member of the set. The mirror of
`exists_lt_of_lt_lub` above, used the same way -- to produce a member from a
failed bound -- and proved classically rather than by an epsilon. -/
theorem exists_gt_of_glb_lt {S : alpha -> Prop} {s t : alpha}
    (hs : IsGreatestLowerBound F.le S s)
    (hst : F.lt s t) :
    Exists (fun x => And (S x) (F.lt x t)) := by
  by_cases hex : Exists (fun x => And (S x) (F.lt x t))
  · exact hex
  · have htLower : IsLowerBound F.le S t := by
      intro x hxS
      by_cases htx : F.le t x
      · exact htx
      · cases F.le_total x t with
        | inl hxt =>
            have hxtlt : F.lt x t := lt_of_le_of_not_le F hxt htx
            exact False.elim
              (hex (Exists.intro x (And.intro hxS hxtlt)))
        | inr htx' =>
            exact htx'
    have hts : F.le t s := hs.right t htLower
    exact False.elim ((not_le_of_lt F hst) hts)

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The supremum property itself, unwrapped from the bundle: a nonempty set
bounded above has a least upper bound. This is the single point at which
Dedekind completeness leaves the valve room -- the entire library's use of
completeness, including every principle of the completeness route graph in
`RealSequence/Principles/`, is ultimately a call to this theorem or to
`exists_glb` beside it. -/
theorem exists_lub (S : alpha -> Prop)
    (hne : Exists S)
    (hbdd : Exists (IsUpperBound C.field.le S)) :
    Exists (fun s => IsLeastUpperBound C.field.le S s) :=
  C.complete.exists_lub S hne hbdd

/-- The infimum property, and it is *derived*, not assumed: the bundle carries
only a supremum field, so the greatest lower bound of a set is obtained as the
least upper bound of its set of lower bounds. Anything that looks symmetric
between suprema and infima in this library is symmetric only after
this theorem. -/
theorem exists_glb (S : alpha -> Prop)
    (hne : Exists S)
    (hbdd : Exists (IsLowerBound C.field.le S)) :
    Exists (fun s => IsGreatestLowerBound C.field.le S s) := by
  let L : alpha -> Prop := fun l => IsLowerBound C.field.le S l
  have hL_nonempty : Exists L := hbdd
  have hL_bounded : Exists (IsUpperBound C.field.le L) := by
    cases hne with
    | intro x hx =>
        refine Exists.intro x ?_
        intro l hl
        exact hl x hx
  cases C.complete.exists_lub L hL_nonempty hL_bounded with
  | intro s hs =>
      refine Exists.intro s ?_
      constructor
      · intro x hx
        apply hs.right x
        intro l hl
        exact hl x hx
      · intro l hl
        exact hs.left l hl

end IsDedekindCompleteOrderedFieldBaseLike

end Tautology
