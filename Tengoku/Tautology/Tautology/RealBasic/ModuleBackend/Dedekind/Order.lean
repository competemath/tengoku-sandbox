module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Basic

/-!
# The order on cuts, and completeness

Order is inclusion: one cut is below another when its member set is contained
in the other's. That makes the order relation free of arithmetic, and it makes
completeness nearly free as well -- the supremum of a family of cuts is the
union of their member sets, which is again a cut.

**This is the reason the Dedekind construction is the one selected.** In the
other two backends completeness is the hardest theorem; here it is almost the
definition, and the work moves instead into the field operations, which are
awkward precisely because inclusion says nothing about products. The three
constructions trade the same difficulty around, and this file is where the
Dedekind side of that trade is visible.

## Position in the development

Above `Dedekind.Basic`. The arithmetic files come after and have to respect
the order established here.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind

namespace Cut

instance : LE Cut where
  le x y := forall q : Rat, x.mem q -> y.mem q

instance : LT Cut where
  lt x y := And (x <= y) (Not (y <= x))

theorem le_refl (x : Cut) : x <= x := by
  intro q hq
  exact hq

theorem le_trans {x y z : Cut} (hxy : x <= y) (hyz : y <= z) :
    x <= z := by
  intro q hxq
  exact hyz q (hxy q hxq)

theorem le_antisymm {x y : Cut} (hxy : x <= y) (hyx : y <= x) :
    x = y := by
  apply Cut.ext
  intro q
  constructor
  · intro hxq
    exact hxy q hxq
  · intro hyq
    exact hyx q hyq

/-- Inclusion of cuts is total. Two arbitrary predicates on the rationals can
be incomparable, so the cut structure has to be used: from a rational lying
in `x` but not in `y`, downward closure of `y` forces every member of `y` to
stay below it, which gives `y <= x`. -/
theorem le_total (x y : Cut) : Or (x <= y) (y <= x) := by
  by_cases hxy : x <= y
  · exact Or.inl hxy
  · apply Or.inr
    have hnot : Not (forall q : Rat, x.mem q -> y.mem q) := hxy
    cases Classical.not_forall.mp hnot with
    | intro a ha_not_imp =>
        have ha_pair : And (x.mem a) (Not (y.mem a)) :=
          Classical.not_imp.mp ha_not_imp
        intro b hyb
        cases _root_.Rat.le_total (a := b) (b := a) with
        | inl hba =>
            cases _root_.Rat.le_iff_lt_or_eq.mp hba with
            | inl hb_lt_a =>
                exact x.downward hb_lt_a ha_pair.left
            | inr hb_eq_a =>
                rw [hb_eq_a]
                exact ha_pair.left
        | inr hab =>
            have hya : y.mem a := by
              cases _root_.Rat.le_iff_lt_or_eq.mp hab with
              | inl ha_lt_b =>
                  exact y.downward ha_lt_b hyb
              | inr ha_eq_b =>
                  rw [ha_eq_b]
                  exact hyb
            exact False.elim (ha_pair.right hya)

theorem lt_of_le_of_not_le {x y : Cut}
    (hxy : x <= y) (hyx : Not (y <= x)) :
    x < y :=
  And.intro hxy hyx

theorem lt_irrefl (x : Cut) : Not (x < x) := by
  intro hxx
  exact hxx.right hxx.left

theorem le_cases {x y : Cut} (hxy : x <= y) : Or (x < y) (x = y) := by
  by_cases hyx : y <= x
  · exact Or.inr (le_antisymm hxy hyx)
  · exact Or.inl (lt_of_le_of_not_le hxy hyx)

theorem lt_eq_gt (x y : Cut) : Or (x < y) (Or (x = y) (y < x)) := by
  cases le_total x y with
  | inl hxy =>
      cases le_cases hxy with
      | inl hlt =>
          exact Or.inl hlt
      | inr heq =>
          exact Or.inr (Or.inl heq)
  | inr hyx =>
      cases le_cases hyx with
      | inl hlt =>
          exact Or.inr (Or.inr hlt)
      | inr heq =>
          exact Or.inr (Or.inl heq.symm)

/-- `u` is an upper bound of `S` when every member of `S` is included in it.
Together with `IsLeastUpperBound`, this is the vocabulary in which the
completeness of the backend is stated. -/
def IsUpperBound (S : Cut -> Prop) (u : Cut) : Prop :=
  forall x : Cut, S x -> x <= u

/-- `s` is the least upper bound of `S`: an upper bound that is included in
every other upper bound. Since the order is inclusion, both halves are
containment statements between member sets. -/
def IsLeastUpperBound (S : Cut -> Prop) (s : Cut) : Prop :=
  And (IsUpperBound S s) (forall u : Cut, IsUpperBound S u -> s <= u)

/-- The supremum of a nonempty family of cuts that has an upper bound: the
union of the member sets. Downward closure and the absence of a greatest
element are inherited from the members, and properness comes from the assumed
upper bound. This definition is where the completeness of the backend is
proved. -/
def sup (S : Cut -> Prop) (hne : Exists S)
    (hbdd : Exists (IsUpperBound S)) :
    Cut where
  mem q := Exists (fun x : Cut => And (S x) (x.mem q))
  nonempty := by
    cases hne with
    | intro x hxS =>
        cases x.nonempty with
        | intro q hxq =>
            exact Exists.intro q (Exists.intro x (And.intro hxS hxq))
  proper := by
    cases hbdd with
    | intro u hu =>
        cases u.proper with
        | intro q hqu =>
            refine Exists.intro q ?_
            intro hq
            cases hq with
            | intro x hx =>
                exact hqu (hu x hx.left q hx.right)
  downward := by
    intro p q hpq hq
    cases hq with
    | intro x hx =>
        exact Exists.intro x (And.intro hx.left (x.downward hpq hx.right))
  no_greatest := by
    intro q hq
    cases hq with
    | intro x hx =>
        cases x.no_greatest hx.right with
        | intro r hr =>
            exact Exists.intro r
              (And.intro (Exists.intro x (And.intro hx.left hr.left))
                hr.right)

theorem sup_isUpperBound {S : Cut -> Prop} {hne : Exists S}
    {hbdd : Exists (IsUpperBound S)} :
    IsUpperBound S (sup S hne hbdd) := by
  intro x hxS q hxq
  exact Exists.intro x (And.intro hxS hxq)

theorem sup_least {S : Cut -> Prop} {hne : Exists S}
    {hbdd : Exists (IsUpperBound S)} {u : Cut}
    (hu : IsUpperBound S u) :
    sup S hne hbdd <= u := by
  intro q hq
  cases hq with
  | intro x hx =>
      exact hu x hx.left q hx.right

theorem sup_isLeastUpperBound {S : Cut -> Prop} {hne : Exists S}
    {hbdd : Exists (IsUpperBound S)} :
    IsLeastUpperBound S (sup S hne hbdd) := by
  constructor
  · exact sup_isUpperBound
  · intro u hu
    exact sup_least hu

/-- Every nonempty family of cuts with an upper bound has a least upper
bound. This is the least-upper-bound statement that `selection` in
`Dedekind.Selection` installs as the completeness half of this backend's
offering. -/
theorem exists_lub (S : Cut -> Prop) (hne : Exists S)
    (hbdd : Exists (IsUpperBound S)) :
    Exists (fun s : Cut => IsLeastUpperBound S s) :=
  Exists.intro (sup S hne hbdd) sup_isLeastUpperBound

end Cut

end Dedekind
end ModuleBackend
end RealBasic
end Tautology
