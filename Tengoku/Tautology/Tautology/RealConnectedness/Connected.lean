import Tengoku.Tautology.Tautology.RealTopology.Subspace
import Tengoku.Tautology.Tautology.RealTopology.Intervals
import Tengoku.Tautology.Tautology.RealBootstrap.Supremum
import Tengoku.Tautology.Tautology.RealSequence.Algebra

/-!
# Connected subsets of an ordered field are exactly its interval sets

The theorem this whole region is built on: over a Dedekind-complete ordered
field, a set is connected precisely when it is an interval set, meaning it
contains every point lying between two of its points
(`connected_iff_intervalSet`). The file fixes both sides of that equivalence --
the separation vocabulary `CoversByTwo`, `IsSeparation`, `IsConnected` and the
order vocabulary `Between`, `IsIntervalSet` -- proves the equivalence, and
reads off the connectedness of the concrete shapes: the whole line, the empty
set, singletons, open and closed intervals, and the four rays.

## The two directions are not the same depth

That a connected set is an interval set holds over any ordered field: if a
point between two members were missing, the members below and above it would
cut the set in two, and both pieces are relatively open. The converse is where
completeness is spent. Given a separation with `a` in one piece and `b` in the
other, take the supremum of the part of `[a, b]` lying in the first piece;
interval-ness puts that supremum back in the set, and then relative openness at
that point contradicts its own minimality, whichever piece it landed in. That
is `not_separation_of_interval_ordered_points`, and the only appeal to
completeness in this file -- `exists_lub` from
`Tautology.RealBootstrap.Supremum`, plus its companions -- happens inside it.

The split shows up in the file layout: the `IsOrderedFieldBaseLike` half needs
no completeness, the `IsDedekindCompleteOrderedFieldBaseLike` half does. Two
consequences worth not misreading. `connected_empty` is proved in the first
half, because `IsSeparation` demands two nonempty pieces and so a set with
nothing to split is connected by definition. But `connected_singleton` and
`connected_universal` are proved in the second half, through the hard
direction; their interval-ness is trivial in any ordered field, their
connectedness in this development is not.

## Position and role

Implementation module, the base of `RealConnectedness`, which sits above
`RealTopology` and below `RealCompactness` in the library's dependency order.
It consumes the relative-topology vocabulary of
`Tautology.RealTopology.Subspace`, the interval and ray vocabulary of
`Tautology.RealTopology.Intervals`, and the supremum interface of
`Tautology.RealBootstrap.Supremum`. Its three sibling modules build on it, and
`Tautology.RealTheory.Topology` specialises the results to the selected carrier
-- that facade is the region's only consumer inside the library.

Everything is stated over bundled structures passed as explicit parameters
(`(F : IsOrderedFieldBaseLike alpha)` and `(C : ...)`), since the project uses
no typeclasses. Nothing here is about the real line as this library constructs
it. Note that `abbrev F` in the complete half is not a new object: it is a
shorthand for `C.field`, letting the ordered-field vocabulary above be applied
to a complete field without spelling out the projection.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- `S` is the union of `U` and `V`, stated as an equality of predicates: the
two pieces cover all of `S` and neither reaches outside it. Mere containment
would not do, because a separation has to exhaust the set it splits. -/
def CoversByTwo (S U V : alpha -> Prop) : Prop :=
  SetPred.Same S (SetPred.Union U V)

/-- A separation of `S`: two nonempty, disjoint sets, each open in `S`, whose
union is exactly `S`. Both pieces are demanded nonempty, so one-point sets
and the empty set have no separation at all and count as connected. -/
def IsSeparation (S U V : alpha -> Prop) : Prop :=
  And (OpenIn F S U)
    (And (OpenIn F S V)
      (And (SetPred.Nonempty U)
        (And (SetPred.Nonempty V)
          (And (CoversByTwo S U V)
            (SetPred.Disjoint U V)))))

/-- `S` is connected: no two sets separate it. The definition negates an
existence statement, so a proof of connectedness argues against an arbitrary
putative split -- the shape every argument below takes. -/
def IsConnected (S : alpha -> Prop) : Prop :=
  forall U V : alpha -> Prop, Not (IsSeparation F S U V)

/-- `y` lies weakly between `x` and `z`: `x ≤ y` and `y ≤ z`, either
comparison allowed to be equality. `IsIntervalSet` is phrased through this
three-point relation. -/
def Between (x y z : alpha) : Prop :=
  And (F.le x y) (F.le y z)

/-- `S` is an interval in the order sense: whenever it contains `x` and `z`
and `y` lies between them, it contains `y` as well. Only the order enters
here; that this property coincides with connectedness over a complete field
is the file's main result. -/
def IsIntervalSet (S : alpha -> Prop) : Prop :=
  forall x y z : alpha,
    S x -> S z -> Between F x y z -> S y

/-- Two distinct points of an ordered field are comparable: `x < y` or
`y < x`. The proof extracts this from weak totality `le_total`, discarding
the equality case with `le_antisymm`. -/
theorem lt_or_gt_of_ne {x y : alpha}
    (hxy : Not (x = y)) :
    Or (F.lt x y) (F.lt y x) := by
  cases F.le_total x y with
  | inl hle_xy =>
      by_cases hle_yx : F.le y x
      · exact False.elim (hxy (F.le_antisymm hle_xy hle_yx))
      · exact Or.inl (lt_of_le_of_not_le F hle_xy hle_yx)
  | inr hle_yx =>
      by_cases hle_xy : F.le x y
      · exact False.elim (hxy (F.le_antisymm hle_xy hle_yx))
      · exact Or.inr (lt_of_le_of_not_le F hle_yx hle_xy)

/-- Given two points strictly right of `x`, there is a third one, `d`, still
strictly right of `x`, at most `y`, and strictly below `z`. The witness is a
midpoint -- of `x` and `y`, or of `x` and `z`, according to which of `y`,
`z` is larger. The completeness argument below uses it with `y` the far end
of a section and `z` the right edge of an open ball around a supremum, so
that `d` lands in the ball without leaving the section. -/
theorem exists_right_between {x y z : alpha}
    (hxy : F.lt x y) (hxz : F.lt x z) :
    Exists
      (fun d : alpha =>
        And (F.lt x d) (And (F.le d y) (F.lt d z))) := by
  by_cases hyz : F.le y z
  · refine Exists.intro (midpoint F x y) ?_
    exact
      And.intro (left_lt_midpoint F hxy)
        (And.intro
          (midpoint_le_right F (le_of_lt F hxy))
          (lt_of_lt_of_le F (midpoint_lt_right F hxy) hyz))
  · have hzy : F.le z y := by
      cases F.le_total z y with
      | inl h => exact h
      | inr h => exact False.elim (hyz h)
    refine Exists.intro (midpoint F x z) ?_
    exact
      And.intro (left_lt_midpoint F hxz)
        (And.intro
          (F.le_trans (midpoint_le_right F (le_of_lt F hxz)) hzy)
          (midpoint_lt_right F hxz))

/-- The two pieces of a separation are interchangeable. The completeness
lemma below is stated with the `U`-witness strictly left of the `V`-witness,
while the witnesses of an arbitrary separation may come in either order, so
the mirrored case is reduced to this one. -/
theorem isSeparation_symm {S U V : alpha -> Prop}
    (hsep : IsSeparation F S U V) :
    IsSeparation F S V U := by
  refine And.intro hsep.right.left ?_
  refine And.intro hsep.left ?_
  refine And.intro hsep.right.right.right.left ?_
  refine And.intro hsep.right.right.left ?_
  refine And.intro ?_ ?_
  · intro x
    constructor
    · intro hxS
      cases (hsep.right.right.right.right.left x).mp hxS with
      | inl hxU => exact Or.inr hxU
      | inr hxV => exact Or.inl hxV
    · intro hxVU
      cases hxVU with
      | inl hxV =>
          exact (hsep.right.right.right.right.left x).mpr (Or.inr hxV)
      | inr hxU =>
          exact (hsep.right.right.right.right.left x).mpr (Or.inl hxU)
  · intro x hxV hxU
    exact hsep.right.right.right.right.right x hxU hxV

/-- The empty set is connected. A separation needs a nonempty piece, and a
piece open in `S` is contained in `S`, which here has no point to give it. -/
theorem connected_empty :
    IsConnected F (SetPred.Empty : alpha -> Prop) := by
  intro U V hsep
  cases hsep.right.right.left with
  | intro x hxU =>
      exact openIn_subset F hsep.left x hxU

/-- The empty set is an interval set: the hypothesis `S x` is vacuous, so
there is no between-witness to produce. -/
theorem intervalSet_empty :
    IsIntervalSet F (SetPred.Empty : alpha -> Prop) := by
  intro x y z hx hz hbetween
  exact False.elim hx

/-- The whole space is an interval set, every point serving as a
between-witness. Turning this into connectedness of the whole line is
exactly the step that spends completeness, in `connected_universal` below. -/
theorem intervalSet_universal :
    IsIntervalSet F (SetPred.Universal : alpha -> Prop) := by
  intro x y z hx hz hbetween
  exact True.intro

/-- A one-point set is an interval set: between the point and itself only
the point can lie, which is all `le_antisymm` has to return. -/
theorem intervalSet_singleton (a : alpha) :
    IsIntervalSet F (SetPred.Singleton a) := by
  intro x y z hx hz hbetween
  rw [hx] at hbetween
  rw [hz] at hbetween
  exact F.le_antisymm hbetween.right hbetween.left

/-- An open interval is an interval set, whatever its endpoints: a point
squeezed between two of its points stays strictly inside. -/
theorem intervalSet_openInterval (left right : alpha) :
    IsIntervalSet F (OpenInterval F left right) := by
  intro x y z hx hz hbetween
  exact
    And.intro
      (lt_of_lt_of_le F hx.left hbetween.left)
      (lt_of_le_of_lt F hbetween.right hz.right)

/-- A closed interval is an interval set, whatever its endpoints, the
one-point case included. -/
theorem intervalSet_closedInterval (left right : alpha) :
    IsIntervalSet F (ClosedInterval F left right) := by
  intro x y z hx hz hbetween
  exact
    And.intro
      (F.le_trans hx.left hbetween.left)
      (F.le_trans hbetween.right hz.right)

/-- An open lower ray is an interval set: a point between two points
strictly below the cut is itself strictly below it. -/
theorem intervalSet_openLowerRay (cut : alpha) :
    IsIntervalSet F (OpenLowerRay F cut) := by
  intro x y z hx hz hbetween
  exact lt_of_le_of_lt F hbetween.right hz

/-- An open upper ray is an interval set, the mirror of the lower-ray case. -/
theorem intervalSet_openUpperRay (cut : alpha) :
    IsIntervalSet F (OpenUpperRay F cut) := by
  intro x y z hx hz hbetween
  exact lt_of_lt_of_le F hx hbetween.left

/-- A closed lower ray is an interval set: betweenness composes with the cut
bound by transitivity of `le`. -/
theorem intervalSet_closedLowerRay (cut : alpha) :
    IsIntervalSet F (ClosedLowerRay F cut) := by
  intro x y z hx hz hbetween
  exact F.le_trans hbetween.right hz

/-- A closed upper ray is an interval set, the mirror of the closed
lower-ray case. -/
theorem intervalSet_closedUpperRay (cut : alpha) :
    IsIntervalSet F (ClosedUpperRay F cut) := by
  intro x y z hx hz hbetween
  exact F.le_trans hx hbetween.left

/-- A connected set is an interval set, over any ordered field. If a
between-point `y` of two points `x`, `z` of `S` were missing, the parts of
`S` strictly below and strictly above `y` would be traces of open rays,
hence open in `S`, nonempty at `x` and `z`, disjoint, and exhaustive -- a
separation. Completeness is needed only for the converse. -/
theorem intervalSet_of_connected {S : alpha -> Prop}
    (hconn : IsConnected F S) :
    IsIntervalSet F S := by
  intro x y z hx hz hbetween
  classical
  by_cases hyS : S y
  · exact hyS
  · have hxy_ne : Not (x = y) := by
      intro hxy
      rw [hxy] at hx
      exact hyS hx
    have hyz_ne : Not (y = z) := by
      intro hyz
      rw [<- hyz] at hz
      exact hyS hz
    have hnot_yx : Not (F.le y x) := by
      intro hyx
      exact hxy_ne (F.le_antisymm hbetween.left hyx)
    have hnot_zy : Not (F.le z y) := by
      intro hzy
      exact hyz_ne (F.le_antisymm hbetween.right hzy)
    have hxy_lt : F.lt x y :=
      lt_of_le_of_not_le F hbetween.left hnot_yx
    have hyz_lt : F.lt y z :=
      lt_of_le_of_not_le F hbetween.right hnot_zy
    let U : alpha -> Prop := Trace S (OpenLowerRay F y)
    let V : alpha -> Prop := Trace S (OpenUpperRay F y)
    have hsep : IsSeparation F S U V := by
      refine And.intro
        (openIn_trace F (S := S) (openLowerRay_isOpen F y)) ?_
      refine And.intro
        (openIn_trace F (S := S) (openUpperRay_isOpen F y)) ?_
      refine And.intro ?_ ?_
      · exact Exists.intro x (And.intro hx hxy_lt)
      · refine And.intro ?_ ?_
        · exact Exists.intro z (And.intro hz hyz_lt)
        · refine And.intro ?_ ?_
          · intro t
            constructor
            · intro htS
              have hty_ne : Not (t = y) := by
                intro hty
                rw [hty] at htS
                exact hyS htS
              cases lt_or_gt_of_ne F hty_ne with
              | inl hty =>
                  exact Or.inl (And.intro htS hty)
              | inr hyt =>
                  exact Or.inr (And.intro htS hyt)
            · intro htUV
              cases htUV with
              | inl htU => exact htU.left
              | inr htV => exact htV.left
          · intro t htU htV
            exact (lt_asymm F htU.right) htV.right
    exact False.elim (hconn U V hsep)

/-- Connectedness in clopen form: `S` is connected exactly when every subset
both open and closed in `S` is empty or all of `S`. One direction splits `S`
into a clopen piece and its relative complement; the other reads a
separation as one piece together with the complement of the other. Pure
order reasoning, no completeness. -/
theorem connected_iff_clopen_trivial {S : alpha -> Prop} :
    IsConnected F S <->
      forall U : alpha -> Prop,
        ClopenIn F S U ->
          Or (forall x : alpha, Not (U x)) (SetPred.Same U S) := by
  constructor
  · intro hconn U hclopen
    classical
    by_cases hneU : SetPred.Nonempty U
    · by_cases hsameUS : SetPred.Same U S
      · exact Or.inr hsameUS
      · have hnonemptyDiff : SetPred.Nonempty (SetPred.Diff S U) := by
          by_cases hsubSU : SetPred.Subset S U
          · have hsame : SetPred.Same U S := by
              intro x
              constructor
              · intro hxU
                exact openIn_subset F hclopen.left x hxU
              · intro hxS
                exact hsubSU x hxS
            exact False.elim (hsameUS hsame)
          · by_cases hex :
                Exists (fun x : alpha => And (S x) (Not (U x)))
            · exact hex
            · exact False.elim
                (hsubSU
                  (fun x hxS =>
                    by
                      by_cases hxU : U x
                      · exact hxU
                      · exact False.elim
                          (hex (Exists.intro x (And.intro hxS hxU)))))
        have hdiffOpen : OpenIn F S (SetPred.Diff S U) :=
          relativeOpen_diff_of_relativeClosed F hclopen.right
        have hsep : IsSeparation F S U (SetPred.Diff S U) := by
          refine And.intro hclopen.left ?_
          refine And.intro hdiffOpen ?_
          refine And.intro hneU ?_
          refine And.intro hnonemptyDiff ?_
          refine And.intro ?_ ?_
          · intro x
            constructor
            · intro hxS
              by_cases hxU : U x
              · exact Or.inl hxU
              · exact Or.inr (And.intro hxS hxU)
            · intro hx
              cases hx with
              | inl hxU => exact openIn_subset F hclopen.left x hxU
              | inr hxD => exact hxD.left
          · intro x hxU hxD
            exact hxD.right hxU
        exact False.elim (hconn U (SetPred.Diff S U) hsep)
    · exact Or.inl (fun x hxU => hneU (Exists.intro x hxU))
  · intro htrivial U V hsep
    have hVdiffSame : SetPred.Same V (SetPred.Diff S U) := by
      intro x
      constructor
      · intro hxV
        exact And.intro
          (openIn_subset F hsep.right.left x hxV)
          (fun hxU => hsep.right.right.right.right.right x hxU hxV)
      · intro hxD
        cases (hsep.right.right.right.right.left x).mp hxD.left with
        | inl hxU => exact False.elim (hxD.right hxU)
        | inr hxV => exact hxV
    have hdiffOpen : OpenIn F S (SetPred.Diff S U) :=
      relativeOpen_congr F hsep.right.left hVdiffSame
    have hclosedU : ClosedIn F S U :=
      relativeClosed_of_diff_relativeOpen F
        (openIn_subset F hsep.left) hdiffOpen
    have hclopenU : ClopenIn F S U :=
      And.intro hsep.left hclosedU
    cases htrivial U hclopenU with
    | inl hempty =>
        cases hsep.right.right.left with
        | intro x hxU => exact hempty x hxU
    | inr hsame =>
        cases hsep.right.right.right.left with
        | intro x hxV =>
            have hxS : S x := openIn_subset F hsep.right.left x hxV
            have hxU : U x := (hsame x).mpr hxS
            exact hsep.right.right.right.right.right x hxU hxV

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- Notation, not a mathematical object: `F C` is the underlying ordered
field of the complete field `C`, there so that the ordered-field results and
vocabulary above apply to `C` without unfolding `C.field` at every use. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The completeness step of the file: an interval set admits no separation
whose `U`-witness lies strictly left of its `V`-witness. The members of `U`
in the section from `a` to `b` form a nonempty set bounded above by `b`, so
they have a least upper bound `s`, which interval-ness returns to `S`. If
`s` lies in `U`, openness produces a section member strictly past `s`,
against its being an upper bound -- unless `s = b`, which already puts `b`
in both pieces. If `s` lies in `V`, openness reaches strictly below `s`, and
leastness places a section member inside that reach, against disjointness. -/
theorem not_separation_of_interval_ordered_points
    {S U V : alpha -> Prop} {a b : alpha}
    (hinterval : (F C).IsIntervalSet S)
    (hsep : (F C).IsSeparation S U V)
    (ha : U a)
    (hb : V b)
    (hab : (F C).lt a b) :
    False := by
  have hUS : SetPred.Subset U S :=
    IsOrderedFieldBaseLike.openIn_subset (F C) hsep.left
  have hVS : SetPred.Subset V S :=
    IsOrderedFieldBaseLike.openIn_subset (F C) hsep.right.left
  have haS : S a := hUS a ha
  have hbS : S b := hVS b hb
  let A : alpha -> Prop :=
    fun t =>
      And (S t)
        (And ((F C).le a t)
          (And ((F C).le t b) (U t)))
  have haA : A a := by
    exact
      And.intro haS
        (And.intro ((F C).le_refl a)
          (And.intro
            (IsOrderedFieldBaseLike.le_of_lt (F C) hab)
            ha))
  have hnonempty : Exists A := Exists.intro a haA
  have hb_upper : IsUpperBound (F C).le A b := by
    intro t ht
    exact ht.right.right.left
  have hbdd : Exists (IsUpperBound (F C).le A) := by
    exact Exists.intro b hb_upper
  cases C.exists_lub A hnonempty hbdd with
  | intro s hs =>
      have ha_s : (F C).le a s :=
        IsOrderedFieldBaseLike.le_lub_of_mem (F C) hs haA
      have hs_b : (F C).le s b :=
        IsOrderedFieldBaseLike.lub_le_of_upper (F C) hs hb_upper
      have hsS : S s :=
        hinterval a s b haS hbS (And.intro ha_s hs_b)
      cases (hsep.right.right.right.right.left s).mp hsS with
      | inl hsU =>
          by_cases hsb_eq : s = b
          · have hbU : U b := by
              rw [hsb_eq] at hsU
              exact hsU
            exact
              hsep.right.right.right.right.right b hbU hb
          · have hnot_bs : Not ((F C).le b s) := by
              intro hbs
              exact hsb_eq ((F C).le_antisymm hs_b hbs)
            have hs_lt_b : (F C).lt s b :=
              IsOrderedFieldBaseLike.lt_of_le_of_not_le (F C)
                hs_b hnot_bs
            cases hsep.left with
            | intro U0 hU0 =>
                have hsU0 : U0 s := ((hU0.right s).mp hsU).right
                cases hU0.left s hsU0 with
                | intro left hleft =>
                    cases hleft with
                    | intro right hright =>
                        cases IsOrderedFieldBaseLike.exists_right_between
                            (F C) hs_lt_b hright.right.left with
                        | intro d hd =>
                            have ha_d : (F C).le a d :=
                              (F C).le_trans ha_s
                                (IsOrderedFieldBaseLike.le_of_lt (F C)
                                  hd.left)
                            have hdS : S d :=
                              hinterval a d b haS hbS
                                (And.intro ha_d hd.right.left)
                            have hdU0 : U0 d :=
                              hright.right.right d
                                (And.intro
                                  (IsOrderedFieldBaseLike.lt_trans (F C)
                                    hright.left hd.left)
                                  hd.right.right)
                            have hdU : U d :=
                              ((hU0.right d).mpr (And.intro hdS hdU0))
                            have hdA : A d :=
                              And.intro hdS
                                (And.intro ha_d
                                  (And.intro hd.right.left hdU))
                            have hds : (F C).le d s := hs.left d hdA
                            exact
                              (IsOrderedFieldBaseLike.not_le_of_lt (F C)
                                hd.left) hds
      | inr hsV =>
          cases hsep.right.left with
          | intro V0 hV0 =>
              have hsV0 : V0 s := ((hV0.right s).mp hsV).right
              cases hV0.left s hsV0 with
              | intro left hleft =>
                  cases hleft with
                  | intro right hright =>
                      cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub
                          (F C) hs hright.left with
                      | intro d hd =>
                          have hdA : A d := hd.left
                          have hd_le_s : (F C).le d s :=
                            hs.left d hdA
                          have hd_lt_right : (F C).lt d right :=
                            IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
                              hd_le_s hright.right.left
                          have hdV0 : V0 d :=
                            hright.right.right d
                              (And.intro hd.right hd_lt_right)
                          have hdV : V d :=
                            ((hV0.right d).mpr
                              (And.intro hdA.left hdV0))
                          exact
                            hsep.right.right.right.right.right d
                              hdA.right.right.right hdV

/-- Over a Dedekind-complete field, every interval set is connected. The
witnesses of a putative separation are distinct by disjointness, hence
comparable, and one lies strictly left of the other; the preceding lemma
closes that case, and `isSeparation_symm` the mirrored one. -/
theorem connected_of_intervalSet {S : alpha -> Prop}
    (hinterval : (F C).IsIntervalSet S) :
    (F C).IsConnected S := by
  intro U V hsep
  cases hsep.right.right.left with
  | intro a ha =>
      cases hsep.right.right.right.left with
      | intro b hb =>
          have hab_ne : Not (a = b) := by
            intro hab_eq
            rw [hab_eq] at ha
            exact hsep.right.right.right.right.right b ha hb
          cases IsOrderedFieldBaseLike.lt_or_gt_of_ne (F C) hab_ne with
          | inl hab =>
              exact
                not_separation_of_interval_ordered_points C
                  hinterval hsep ha hb hab
          | inr hba =>
              exact
                not_separation_of_interval_ordered_points C
                  hinterval
                  (IsOrderedFieldBaseLike.isSeparation_symm (F C) hsep)
                  hb ha hba

/-- The main result: over a Dedekind-complete ordered field, the connected sets
are exactly the interval sets. The forward direction is the ordered-field
`intervalSet_of_connected`; the reverse runs through the least-upper-bound
property, which is what keeps it out of the namespace above.
`Tautology.RealTheory.Topology` specializes both directions to the selected
carrier. -/
theorem connected_iff_intervalSet {S : alpha -> Prop} :
    (F C).IsConnected S <-> (F C).IsIntervalSet S := by
  constructor
  · intro hconn
    exact IsOrderedFieldBaseLike.intervalSet_of_connected (F C) hconn
  · intro hinterval
    exact connected_of_intervalSet C hinterval

/-- The whole line is connected. Its being an interval set holds over any
ordered field, but this step is proved through completeness, via
`connected_of_intervalSet`. -/
theorem connected_universal :
    (F C).IsConnected (SetPred.Universal : alpha -> Prop) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_universal (F C))

/-- A one-point set is connected, straight from its being an interval set.
The empty case needed no completeness and was settled directly in the
ordered-field half above. -/
theorem connected_singleton (a : alpha) :
    (F C).IsConnected (SetPred.Singleton a) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_singleton (F C) a)

/-- An open interval is connected, whatever its endpoints, the empty case
included. -/
theorem connected_openInterval (left right : alpha) :
    (F C).IsConnected ((F C).OpenInterval left right) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_openInterval (F C) left right)

/-- A closed interval is connected, whatever its endpoints, one-point and
empty cases included. -/
theorem connected_closedInterval (left right : alpha) :
    (F C).IsConnected ((F C).ClosedInterval left right) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_closedInterval (F C) left right)

/-- An open lower ray is connected: the classification also covers the
unbounded shapes, with the cut arbitrary. -/
theorem connected_openLowerRay (cut : alpha) :
    (F C).IsConnected ((F C).OpenLowerRay cut) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_openLowerRay (F C) cut)

/-- An open upper ray is connected, the mirror of the open lower-ray case. -/
theorem connected_openUpperRay (cut : alpha) :
    (F C).IsConnected ((F C).OpenUpperRay cut) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_openUpperRay (F C) cut)

/-- A closed lower ray is connected, the cut itself belonging to the set. -/
theorem connected_closedLowerRay (cut : alpha) :
    (F C).IsConnected ((F C).ClosedLowerRay cut) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_closedLowerRay (F C) cut)

/-- A closed upper ray is connected, the cut itself belonging to the set,
mirror of the closed lower-ray case. -/
theorem connected_closedUpperRay (cut : alpha) :
    (F C).IsConnected ((F C).ClosedUpperRay cut) :=
  connected_of_intervalSet C
    (IsOrderedFieldBaseLike.intervalSet_closedUpperRay (F C) cut)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
