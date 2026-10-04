/-
Copyright (c) 2024 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module

public import Tengoku

public import Tengoku.SpherePackingOrig.SpherePacking.Basic.SpherePacking
public import Tengoku.SpherePackingOrig.SpherePacking.ForMathlib.ENNReal
public import Tengoku.SpherePackingOrig.SpherePacking.ForMathlib.Encard
public import Tengoku.SpherePackingOrig.SpherePacking.ForMathlib.ENat
public import Tengoku.SpherePackingOrig.SpherePacking.ForMathlib.ZLattice

/-!
# Periodic Sphere Packings

Defines periodic sphere packings and relates their density to that of the underlying packing.
-/

@[expose] public section

-- import Mathlib

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

/-#
Key results:

* `PeriodicSpherePacking.density_eq`: The density of a periodic sphere packing equals the natural
density within a fundamental domain w.r.t. any basis.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

lemma aux1 (hD_isBounded : IsBounded D) :
    IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) := by
  apply isBounded_iff_forall_norm_le.mpr
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.mp <| hD_isBounded
  use L + S.separation / 2
  intro x hx
  obtain ⟨y, s, hy, hy'⟩ := Set.mem_iUnion.mp hx
  rw [Set.mem_range, exists_prop] at hy
  obtain ⟨hy, rfl⟩ := hy
  rw [mem_ball, dist_eq_norm] at hy'
  specialize hL y hy.right
  exact (norm_le_norm_add_norm_sub' x y).trans (by gcongr)

lemma aux2 (D : Set (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint (S.centers ∩ D) (fun x ↦ ball x (S.separation / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [add_halves]
  exact S.centers_dist' _ _ hx.left hy.left hxy

theorem aux3 {ι τ : Type*} {s : Set ι} {f : ι → Set (EuclideanSpace ℝ τ)} {c : ℝ≥0∞} (hc : 0 < c)
    [Fintype τ] [NullSingletonClass (volume : Measure (EuclideanSpace ℝ τ))]
    (h_measurable : ∀ x ∈ s, MeasurableSet (f x))
    (h_bounded : IsBounded (⋃ x ∈ s, f x))
    (h_volume : ∀ x ∈ s, c ≤ volume (f x))
    (h_disjoint : s.PairwiseDisjoint f) :
    s.Finite := by
  wlog h_countable : s.Countable with h_wlog
  · by_contra! h_finite
    rw [Set.Countable, ← Cardinal.mk_le_aleph0_iff, not_le] at h_countable
    -- Brilliant(!!) idea by Etienne Marion on Zulip
    -- If s is uncountable, then we can argue on a countable subset!
    obtain ⟨t, ⟨ht_subset, ht_aleph0⟩⟩ := Cardinal.le_mk_iff_exists_subset.mp h_countable.le
    have ht_infinite : Infinite t := Cardinal.aleph0_le_mk_iff.mp ht_aleph0.symm.le
    have ht_countable := Cardinal.mk_le_aleph0_iff.mp ht_aleph0.le
    specialize @h_wlog _ _ t f c hc _ _ ?_ ?_ ?_ ?_ ht_countable
    · exact fun x hx ↦ h_measurable x (ht_subset hx)
    · exact h_bounded.subset <| Set.biUnion_mono ht_subset (by intros; rfl)
    · exact fun x hx ↦ h_volume x (ht_subset hx)
    · exact Set.Pairwise.mono ht_subset h_disjoint
    · exact ht_infinite.not_finite h_wlog
  · haveI : Countable s := h_countable
    obtain ⟨L, hL⟩ := h_bounded.subset_ball 0
    have h_volume' := volume.mono hL
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure, Set.biUnion_eq_iUnion,
      measure_iUnion] at h_volume'
    · have h_le : ∑' (n : ↑s), c ≤ ∑' (n : ↑s), volume (f ↑n) :=
          Summable.tsum_mono (f := fun _ ↦ c) (g := fun (x : s) ↦ volume (f x)) ?_ ?_ ?_
      · have h₁ := (ENNReal.tsum_set_const _ _ ▸ h_le).trans h_volume'
        rw [← Set.encard_lt_top_iff, ← ENat.toENNReal_lt, ENat.toENNReal_top]
        refine lt_of_le_of_lt ((ENNReal.le_div_iff_mul_le ?_ ?_).mpr h₁) <|
          ENNReal.div_lt_top ?_ hc.ne.symm
        · left; positivity
        · right; exact (volume_ball_lt_top _).ne
        · exact (volume_ball_lt_top _).ne
      · exact ENNReal.summable
      · exact ENNReal.summable
      · intro x
        exact h_volume x.val x.prop
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      exact h_disjoint hx hy (by simpa using hxy)
    · exact fun ⟨x, hx⟩ ↦ h_measurable x hx

lemma aux4 (hD_isBounded : IsBounded D) (hd : 0 < d) : Finite ↑(S.centers ∩ D) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply aux3 (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))) ?_ ?_
      (aux1 S D hD_isBounded)
  · intros
    simp [Measure.addHaar_ball_center]
  · intro x hx y hy hxy
    apply ball_disjoint_ball
    simpa [add_halves] using S.centers_dist' _ _ hx.left hy.left hxy
  · apply volume_ball_pos
    linarith [S.separation_pos]
  · intros
    exact measurableSet_ball

lemma aux4' {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) :
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  aux4 S _ (ZSpan.fundamentalDomain_isBounded _) hd

open scoped Pointwise in
lemma aux4''
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) :
    Finite ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) :=
  aux4 S _ (IsBounded.vadd (ZSpan.fundamentalDomain_isBounded _) _) hd

end aux_lemmas

section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise

-- TODO: rename + move
theorem PeriodicSpherePacking.fract_centers
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (s : S.centers) :
    fract (b.ofZLatticeBasis ℝ _) s.val ∈ S.centers := by
  have := (floor (b.ofZLatticeBasis ℝ _) s).prop
  simp_rw [S.basis_Z_span] at this
  rw [fract_apply, sub_eq_add_neg, add_comm]
  apply S.lattice_action (neg_mem this) s.prop

-- TODO: rename + move
theorem PeriodicSpherePacking.orbitRel_fract
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (a : S.centers) :
    (S.addAction.orbitRel).r ⟨fract (b.ofZLatticeBasis ℝ _) a, S.fract_centers _ _⟩ a := by
  rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range]
  refine ⟨⟨-↑(floor (b.ofZLatticeBasis ℝ _) ↑a), ?_⟩, ?_⟩
  · apply neg_mem
    have := (floor (b.ofZLatticeBasis ℝ _) a.val).prop
    simp_rw [S.basis_Z_span] at this
    exact this
  · simp_rw [fract_apply, sub_eq_neg_add]
    rfl

end instances

section numReps

-- Gareth's Code

open scoped Pointwise

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

noncomputable instance PeriodicSpherePacking.instCentersSetoid : Setoid S.centers :=
  S.addAction.orbitRel

-- TODO: rename

end numReps

-- TODO: Merge above and below; rename stuff as needed

section numReps_aux

  -- Sid's code for Cohn-Elkies

variable {d : ℕ}

@[reducible]
noncomputable def PeriodicSpherePacking.instFintypeNumReps'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd

noncomputable def PeriodicSpherePacking.numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  letI := S.instFintypeNumReps' hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)

theorem PeriodicSpherePacking.numReps'_nonneg (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  0 ≤ S.numReps' hd hD_isBounded := by
  letI := S.instFintypeNumReps' hd hD_isBounded
  rw [PeriodicSpherePacking.numReps']
  exact Nat.zero_le (Fintype.card ↑(S.centers ∩ D))

-- theorem PeriodicSpherePacking.numReps_ne_zero (S : PeriodicSpherePacking d)

end numReps_aux

section theorem_2_3

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

open scoped Pointwise

-- Theorem 2.3, lower bound

-- Theorem 2.3, upper bound - the proof is similar to lower bound

end theorem_2_3

----------------------------------------------------

section theorem_2_2

/- In this section we prove Theorem 2.2 of the blueprint. Below, instead of using a single
assumption `IsAddFundamentalDomain S.lattice D`, we chose to split it up into `hD_unique_covers` and
`hD_measure` (see below), which together (along with that D is null measurable) imply that `D` is an
additive fundamental domain. We do this because annoyingly, `IsAddFundamentalDomain` only requires D
to *almost* cover the entire space (ℝ ^ n), i.e. up to a null measurable set, and also for the
cosets to be *almost* disjoint. This makes the proofs below extremely annoying. For example, proving
that `volume (⋃ x ∈ s, x +ᵥ D) = s.encard • volume D` is tedious because `measure_iUnion` requires
things to be strictly disjoint. In short, results below *should* work if D is
`IsAddFundamentalDomain`, but we don't bother.

Note that this is consistent with how some parts of Mathlib are structured - they don't bother
either :)
-/

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

private theorem hD_isAddFundamentalDomain
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    IsAddFundamentalDomain S.lattice D where
  nullMeasurableSet := hD_measurable.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun x ↦ (hD_unique_covers x).exists
  aedisjoint := by
    apply Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_zero
    · intro g hg
      apply Disjoint.aedisjoint
      rw [Set.disjoint_iff]
      intro x ⟨hx₁, hx₂⟩
      have ⟨y, ⟨_, hy_unique⟩⟩ := hD_unique_covers x
      have hy₁ := hy_unique 0 (by simpa [Submodule.vadd_def, vadd_eq_add] using hx₂)
      have hy₂ := hy_unique (-g) (Set.mem_vadd_set_iff_neg_vadd_mem.mp hx₁)
      rw [neg_eq_iff_eq_neg.mp hy₂, ← hy₁] at hg
      norm_num at hg
    · exact fun _ ↦ quasiMeasurePreserving_add_left _ _

theorem aux7 (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  obtain ⟨g, hg, _⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · simp
  · rw [← norm_neg] at hx
    rw [mem_ball_zero_iff, norm_neg]
    calc
      _ = ‖(g + x) + (-x)‖ := by congr; abel
      _ ≤ ‖(g + x)‖ + ‖(-x)‖ := norm_add_le _ _
      _ < L + (R - L) := add_lt_add_of_le_of_lt (hL _ hg) hx
      _ = R := by abel
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg]
    exact hg

omit d S D L R ι in
instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ :=
  inferInstanceAs <| VAddInvariantMeasure s.toAddSubgroup E μ

-- Theorem 2.2, lower bound
theorem PeriodicSpherePacking.aux2_ge
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  rw [ge_iff_le, ENNReal.div_le_iff]
  · calc
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
          ≤ volume (⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, x +ᵥ D) :=
        volume.mono <| aux7 S D R hD_unique_covers hL
      _ = (↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard : ℝ≥0∞)
          * volume D := by
        rw [Set.biUnion_eq_iUnion]
        have : Countable ↑S.lattice := inferInstance
        have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
          Set.Countable.mono (Set.inter_subset_left) this
        rw [measure_iUnion]
        · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
        · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
          replace hxy : x ≠ y := Subtype.ext_iff.ne.mp hxy
          simp_rw [Set.disjoint_iff]
          intro v ⟨hxv, hyv⟩
          obtain ⟨⟨z, hz⟩, _, hz_unique⟩ := hD_unique_covers v
          have hx' := hz_unique ⟨-x, neg_mem hx.left⟩
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxv)
          have hy' := hz_unique ⟨-y, neg_mem hy.left⟩
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hyv)
          replace hx' : x = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hx'
          replace hy' : y = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hy'
          exact hxy (hx'.trans hy'.symm)
        · intro i
          exact MeasurableSet.const_vadd hD_measurable i.val
  · convert (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume)
  · have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    rw [← lt_top_iff_ne_top]
    exact Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)

theorem aux8 (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  rw [mem_ball_zero_iff]
  obtain ⟨g, _, _⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff] at hx
  obtain ⟨i, ⟨_, hi_ball⟩, hi_fd⟩ := hx
  rw [mem_ball_zero_iff] at hi_ball
  have := hL (-i + x) (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_fd)
  calc
    _ = ‖i + (-i + x)‖ := by congr; abel
    _ ≤ ‖i‖ + ‖-i + x‖ := norm_add_le _ _
    _ < R + L := add_lt_add_of_lt_of_le hi_ball this

-- Theorem 2.2, upper bound
theorem PeriodicSpherePacking.aux2_le
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  rw [ENNReal.le_div_iff_mul_le]
  · calc
      (↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard : ℝ≥0∞) * volume D
          = volume (⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, x +ᵥ D) := by
        rw [Set.biUnion_eq_iUnion]
        have : Countable ↑S.lattice := inferInstance
        have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
          Set.Countable.mono (Set.inter_subset_left) this
        rw [measure_iUnion]
        · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
        · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
          replace hxy : x ≠ y := Subtype.ext_iff.ne.mp hxy
          simp_rw [Set.disjoint_iff]
          intro v ⟨hxv, hyv⟩
          obtain ⟨⟨z, hz⟩, _, hz_unique⟩ := hD_unique_covers v
          have hx' := hz_unique ⟨-x, neg_mem hx.left⟩
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxv)
          have hy' := hz_unique ⟨-y, neg_mem hy.left⟩
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hyv)
          replace hx' : x = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hx'
          replace hy' : y = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hy'
          exact hxy (hx'.trans hy'.symm)
        · intro i
          exact MeasurableSet.const_vadd hD_measurable i.val
      _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) :=
        volume.mono <| aux8 S D R hD_unique_covers hL
  · left
    convert (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume)
  · left
    have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    rw [← lt_top_iff_ne_top]
    exact Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)

open ZSpan

variable (b : Basis ι ℤ S.lattice)

-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice
theorem PeriodicSpherePacking.aux2_ge'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.aux2_ge _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  simp only [S.basis_Z_span] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  · rwa [Subtype.ext_iff] at this ⊢
  · rw [S.basis_Z_span]
    exact hy

-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice
theorem PeriodicSpherePacking.aux2_le'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.aux2_le _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  simp only [S.basis_Z_span] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  · rwa [Subtype.ext_iff] at this ⊢
  · rw [S.basis_Z_span]
    exact hy

section finiteDensity_limit

/- TODO: consider moving this section. -/

open MeasureTheory Measure Metric ZSpan

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

open Filter Topology

section VolumeBallRatio

open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace

-- Credits to Bhavik Mehta for this <3 my original code is 92 lines long x)
private lemma aux_bhavik {d : ℝ} {ε : ℝ≥0∞} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  suffices Filter.Tendsto
      (fun k => (ENNReal.ofReal (1 - (k + 1)⁻¹) ^ d)) atTop (𝓝 (ENNReal.ofReal (1 - 0) ^ d)) by
    rw [ENNReal.tendsto_atTop ?ha] at this
    case ha => simp
    obtain ⟨k, hk⟩ := this ε hε
    refine ⟨max 0 k, by simp, ?_⟩
    simp only [max_le_iff, and_imp]
    intro k' hk₀ hk₁
    have := hk k' hk₁
    rwa [sub_zero, ofReal_one, one_rpow, ←one_div, one_sub_div, add_sub_cancel_right,
      ENNReal.ofReal_rpow_of_nonneg] at this
    · positivity
    · positivity
    · positivity
  refine Tendsto.ennrpow_const d (tendsto_ofReal (Tendsto.const_sub 1 ?_))
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)

private lemma aux_bhavik' {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  simpa using aux_bhavik (d := d) (Nat.cast_nonneg _) hε

theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rcases le_iff_eq_or_lt.mp hC with (rfl | hC)
  · simp_rw [add_zero]
    apply Tendsto.congr' (f₁ := 1) ?_ tendsto_const_nhds
    rw [EventuallyEq, eventually_atTop]
    use 1
    intro b hb
    rw [ENNReal.div_self, Pi.one_apply]
    · exact (volume_ball_pos _ (by linarith)).ne.symm
    · exact (volume_ball_lt_top _).ne
  · have (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
          = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
      rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
        ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos, mul_div_mul_right]
      <;> positivity
    rw [ENNReal.tendsto_atTop (by decide)]
    intro ε hε
    obtain ⟨k, ⟨hk₁, hk₂⟩⟩ := aux_bhavik' (d := d) hε
    use k * C
    intro n hn
    rw [this _ ((by positivity : 0 ≤ k * C).trans hn)]
    convert hk₂ (n / C) ((le_div_iff₀ hC).mpr hn)
    rw [div_add_one, div_div_div_cancel_right₀, div_pow]
    · positivity
    · positivity

theorem volume_ball_ratio_tendsto_nhds_one'
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  -- I love ENNReal (I don't)
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply Tendsto.congr' (f₁ := fun R ↦
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))
        / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))))
  · rw [EventuallyEq, eventually_atTop]
    use 1
    intro R hR
    have hR' : 0 < R := by linarith
    rw [ENNReal.div_div_div_cancel_left]
    · exact (volume_ball_pos _ hR').ne.symm
    · exact (volume_ball_lt_top _).ne
    · exact (volume_ball_lt_top _).ne
  · convert ENNReal.Tendsto.div (volume_ball_ratio_tendsto_nhds_one hd hC') ?_
      (volume_ball_ratio_tendsto_nhds_one hd hC) ?_ <;> simp

theorem Filter.map_add_atTop_eq' {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α := by
  constructor <;> intro hf
  · apply tendsto_map'_iff.mp
    convert hf
    rw [map_atTop_eq_of_gc (fun x ↦ x - C) 0 ?_ ?_ ?_]
    · exact Monotone.add_const (fun _ _ a ↦ a) _
    · simp [le_sub_iff_add_le]
    · simp [sub_add_cancel]
  · convert tendsto_map'_iff.mpr hf using 1
    rw [map_atTop_eq_of_gc (fun x ↦ x - C) 0 ?_ ?_ ?_]
    · exact Monotone.add_const (fun _ _ a ↦ a) _
    · simp [le_sub_iff_add_le]
    · simp [sub_add_cancel]

theorem volume_ball_ratio_tendsto_nhds_one'' {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  apply (Filter.map_add_atTop_eq' (max (-C) (-C')) _).mpr
  simp_rw [add_assoc]
  convert volume_ball_ratio_tendsto_nhds_one' hd ?_ ?_
  · trans (-C) + C
    · linarith
    · gcongr; simp
  · trans (-C') + C'
    · linarith
    · gcongr; simp

end VolumeBallRatio

section DensityEqFdDensity

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

end DensityEqFdDensity

section ConstantEqNormalizedConstant

theorem periodic_constant_eq_periodic_constant_normalized (hd : 0 < d) :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.density := by
  -- Argument almost identical to `constant_eq_constant_normalized`, courtesy Gareth
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  apply le_antisymm
  · apply iSup_le
    intro S
    have h := inv_mul_cancel₀ S.separation_pos.ne.symm
    have := le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦ x.val.density)
        ⟨S.scale (inv_pos.mpr S.separation_pos), h⟩
    rw [← scale_density hd]
    · exact this
    · rw [inv_pos]
      exact S.separation_pos
  · apply iSup_le
    intro ⟨S, _⟩
    simp only
    exact le_iSup_iff.mpr fun b a ↦ a S

end ConstantEqNormalizedConstant

section Disjoint_Covering_of_Centers

theorem PeriodicSpherePacking.unique_covers_of_centers (S : PeriodicSpherePacking d) -- (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} -- (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) -- (hD_measurable : MeasurableSet D)
  :
  ∀ x : S.centers, ∃! g : S.lattice, (g +ᵥ x : EuclideanSpace ℝ (Fin d)) ∈ S.centers ∩ D := by
  intro x
  obtain ⟨g, hg₁, hg₂⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
  use g
  simp only [Set.mem_inter_iff, Subtype.coe_prop, true_and, Subtype.forall] at hg₁ hg₂ ⊢
  constructor
  · exact hg₁
  · intro a ha hmem
    exact hg₂ a ha hmem

theorem PeriodicSpherePacking.centers_union_over_lattice (S : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    S.centers = ⋃ (g : S.lattice), (g +ᵥ S.centers ∩ D) := by
  ext x
  simp only [Set.mem_iUnion, Subtype.exists]
  constructor
  · intro hx
    obtain ⟨g, hg₁, _⟩ := S.unique_covers_of_centers hD_unique_covers ⟨x, hx⟩
    use -g
    simp only [neg_mem_iff, SetLike.coe_mem]
    obtain ⟨hy₁, hy₂⟩ := hg₁
    have : ∃ y : D, ↑y = g +ᵥ x := by use ⟨g +ᵥ x, hy₂⟩
    obtain ⟨y, hy⟩ := this
    suffices x = -g +ᵥ (y : EuclideanSpace ℝ (Fin d)) by
      rw [this]
      have hy' := Subtype.coe_prop y
      use True.intro -- so weird
      refine Set.vadd_mem_vadd_set ?h.intro.intro.a
      simp only [Set.mem_inter_iff, hy', and_true]
      rw [hy]
      -- Idea: closure under additive action
      exact hy₁
    rw [hy]
    exact (neg_vadd_vadd g x).symm
  · intro hexa
    obtain ⟨g, hg₁, hg₂⟩ := hexa
    rw [Set.mem_vadd_set] at hg₂
    -- Idea: x = g +ᵥ y for some y in the set of centers
    -- Then apply closure under action
    obtain ⟨y, hy, hy₂⟩ := hg₂
    rw [← hy₂]
    exact S.lattice_action hg₁ hy.left

-- This is true but unnecessary (for now). What's more important is expressing it as a disjoint
-- union over points in X / Λ = X ∩ D of translates of the lattice by points in X / Λ = X ∩ D or
-- something like that, because that's what's needed for `tsum_finset_bUnion_disjoint`.
-- theorem PeriodicSpherePacking.translates_disjoint (S : PeriodicSpherePacking d) -- (hd : 0 < d)
-- {D : Set (EuclideanSpace ℝ (Fin d))} -- (hD_isBounded : IsBounded D)
-- (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) -- (hD_measurable : MeasurableSet D)
-- : Set.Pairwise ⊤ (Disjoint on (fun (g : S.lattice) => g +ᵥ S.centers ∩ D)) -- why the error?
-- -- True
-- := by
-- intro x hx y hy hxy
-- obtain ⟨g, hg₁, hg₂⟩ := hD_unique_covers x
-- specialize hg₂ y
-- simp only at hg₂
-- simp only [Set.disjoint_iff_inter_eq_empty]
-- ext z
-- simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
-- intro hz₁ hz₂
-- sorry

-- Can we use some sort of orbit disjointedness result and factor through the equivalence between
-- the `Quotient` and `S.centers ∩ D`?

end Disjoint_Covering_of_Centers

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

-- I include the following because some lemmas in `PeriodicPacking` have them as assumptions, and
-- I'd like to replace all instances of `D` with `fundamentalDomain (b.ofZLatticeBasis ℝ _)` and
-- the assumptions on `D` with the following lemmas.

-- Note that we have `ZSpan.fundamentalDomain_isBounded`. We can use this to prove the following,
-- which is necessary for `PeriodicSpherePacking.density_eq`.
theorem PeriodicSpherePacking.exists_bound_on_fundamental_domain :
  ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))

-- Note that we have `ZSpan.exist_unique_vadd_mem_fundamentalDomain`. We can use this to prove the
-- following.
theorem PeriodicSpherePacking.fundamental_domain_unique_covers :
   ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  have : S.lattice = span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) :=
    Eq.symm (Basis.ofZLatticeBasis_span ℝ S.lattice b)
  intro x
  -- The `g` we need should be the negative of the floor of `x`, but we can obtain it from the
  -- existing library result.
  obtain ⟨g, hg₁, hg₂⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  have hg_mem : ↑g ∈ S.lattice := by simp only [this, SetLike.coe_mem]
  use ⟨↑g, hg_mem⟩
  constructor
  · exact hg₁
  · intro y
    have hy_mem : ↑y ∈ (span ℤ (Set.range ⇑(Basis.ofZLatticeBasis ℝ S.lattice b))).toAddSubgroup :=
      by simp only [← this, SetLike.coe_mem]
    intro hy
    simp only at hg₂ ⊢
    specialize hg₂ ⟨y, hy_mem⟩ hy
    refine SetCoe.ext ?h.right.a
    have heq : ↑y = (g : EuclideanSpace ℝ (Fin d)) := by rw [← hg₂]
    exact heq

-- Note that we already have `ZSpan.fundamentalDomain_measurableSet`. Use
-- `fundamentalDomain_measurableSet (Basis.ofZLatticeBasis ℝ S.lattice b)` to say that our desired
-- fundamental domain is measurable.

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

noncomputable instance HDivENNReal : HDiv NNReal ENNReal ENNReal where
  hDiv := fun x y => x / y
noncomputable instance HMulENNReal : HMul NNReal ENNReal ENNReal where
  hMul := fun x y => x * y

noncomputable def ZLattice.basis_index_equiv (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) := by
  refine Fintype.equivFinOfCardEq ?h
  rw [← Module.finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ Λ,
      finrank_euclideanSpace, Fintype.card_fin]

noncomputable def PeriodicSpherePacking.basis_index_equiv (P : PeriodicSpherePacking d) :
  (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) := ZLattice.basis_index_equiv P.lattice

/- Here's a version of `PeriodicSpherePacking.density_eq` that
1. does not require the `hL` hypothesis that the original one does
2. uses `ZLattice.covolume` instead of the `volume` of a basis-dependent `fundamentalDomain`
-/

end Periodic_Density_Formula

section Empty_Centers

end Empty_Centers

section Periodic_Constant_Eq_Constant

end Periodic_Constant_Eq_Constant
end finiteDensity_limit

end theorem_2_2
