/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne
-/
module

public import Tengoku.BrownianMotion.BrownianMotion.Choquet.Capacity
public import Tengoku.BrownianMotion.BrownianMotion.StochasticIntegral.Predictable
public import Tengoku

/-!
This file contains the basic definitions and properties of the debut of a set.

## Implementation notes

We follow the implementation of hitting times in `Mathlib.Probability.Process.HittingTime`.
The debut has values in `WithTop ι`, ensuring that it is always well-defined.
-/

@[expose] public section

open Filter
open scoped Topology

namespace MeasureTheory

lemma nullMeasurable_generateFrom {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, NullMeasurableSet (f ⁻¹' t) μ) :
    @NullMeasurable _ _ _ (MeasurableSpace.generateFrom s) f μ := by
  refine fun t ht ↦ MeasurableSpace.generateFrom_induction (C := s)
    (fun s _ ↦ NullMeasurableSet (f ⁻¹' s) μ) (fun t hts _ ↦ h t hts) (by simp) (by simp) ?_ _ ht
  simp only [Set.preimage_iUnion]
  exact fun t _ hft ↦ NullMeasurableSet.iUnion hft

lemma nullMeasurable_of_Iio {α δ : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [LinearOrder α] [OrderTopology α] [SecondCountableTopology α]
    {mδ : MeasurableSpace δ} {μ : Measure δ}
    {f : δ → α} (hf : ∀ x, NullMeasurableSet (f ⁻¹' Set.Iio x) μ) : NullMeasurable f μ := by
  convert nullMeasurable_generateFrom (α := δ) _
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio _)
  · rintro _ ⟨x, rfl⟩; exact hf x

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open scoped Classical in
/-- The debut of a set `E ⊆ T × Ω` after `n` is the random variable that gives the smallest
`t ≥ n` such that `(t, ω) ∈ E` for a given `ω`. -/
noncomputable def debut [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n : ι) : Ω → WithTop ι :=
  hittingAfter (fun t ω ↦ (t, ω)) E n

open scoped Classical in
lemma debut_eq_ite [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n : ι) :
    debut E n = fun ω ↦ if ∃ t ≥ n, (t, ω) ∈ E then
      ((sInf {t ≥ n | (t, ω) ∈ E} : ι) : WithTop ι) else ⊤ := rfl

lemma debut_eq_hittingAfter_indicator [Preorder ι] [InfSet ι] (E : Set (ι × Ω))
    [∀ t ω, Decidable ((t, ω) ∈ E)] (n : ι) :
    debut E n = hittingAfter (fun t ω ↦ if (t, ω) ∈ E then 1 else 0) {1} n := by
  ext ω
  simp only [debut, hittingAfter]
  split_ifs <;> simp <;> grind

lemma hittingAfter_eq_debut [Preorder ι] [InfSet ι] {β : Type*} (u : ι → Ω → β)
    (s : Set β) (n : ι) :
    hittingAfter u s n = debut {p : ι × Ω | u p.1 p.2 ∈ s} n := rfl

section Debut

/-- The debut of the empty set is the constant function that returns `m`. -/
@[simp]
lemma debut_empty [Preorder ι] [InfSet ι] (n : ι) : debut (∅ : Set (ι × Ω)) n = fun _ ↦ ⊤ :=
  hittingAfter_empty n

@[simp]
lemma debut_univ [ConditionallyCompleteLattice ι] (n : ι) :
    debut (.univ : Set (ι × Ω)) n = fun _ ↦ (n : WithTop ι) := hittingAfter_univ n

open scoped Classical in
@[simp]
lemma debut_prod [Preorder ι] [InfSet ι] (n : ι) (I : Set ι) (A : Set Ω) :
    debut (I ×ˢ A) n = fun ω ↦ if .Ici n ∩ I ≠ ∅ then
        if ω ∈ A then ((sInf (.Ici n ∩ I) : ι) : WithTop ι) else ⊤
      else ⊤ := by
  ext ω
  split_ifs with hI hω
  · simp only [debut_eq_ite, Set.mem_prod, hω, and_true]
    exact ite_eq_left (Set.nonempty_iff_ne_empty.mpr hI)
  · simp [debut_eq_ite, hω]
  · simp only [ne_eq, Decidable.not_not] at hI
    refine ite_eq_right ?_
    simp only [Set.mem_prod, not_exists, not_and]
    exact fun i hni hiI _ ↦ Set.notMem_empty i (hI ▸ ⟨hni, hiI⟩)

lemma debut_prod_univ [Preorder ι] [InfSet ι] (n : ι) (I : Set ι) [Decidable (Set.Ici n ∩ I ≠ ∅)] :
    debut (I ×ˢ (.univ : Set Ω)) n = fun _ ↦ if .Ici n ∩ I ≠ ∅ then
      ((sInf (.Ici n ∩ I) : ι) : WithTop ι) else ⊤ := by simp

lemma debut_univ_prod [ConditionallyCompleteLattice ι] (n : ι) (A : Set Ω) [DecidablePred (· ∈ A)] :
    debut ((.univ : Set ι) ×ˢ A) n = fun ω ↦ if ω ∈ A then (n : WithTop ι) else ⊤ := by
  rw [debut_eq_ite]
  ext ω
  split_ifs with hi hω hω
  · simp only [Set.mem_prod, Set.mem_univ, hω, and_true, WithTop.coe_eq_coe]
    exact csInf_Ici
  · simp_all
  · simp only [Set.mem_prod, Set.mem_univ, hω, and_true, not_exists] at hi
    simpa only [le_refl, not_true_eq_false] using hi n
  · simp_all

lemma debut_anti [ConditionallyCompleteLinearOrder ι] (n : ι) : Antitone (debut (Ω := Ω) · n) :=
  hittingAfter_anti _ n

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {E : Set (ι × Ω)} {n t : ι} {ω : Ω}

lemma notMem_of_lt_debut (ht : t < debut E n ω) (hnt : n ≤ t) : (t, ω) ∉ E :=
  notMem_of_lt_hittingAfter ht hnt

lemma debut_eq_top_iff : debut E n ω = ⊤ ↔ ∀ t ≥ n, (t, ω) ∉ E := hittingAfter_eq_top_iff

lemma debut_ne_top_iff : debut E n ω ≠ ⊤ ↔ ∃ t ≥ n, (t, ω) ∈ E := by simp [debut_eq_top_iff]

lemma le_debut (ω : Ω) : n ≤ debut E n ω := le_hittingAfter ω

lemma debut_mem_set [WellFoundedLT ι] (h : ∃ t ≥ n, (t, ω) ∈ E) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set h

lemma debut_mem_set_of_ne_top [WellFoundedLT ι] (h : debut E n ω ≠ ⊤) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set_of_ne_top h

lemma debut_le_of_mem (ht : n ≤ t) (h_mem : (t, ω) ∈ E) :
    debut E n ω ≤ t := hittingAfter_le_of_mem ht h_mem

-- todo: replace `hittingAfter_lt_iff` with this
lemma hittingAfter_lt_iff' {Ω β ι : Type*} [ConditionallyCompleteLinearOrder ι]
    {u : ι → Ω → β} {s : Set β} {n : ι} {ω : Ω} {i : ι} :
    hittingAfter u s n ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω ≠ ⊤ := fun h ↦ by simp [h] at h'
    have h_top' : ∃ j, n ≤ j ∧ u j ω ∈ s := by
      rw [ne_eq, hittingAfter_eq_top_iff] at h_top
      push Not at h_top
      exact h_top
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    rw [hittingAfter, ite_eq_left h_top'] at h'
    norm_cast at h'
    rw [csInf_lt_iff] at h'
    rotate_left
    · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    · exact h_top'
    simp only [Set.mem_ofPred_eq] at h'
    obtain ⟨j, hj₁, hj₂⟩ := h'
    refine ⟨j, ⟨hj₁.1, hj₂⟩, hj₁.2⟩
  · obtain ⟨j, hj₁, hj₂⟩ := h'
    refine lt_of_le_of_lt ?_ (mod_cast hj₁.2 : (j : WithTop ι) < i)
    exact hittingAfter_le_of_mem hj₁.1 hj₂

lemma debut_le_iff [WellFoundedLT ι] : debut E n ω ≤ t ↔ ∃ j ∈ Set.Icc n t, (j, ω) ∈ E :=
  hittingAfter_le_iff

lemma debut_lt_iff : debut E n ω < t ↔ ∃ j ∈ Set.Ico n t, (j, ω) ∈ E :=
  hittingAfter_lt_iff'

lemma debut_mono (E : Set (ι × Ω)) (ω : Ω) : Monotone (debut E · ω) := hittingAfter_apply_mono _ _ _

end Inequalities

lemma debut_mem_of_isClosed {𝓧 ι : Type*} [TopologicalSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderTopology ι] [FirstCountableTopology ι]
    {s : Set (ι × 𝓧)} {ω : 𝓧} {n : ι}
    (hs : IsClosed {t | n ≤ t ∧ (t, ω) ∈ s}) (hω : debut s n ω ≠ ⊤) :
    ((debut s n ω).untopA, ω) ∈ s := by
  obtain ⟨t₀, ht₀⟩ : ∃ t ≥ n, (t, ω) ∈ s := debut_ne_top_iff.mp hω
  obtain ⟨u, _, hu_tendso, hu_mem⟩ : ∃ u : ℕ → ι, Antitone u ∧
      Tendsto u atTop (𝓝 ((debut s n ω).untopA)) ∧ (∀ i, n ≤ u i ∧ (u i, ω) ∈ s) := by
    simp only [debut_eq_ite, ge_iff_le]
    rw [ite_eq_left (debut_ne_top_iff.mp hω)]
    have : ((sInf {t : ι |  n ≤ t ∧ (t, ω) ∈ s} : ι) : WithTop ι).untopA =
        sInf {t | n ≤ t ∧ (t, ω) ∈ s} := by
      rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [this]
    exact exists_seq_tendsto_sInf (S := {t | n ≤ t ∧ (t, ω) ∈ s}) (debut_ne_top_iff.mp hω)
      ⟨n, mem_lowerBounds.mpr (by grind)⟩
  suffices (debut s n ω).untopA ∈ {t | n ≤ t ∧ (t, ω) ∈ s} from this.2
  exact IsClosed.mem_of_tendsto (f := u) hs hu_tendso (.of_forall hu_mem)

-- TODO: change the name to reflect the `IsStronglyProgressive` new name
/-- A set `E : Set ι × Ω` is progressively measurable with respect to a filtration `𝓕` if the
indicator function of `E` is a progressively measurable process with respect to `𝓕`. -/
def ProgMeasurableSet [Preorder ι] [MeasurableSpace ι] (E : Set (ι × Ω)) (𝓕 : Filtration ι mΩ) :=
  IsStronglyProgressive 𝓕 (E.indicator fun _ ↦ 1).curry

lemma ProgMeasurableSet.measurableSet_prod [Preorder ι] [MeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 t)]
      {p : Set.Iic t × Ω | ((p.1 : ι), p.2) ∈ E} := by
  rw [← measurable_indicator_const_iff (b := 1)]
  exact (hE t).measurable

lemma ProgMeasurableSet.measurableSet_inter_Iic [Preorder ι]
    [TopologicalSpace ι] [ClosedIicTopology ι] {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iic t ×ˢ .univ)) := by
  have h_prod := hE.measurableSet_prod t
  have : (E ∩ Set.Iic t ×ˢ Set.univ) =
      (Prod.map ((↑) : Set.Iic t → ι) id) '' {p : Set.Iic t × Ω | ((p.1 : ι), p.2) ∈ E} := by
    ext; simp; grind
  rw [this]
  refine (@MeasurableEmbedding.measurableSet_image _ _ _ (Subtype.instMeasurableSpace.prod (𝓕 t))
    (mι.prod (𝓕 t)) _ ?_).mpr h_prod
  refine MeasurableEmbedding.prodMap ?_ .id
  exact MeasurableEmbedding.subtype_coe measurableSet_Iic

@[gcongr]
lemma MeasurableSpace.prod_mono {mι : MeasurableSpace ι} {mι' : MeasurableSpace ι}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω}
    (h₁ : mι ≤ mι') (h₂ : mΩ ≤ mΩ') :
    mι.prod mΩ ≤ mι'.prod mΩ' := by
  simp only [MeasurableSpace.prod, sup_le_iff]
  refine ⟨le_sup_of_le_left ?_, le_sup_of_le_right ?_⟩
  · rw [MeasurableSpace.comap_le_iff_le_map]
    exact h₁.trans MeasurableSpace.le_map_comap
  · rw [MeasurableSpace.comap_le_iff_le_map]
    exact h₂.trans MeasurableSpace.le_map_comap

lemma ProgMeasurableSet.measurableSet_inter_Iio [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio t ×ˢ .univ)) := by
  by_cases ht : 𝓝[<] t = ⊥
  · rw [nhdsLT_eq_bot_iff] at ht
    cases ht with
    | inl ht =>
      have h_empty : Set.Iio t = ∅ := by ext x; simp [ht x]
      simp [h_empty]
    | inr ht =>
      obtain ⟨s, hst, hs⟩ := ht
      simp only [not_lt] at hs
      have h_eq_Iic : Set.Iio t = Set.Iic s := by
        ext x
        simp only [Set.mem_Iio, Set.mem_Iic]
        rcases le_or_gt x s <;> grind
      rw [h_eq_Iic]
      have hs := hE.measurableSet_inter_Iic s
      have h_le : mι.prod (𝓕 s) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl (𝓕.mono hst.le)
      exact h_le _ hs
  have : (𝓝[<] t).NeBot := ⟨ht⟩
  -- write Iio as a countable union of Iic and use the previous lemma
  obtain ⟨s, hs_gt, hs_tendsto⟩ : ∃ s : ℕ → ι, (∀ n, s n < t) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : ∃ᶠ x in 𝓝[<] t, x < t :=
      Eventually.frequently <| eventually_nhdsWithin_of_forall fun _ hx ↦ hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  have h_iUnion : ⋃ i, Set.Iic (s i) = Set.Iio t :=
    iUnion_Iic_eq_Iio_of_lt_of_tendsto hs_gt hs_tendsto
  rw [← h_iUnion, Set.iUnion_prod_const, Set.inter_iUnion]
  refine MeasurableSet.iUnion fun i ↦ ?_
  have hs := hE.measurableSet_inter_Iic (s i)
  have h_le : mι.prod (𝓕 (s i)) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl
    (𝓕.mono (hs_gt _).le)
  exact h_le _ hs

lemma ProgMeasurableSet.measurableSet_inter_Ico [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (s t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Ico s t ×ˢ .univ)) := by
  rcases le_total t s with h_ts | h_st
  · simp [h_ts]
  -- write `Ico s t` as `Iio t \ Iio s` and use the previous lemmas
  have h_meas_s : MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio s ×ˢ .univ)) := by
    have hs := hE.measurableSet_inter_Iio s
    have h_le : mι.prod (𝓕 s) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl (𝓕.mono h_st)
    exact h_le _ hs
  have h_meas_t := hE.measurableSet_inter_Iio t
  convert h_meas_t.diff h_meas_s using 1
  ext
  simp
  grind

lemma ProgMeasurableSet.measurableSet_inter_Icc [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (s t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Icc s t ×ˢ .univ)) := by
  rcases le_or_gt s t with h_st | h_ts
  swap; · simp [h_ts]
  -- write `Icc s t` as `Iic t \ Iio s` and use the previous lemmas
  have h_meas_s : MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio s ×ˢ .univ)) := by
    have hs := hE.measurableSet_inter_Iio s
    have h_le : mι.prod (𝓕 s) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl (𝓕.mono h_st)
    exact h_le _ hs
  convert (hE.measurableSet_inter_Iic t).diff h_meas_s using 1
  ext
  simp
  grind

lemma debut_eq_iff_of_nhdsGT_eq_bot
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (E : Set (ι × Ω)) {n t : ι} (hnt : n ≤ t) (ht : 𝓝[>] t = ⊥) (ω : Ω)
    (h_ge : t ≤ debut E n ω) :
    debut E n ω = t ↔ (t, ω) ∈ E := by
  -- todo: extract a lemma about hittingAfter?
  simp only [debut, hittingAfter] at h_ge ⊢
  split_ifs with h_exists
  swap
  · simp only [not_exists, not_and] at h_exists
    simp only [WithTop.top_ne_coe, false_iff]
    exact h_exists t hnt
  simp only [h_exists, ↓reduceIte, WithTop.coe_le_coe, WithTop.coe_inj] at h_ge ⊢
  refine ⟨fun h_eq ↦ ?_, fun h_mem ↦ ?_⟩
  · rw [nhdsGT_eq_bot_iff] at ht
    cases ht with
    | inl ht =>
      obtain ⟨j, hj⟩ := h_exists
      suffices htj : t ≤ j by
        have htj_eq := le_antisymm htj (ht j)
        simpa [htj_eq] using hj.2
      refine h_ge.trans ?_
      refine csInf_le ?_ hj
      exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    | inr ht =>
      obtain ⟨u, htu, hu⟩ := ht
      simp only [not_lt] at hu
      by_contra! h_notMem
      suffices u ≤ sInf {j | n ≤ j ∧ (j, ω) ∈ E} by
        refine not_le.mpr htu ?_
        rwa [h_eq] at this
      refine le_csInf h_exists fun j hj ↦ ?_
      refine hu (lt_of_le_of_ne ?_ ?_)
      · rw [le_csInf_iff] at h_ge
        · exact h_ge j hj
        · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
        · exact h_exists
      · intro htj_eq
        simp only [Set.mem_ofPred_eq, ← htj_eq] at hj
        exact h_notMem hj.2
  · refine le_antisymm ?_ h_ge
    refine csInf_le ?_ ⟨hnt, h_mem⟩
    exact ⟨n, by simp [mem_lowerBounds]; grind⟩

end Debut

section HittingTime

/-- `leastGT f r` is the stopping time corresponding to the first time `f ≥ r`. -/
noncomputable def leastGT {ι Ω β : Type*} [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ioi r) ⊥

lemma leastGT_lt_iff {ι β : Type*} [ConditionallyCompleteLinearOrder ι] [OrderBot ι] [Preorder β]
    (X : ι → Ω → β) (a : β) (t : ι) (ω : Ω) :
    leastGT X a ω < t ↔ ∃ s < t, a < X s ω := by simp [leastGT, hittingAfter_lt_iff']

end HittingTime

end MeasureTheory
