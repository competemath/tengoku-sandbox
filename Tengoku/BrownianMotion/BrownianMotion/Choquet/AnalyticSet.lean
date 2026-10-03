/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Tengoku.BrownianMotion.BrownianMotion.Choquet.CompactSystem
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# Analytic sets in the sense of a paved space

TODO: we use `IsCompactSystem`, which corresponds to semi-compact pavings for D-M. We use this and
not compact pavings (which would be the same, but for arbitrary intersections instead of countable
ones), because it's sufficient for our applications, and because it's easier to work with.

-/

@[expose] public section

open scoped ENNReal NNReal

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

lemma Set.iInter_prod {α β ι : Type*} {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (⋂ i, t i) ×ˢ s = ⋂ i, t i ×ˢ s := by
  ext x
  simp only [Set.mem_prod, Set.mem_iInter]
  exact ⟨fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2⟩, fun h ↦ ⟨fun i ↦ (h i).1, (h hι.some).2⟩⟩

lemma MeasurableSet.of_mem_countableInfClosure {m𝓧 : MeasurableSpace 𝓧} {s : Set 𝓧}
    (hs : s ∈ countableInfClosure {t | MeasurableSet t}) :
    MeasurableSet s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact MeasurableSet.iInter hA

lemma MeasurableSet.of_mem_countableInfClosure' {m𝓧 : MeasurableSpace 𝓧}
    {s : Set 𝓧} {p : Set (Set 𝓧)} (hs : s ∈ countableInfClosure p) (hp : ∀ t ∈ p, MeasurableSet t) :
    MeasurableSet s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.iInter fun n ↦ hp (t n) (ht n)

lemma MeasurableSet.of_mem_countableSupClosure' {m𝓧 : MeasurableSpace 𝓧}
    {s : Set 𝓧} {p : Set (Set 𝓧)} (hs : s ∈ countableSupClosure p) (hp : ∀ t ∈ p, MeasurableSet t) :
    MeasurableSet s := by
  rw [mem_countableSupClosure_iff_iSup] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n ↦ hp (t n) (ht n)

lemma MeasurableSet.of_mem_supClosure {m𝓧 : MeasurableSpace 𝓧} {s : Set 𝓧}
    {p : Set (Set 𝓧)} (hs : s ∈ supClosure p) (hp : ∀ t ∈ p, MeasurableSet t) :
    MeasurableSet s := by
  rw [mem_supClosure_set_iff'] at hs
  obtain ⟨t, _, A, ht, h_eq⟩ := hs
  rw [h_eq]
  exact MeasurableSet.biUnion (Finset.countable_toSet t) fun n hn ↦ hp (A n) (ht n hn)

lemma MeasurableSet.of_mem_image2_prod {Ω 𝓧 : Type*}
    {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {s : Set (𝓧 × Ω)} {p : Set (Set 𝓧)} {q : Set (Set Ω)} (hs : s ∈ Set.image2 (· ×ˢ ·) p q)
    (hp : ∀ t ∈ p, MeasurableSet t) (hq : ∀ t ∈ q, MeasurableSet t) :
    MeasurableSet s := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hs
  exact MeasurableSet.prod (hp A hA) (hq B hB)

lemma MeasurableSet.of_mem_prodSigmaDelta {Ω 𝓧 : Type*}
    {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {s : Set (𝓧 × Ω)} {p : Set (Set 𝓧)} {q : Set (Set Ω)}
    (hs : s ∈ MeasureTheory.prodSigmaDelta p q)
    (hp : ∀ t ∈ p, MeasurableSet t) (hq : ∀ t ∈ q, MeasurableSet t) :
    MeasurableSet s := by
  unfold MeasureTheory.prodSigmaDelta at hs
  refine .of_mem_countableInfClosure' hs fun s hs ↦ ?_
  refine .of_mem_countableSupClosure' hs fun s hs ↦ ?_
  exact .of_mem_image2_prod hs hp hq

namespace MeasureTheory

/-- A set `s` is analytic for a paving (predicate) `p` and a type `𝓚` if there exists a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`prodSigmaDelta p q`. -/
def IsPavingAnalyticFor (p : Set (Set 𝓧)) (𝓚 : Type*) (s : Set 𝓧) : Prop :=
  ∃ q : Set (Set 𝓚), ∅ ∈ q ∧ IsCompactSystem q ∧
    ∃ t : Set (𝓧 × 𝓚), t ∈ prodSigmaDelta p q ∧ s = Prod.fst '' t

/-- A set `s` is analytic for a paving (predicate) `p` if there exists a type `𝓚` and a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`prodSigmaDelta p q`. -/
def IsPavingAnalytic (p : Set (Set 𝓧)) (s : Set 𝓧) : Prop :=
  ∃ 𝓚 : Type, Nonempty 𝓚 ∧ IsPavingAnalyticFor p 𝓚 s

lemma IsPavingAnalyticFor.isPavingAnalytic {𝓚 : Type} [Nonempty 𝓚]
    (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalytic p s := ⟨𝓚, ‹_›, hs⟩

lemma isPavingAnalyticFor_of_mem (𝓚 : Type*) [Nonempty 𝓚] (hs : s ∈ p) :
    IsPavingAnalyticFor p 𝓚 s := by
  classical
  refine ⟨{Set.univ, ∅}, ?_, ?_, ⟨s ×ˢ .univ, ?_, by ext; simp⟩⟩
  · simp
  · exact IsCompactSystem.insert_univ isCompactSystem_singleton_empty
  · exact mem_prodSigmaDelta_of_mem hs (by simp)

lemma isPavingAnalytic_of_mem (hs : s ∈ p) : IsPavingAnalytic p s :=
  (isPavingAnalyticFor_of_mem ℝ hs).isPavingAnalytic

lemma IsPavingAnalyticFor.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor p' 𝓚 s := by
  obtain ⟨q, hq_empty, hq_compact, t, ht_prod, rfl⟩ := hs
  refine ⟨q, hq_empty, hq_compact, ⟨t, ?_, rfl⟩⟩
  exact prodSigmaDelta.mono hp (fun _ ↦ id) ht_prod

lemma IsPavingAnalytic.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic p' s := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.mono hp hs𝓚).isPavingAnalytic

-- He paragraph after 1.25
lemma IsPavingAnalyticFor.exists_mem_countableSupClosure_superset (hs : IsPavingAnalyticFor p 𝓚 s) :
    ∃ t, t ∈ countableSupClosure p ∧ s ⊆ t := by
  obtain ⟨q, hq_empty, hq_compact, B, hB_prod, rfl⟩ := hs
  rw [mem_prodSigmaDelta_iff] at hB_prod
  obtain ⟨A, hA, K, hK, rfl⟩ := hB_prod
  simp_rw [mem_countableSupClosure_iff_iSup]
  refine ⟨⋃ m, A 0 m, ?_, ?_⟩
  · exact ⟨fun m ↦ A 0 m, hA 0, rfl⟩
  · intro x hx
    simp only [Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Prod.exists,
      exists_and_right, exists_eq_right] at hx ⊢
    obtain ⟨_, h⟩ := hx
    choose n hn _ using h
    exact ⟨n 0, hn 0⟩

lemma IsPavingAnalyticFor.empty (𝓚 : Type*) (hp_empty : ∅ ∈ p) : IsPavingAnalyticFor p 𝓚 ∅ := by
  rcases isEmpty_or_nonempty 𝓚 with h_empty | h_nonempty
  · refine ⟨Set.univ, by simp, ?_, ∅ ×ˢ ∅, mem_prodSigmaDelta_of_mem hp_empty (by simp), by simp⟩
    simp only [IsCompactSystem]
    intro C _ _
    have h_eq_empty n : C n = ∅ := Set.eq_empty_of_isEmpty (C n)
    refine ⟨0, ?_⟩
    simpa using h_eq_empty 0
  · exact isPavingAnalyticFor_of_mem 𝓚 hp_empty

@[simp]
lemma IsPavingAnalytic.empty (hp_empty : ∅ ∈ p) : IsPavingAnalytic p ∅ :=
  (IsPavingAnalyticFor.empty ℝ hp_empty).isPavingAnalytic

@[simp]
lemma isPavingAnalyticFor_iff_eq_empty (𝓚 : Type*) [IsEmpty 𝓚] (hp_empty : ∅ ∈ p) (s : Set 𝓧) :
    IsPavingAnalyticFor p 𝓚 s ↔ s = ∅ := by
  refine ⟨fun hs ↦ ?_, fun hs_empty ↦ ?_⟩
  · obtain ⟨q, hq_empty, hq_compact, t, h_prod, h_eq⟩ := hs
    rw [h_eq]
    simp only [Set.image_eq_empty]
    exact Set.eq_empty_of_isEmpty t
  · rw [hs_empty]
    exact IsPavingAnalyticFor.empty 𝓚 hp_empty

-- He 1.26

-- He 1.26
lemma IsPavingAnalyticFor.iUnion {𝓚 : ℕ → Type*} {s : ℕ → Set 𝓧}
    (hs : ∀ n, IsPavingAnalyticFor p (𝓚 n) (s n)) :
    IsPavingAnalyticFor p (Σ n, 𝓚 n) (⋃ n, s n) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  let C := Prod.swap ''
    ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' (Set.sigma Set.univ (fun n ↦ Prod.swap '' (B n))))
  let q'' := {t : Set (Σ n, 𝓚 n) |
    ∃ s : Finset ℕ, t ∈ (s : Set ℕ).sigma '' (Set.univ.pi (fun n ↦ insert Set.univ (q n)))}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, q'']
    exact ⟨∅, fun _ ↦ Set.univ, by simp⟩
  · exact IsCompactSystem.sigma (fun n ↦ (hq_compact n).insert_univ)
  · unfold prodSigmaDelta at hB_prod
    simp_rw [mem_countableInfClosure_iff_iInf] at hB_prod
    choose A hA hB_eq using hB_prod
    have hC_eq : C = ⋂ k, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm ''
        (Set.sigma Set.univ (fun n ↦ Prod.swap '' (A n k)))) := by
      simp only [C, ← hB_eq]
      rw [← Set.image_iInter Prod.swap_bijective, ← Set.image_iInter (Equiv.bijective _)]
      simp only [Equiv.sigmaProdDistrib_symm_apply, Set.iInf_eq_iInter]
      simp_rw [Set.image_iInter Prod.swap_bijective]
      congr
      ext
      simp
    rw [hC_eq]
    refine countableInfClosed_countableInfClosure.iInf_mem fun k ↦ subset_countableInfClosure ?_
    simp_rw [mem_countableSupClosure_image2_prod_iff] at hA
    choose B hB K hK hA_eq using hA
    simp_rw [hA_eq]
    have h_eq : Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' ⋃ n_1, B n k n_1 ×ˢ K n k n_1)
      = ⋃ n_1, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' (B n k n_1 ×ˢ K n k n_1)) := by ext; simp; grind
    rw [h_eq]
    refine countableSupClosed_countableSupClosure.iSup_mem fun i ↦ ?_
    simp only [Set.image_swap_prod, Set.sigma_eq_biUnion, Set.mem_univ, Set.iUnion_true,
      Set.image_iUnion]
    refine countableSupClosed_countableSupClosure.iSup_mem fun j ↦ subset_countableSupClosure ?_
    refine ⟨B j k i, hB _ _ _, Sigma.mk j '' (K j k i), ?_, by ext; simp; grind⟩
    simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const, q'']
    refine ⟨{j}, fun j ↦ K j k i, ?_⟩
    simp only [Finset.coe_singleton, Set.singleton_sigma, and_true]
    exact fun m ↦ .inr (hK _ _ _)
  · simp only [hB_eq, Equiv.sigmaProdDistrib_symm_apply, C]
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Set.mem_sigma_iff, Set.mem_univ, Prod.swap_prod_mk, true_and, Sigma.exists, Prod.mk.injEq,
      ↓existsAndEq, exists_eq_right_right, Sigma.mk.injEq, and_true]
    grind

lemma IsPavingAnalytic.iUnion {s : ℕ → Set 𝓧} (hs : ∀ n, IsPavingAnalytic p (s n)) :
    IsPavingAnalytic p (⋃ n, s n) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.iUnion hs𝓚).isPavingAnalytic

-- He 1.26

-- He 1.26
lemma IsPavingAnalyticFor.union.{u} {𝓚 𝓚' : Type u} {t : Set 𝓧}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 ⊕ 𝓚') (s ∪ t) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  choose q' hq'_empty hq'_compact B' hB'_prod hB'_eq using ht
  let C : Set (𝓧 × (𝓚 ⊕ 𝓚')) :=
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (B, B')
  let q'' := {t | Sum.inl ⁻¹' t ∈ insert Set.univ q ∧ Sum.inr ⁻¹' t ∈ insert Set.univ q'}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_ofPred_eq,
      Set.subset_empty_iff, Set.range_eq_empty_iff, Set.preimage_empty, q'']
    exact ⟨.inr hq_empty, .inr hq'_empty⟩
  · exact IsCompactSystem.sum hq_compact.insert_univ hq'_compact.insert_univ
  · unfold prodSigmaDelta at hB_prod hB'_prod
    simp_rw [mem_countableInfClosure_iff_iInf] at hB_prod hB'_prod
    choose A hA hB_eq using hB_prod
    choose A' hA' hB'_eq using hB'_prod
    have hC_eq : C = ⋂ k,
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (A k, A' k) := by
      simp only [C, ← hB_eq, ← hB'_eq]
      rw [← Set.image_iInter (Equiv.bijective _)]
      congr
      calc Set.sumEquiv.symm (⋂ n, A n, ⋂ n, A' n)
      _ = Set.sumEquiv.symm (⨅ n, (A n, A' n)) := by
        congr 1
        ext <;> simp [iInf, Prod.fst_sInf, Prod.snd_sInf]
      _ = ⨅ n, Set.sumEquiv.symm (A n, A' n) := OrderIso.map_iInf _ _
      _ = ⋂ i, Set.sumEquiv.symm (A i, A' i) := rfl
    rw [hC_eq]
    refine countableInfClosed_countableInfClosure.iInf_mem fun k ↦ subset_countableInfClosure ?_
    simp_rw [mem_countableSupClosure_image2_prod_iff] at hA hA'
    choose B hB K hK hA_eq using hA
    choose B' hB' K' hK' hA'_eq using hA'
    simp_rw [hA_eq, hA'_eq]
    have h_eq : (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
        = ⋃ n, (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := by
      rw [← Set.image_iUnion]
      congr 1
      calc Set.sumEquiv.symm (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
      _ = Set.sumEquiv.symm (⨆ n, (B k n ×ˢ K k n, B' k n ×ˢ K' k n)) := by
        congr 1
        ext <;> simp [iSup, Prod.fst_sSup, Prod.snd_sSup]
      _ = ⨆ n, Set.sumEquiv.symm (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := OrderIso.map_iSup _ _
      _ = ⋃ i, Set.sumEquiv.symm (B k i ×ˢ K k i, B' k i ×ˢ K' k i) := rfl
    rw [h_eq]
    refine countableSupClosed_countableSupClosure.iSup_mem fun i ↦ ?_
    simp only [Set.sumEquiv, OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [Set.image_union]
    refine supClosed_countableSupClosure
      (subset_countableSupClosure ?_) (subset_countableSupClosure ?_)
    · refine ⟨B k i, hB _ _, Sum.inl '' (K k i), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_ofPred_eq,
          Set.preimage_inr_image_inl, q'']
        refine ⟨.inr ?_, .inr hq'_empty⟩
        convert hK k i
        ext
        simp
      · ext; simp [Equiv.prodSumDistrib]; grind
    · refine ⟨B' k i, hB' _ _, Sum.inr '' (K' k i), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_ofPred_eq,
          Set.preimage_inl_image_inr, q'']
        refine ⟨.inr hq_empty, .inr ?_⟩
        convert hK' k i
        ext
        simp
      · ext; simp [Equiv.prodSumDistrib]; grind
  · simp only [hB_eq, hB'_eq, C]
    ext
    simp [Equiv.prodSumDistrib, Equiv.sumProdDistrib, Set.sumEquiv]

lemma IsPavingAnalytic.union {t : Set 𝓧}
    (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∪ t) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  choose 𝓚' h𝓚' ht𝓚' using ht
  exact (IsPavingAnalyticFor.union hs𝓚 ht𝓚').isPavingAnalytic

lemma isPavingAnalyticFor_of_mem_countableSupClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableSupClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Σ _ : ℕ, 𝓚) s := by
  rw [mem_countableSupClosure_iff_iSup] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iUnion fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_mem_countableSupClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableSupClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  rw [mem_countableSupClosure_iff_iSup] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iUnion fun n ↦ hqp _ (hA n)

-- He 1.28

lemma IsPavingAnalyticFor.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 (t ×ˢ s) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : t ×ˢ s = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s')) := by
    ext; simp; grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s'), ?_, h_eq'⟩
  simp_rw [mem_prodSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ t ×ˢ A n m, fun n m ↦ ?_, K, hK, ?_⟩
  · exact ⟨t, ht, A n m, hA n m, rfl⟩
  · rw [Set.prod_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    congr with
    simp
    grind

lemma IsPavingAnalytic.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) (t ×ˢ s) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_left ht).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : r t) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 (s ×ˢ t) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : s ×ˢ t = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm ''
      (Prod.map id Prod.swap '' ((Equiv.prodAssoc _ _ _) '' (s' ×ˢ t)))) := by
    congr with
    simp
    grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm ''
      (Prod.map id Prod.swap '' ((Equiv.prodAssoc _ _ _) '' (s' ×ˢ t))), ?_, h_eq'⟩
  simp_rw [mem_prodSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ A n m ×ˢ t, fun n m ↦ ?_, K, hK, ?_⟩
  · exact ⟨A n m, hA n m, t, ht, rfl⟩
  · rw [Set.iInter_prod, Set.image_iInter (Equiv.prodAssoc _ _ _).bijective,
      Set.image_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    swap; · exact Function.bijective_id.prodMap Prod.swap_bijective
    congr with n x
    simp
    grind

lemma IsPavingAnalytic.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalytic p s) (ht : r t) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) (s ×ˢ t) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_right ht).isPavingAnalytic

lemma isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : t ∈ Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚)) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalytic_of_image2_prod_isPavingAnalytic_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : t ∈ Set.image2 (· ×ˢ ·) r (IsPavingAnalytic p)) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : t ∈ Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalytic_of_image2_prod_isPavingAnalytic_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : t ∈ Set.image2 (· ×ˢ ·) (IsPavingAnalytic p) r) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓨 × 𝓧)}
    (ht : t ∈ countableSupClosure (Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚))) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚)) ht fun s hs ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left hs

lemma isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓧 × 𝓨)}
    (ht : t ∈ countableSupClosure (Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r)) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r) ht fun s hs ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right hs

lemma IsPavingAnalyticFor.prod_mem_countableSupClosure_left {𝓨 : Type*} {r : Set (Set 𝓨)}
    {t : Set 𝓨} (ht : t ∈ countableSupClosure r) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) (Σ _ : ℕ, 𝓚) (t ×ˢ s) := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left ?_
  rw [mem_countableSupClosure_iff_iSup] at ht ⊢
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ A n ×ˢ s, fun n ↦ ⟨A n, hA n, s, hs, rfl⟩, ?_⟩
  simp only [Set.iSup_eq_iUnion]
  rw [Set.iUnion_prod_const]

lemma IsPavingAnalyticFor.prod_mem_countableSupClosure_right {𝓨 : Type*} {r : Set (Set 𝓨)}
    {t : Set 𝓨} (hs : IsPavingAnalyticFor p 𝓚 s) (ht : t ∈ countableSupClosure r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) (Σ _ : ℕ, 𝓚) (s ×ˢ t) := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right ?_
  rw [mem_countableSupClosure_iff_iSup] at ht ⊢
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ s ×ˢ A n, fun n ↦ ⟨s, hs, A n, hA n, rfl⟩, ?_⟩
  simp only [Set.iSup_eq_iUnion]
  rw [Set.prod_iUnion]

-- He 1.27

-- He 1.29

-- He 1.30
lemma IsPavingAnalyticFor.inter_set (hs : IsPavingAnalyticFor p 𝓚 s) (t : Set 𝓧) :
    IsPavingAnalyticFor {u | ∃ v, v ∈ p ∧ u = v ∩ t} 𝓚 (s ∩ t) := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  let A' := (t ×ˢ .univ) ∩ A
  refine ⟨q, hq_empty, hq, A', ?_, by ext; simp; grind⟩
  simp_rw [mem_prodSigmaDelta_iff] at hA ⊢
  obtain ⟨B, hB, K, hK, rfl⟩ := hA
  refine ⟨fun n m ↦ B n m ∩ t, fun n m ↦ ⟨B n m, hB n m, rfl⟩, K, hK, ?_⟩
  simp only [A']
  simp_rw [Set.inter_iInter, Set.inter_iUnion]
  congr with
  simp
  grind

-- He 1.30
lemma exists_isPavingAnalyticFor_of_inter_set (t : Set 𝓧)
    (hs : IsPavingAnalyticFor {u | ∃ v, v ∈ p ∧ u = v ∩ t} 𝓚 s) :
    ∃ s', IsPavingAnalyticFor p 𝓚 s' ∧ s = s' ∩ t := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  rw [mem_prodSigmaDelta_iff] at hA
  obtain ⟨B, hB, K, hK, rfl⟩ := hA
  choose A' hA' hBA' using hB
  refine ⟨Prod.fst '' (⋂ n, ⋃ m, A' n m ×ˢ K n m), ?_, ?_⟩
  · refine ⟨q, hq_empty, hq, ?_⟩
    refine ⟨⋂ n, ⋃ m, A' n m ×ˢ K n m, ?_, rfl⟩
    rw [mem_prodSigmaDelta_iff]
    exact ⟨A', hA', K, hK, rfl⟩
  · simp only [hBA']
    have h_eq n m : (A' n m ∩ t) ×ˢ K n m = (A' n m ×ˢ K n m) ∩ (t ×ˢ .univ) := by
      ext; simp; grind
    simp_rw [h_eq, ← Set.iUnion_inter, ← Set.iInter_inter]
    suffices h_eq' : ∀ (s : Set (𝓧 × 𝓚)), Prod.fst '' (s ∩ (t ×ˢ .univ)) = Prod.fst '' s ∩ t by
      rw [h_eq']
    intro s
    ext s
    simp

-- He 1.31

lemma Iic_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (u : ι) :
  Set.Iic u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  by_cases h_bot : ∃ x : ι, IsBot x
  · obtain ⟨x, hx_bot⟩ := h_bot
    refine subset_countableSupClosure ⟨x, u, ?_⟩
    ext y
    simp only [Set.mem_Icc, Set.mem_Iic, and_iff_right_iff_imp]
    exact fun _ ↦ hx_bot y
  obtain ⟨u₁, hu₁_anti, hu₁_tendsto⟩ := Filter.exists_seq_antitone_tendsto_atTop_atBot ι
  rw [mem_countableSupClosure_iff_iSup]
  refine ⟨fun n ↦ Set.Icc (u₁ n) u, fun n ↦ ⟨u₁ n, u, rfl⟩, ?_⟩
  ext x
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Icc, exists_and_right, Set.mem_Iic,
    and_iff_right_iff_imp]
  intro hxu
  exact (hu₁_tendsto.eventually_le_atBot x).exists

lemma Ici_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (u : ι) :
  Set.Ici u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  by_cases h_top : ∃ x : ι, IsTop x
  · obtain ⟨x, hx_top⟩ := h_top
    refine subset_countableSupClosure ⟨u, x, ?_⟩
    ext y
    simp only [Set.mem_Icc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun _ ↦ hx_top y
  obtain ⟨u₁, hu₁_anti, hu₁_tendsto⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  rw [mem_countableSupClosure_iff_iSup]
  refine ⟨fun n ↦ Set.Icc u (u₁ n), fun n ↦ ⟨u, u₁ n, rfl⟩, ?_⟩
  ext x
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Icc, exists_and_left, Set.mem_Ici,
    and_iff_left_iff_imp]
  intro hxu
  exact (hu₁_tendsto.eventually_ge_atTop x).exists

lemma Iio_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [DenselyOrdered ι]
    (u : ι) :
    Set.Iio u ∈ countableSupClosure (insert ∅ {t | ∃ a b, Set.Icc a b = t}) := by
  by_cases h_bot : IsBot u
  · have : Set.Iio u = ∅ := by
      ext x
      simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact h_bot x
    rw [this]
    refine subset_countableSupClosure (Or.inl rfl)
  obtain ⟨v, hvu⟩ : ∃ v, v < u := by simpa [IsBot] using h_bot
  obtain ⟨s, hs_mono, hs_lt, hs_tendsto⟩ := exists_seq_strictMono_tendsto' hvu
  have : Set.Iio u = ⋃ n, Set.Iic (s n) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    refine ⟨fun hxu ↦ ?_, fun ⟨i, hi⟩ ↦ hi.trans_lt (hs_lt i).2⟩
    exact (hs_tendsto.eventually_const_le hxu).exists
  rw [this]
  have h_mem := countableSupClosed_countableSupClosure.iSup_mem
    fun n ↦ Iic_mem_countableSupClosure_Icc (s n)
  exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs) h_mem

lemma Ioi_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [DenselyOrdered ι]
    (u : ι) :
    Set.Ioi u ∈ countableSupClosure (insert ∅ {t | ∃ a b, Set.Icc a b = t}) := by
  by_cases h_top : IsTop u
  · have : Set.Ioi u = ∅ := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
      exact h_top x
    rw [this]
    refine subset_countableSupClosure (Or.inl rfl)
  obtain ⟨v, huv⟩ : ∃ v, u < v := by simpa [IsTop] using h_top
  obtain ⟨s, hs_mono, hs_gt, hs_tendsto⟩ := exists_seq_strictAnti_tendsto' huv
  have : Set.Ioi u = ⋃ n, Set.Ici (s n) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
    refine ⟨fun hxu ↦ ?_, fun ⟨i, hi⟩ ↦ (hs_gt i).1.trans_le hi⟩
    exact (hs_tendsto.eventually_le_const hxu).exists
  rw [this]
  have h_mem := countableSupClosed_countableSupClosure.iSup_mem
    fun n ↦ Ici_mem_countableSupClosure_Icc (s n)
  exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs) h_mem

lemma univ_mem_countableSupClosure_Icc {ι : Type*} [hι : Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] :
    (Set.univ : Set ι) ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  obtain x : ι := hι.some
  have : (Set.univ : Set ι) = Set.Iic x ∪ Set.Ici x := by ext; simp
  rw [this]
  exact supClosed_countableSupClosure (Iic_mem_countableSupClosure_Icc x)
    (Ici_mem_countableSupClosure_Icc x)

lemma aux_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (l u : ι) :
    (Set.Icc l u)ᶜ ∈ countableSupClosure (insert ∅ {t | ∃ a b, Set.Icc a b = t}) := by
  rcases lt_or_ge u l with hlu | hlu
  · simp only [not_le, hlu, Set.Icc_eq_empty, Set.compl_empty]
    exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs)
      univ_mem_countableSupClosure_Icc
  · have : (Set.Icc l u)ᶜ = Set.Iio l ∪ Set.Ioi u := by ext; simp; grind
    rw [this]
    exact supClosed_countableSupClosure (Iio_mem_countableSupClosure_Icc l)
      (Ioi_mem_countableSupClosure_Icc u)

lemma aux'_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace 𝓧] (s : Set (𝓧 × ι))
    (hs : s ∈ Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) :
     sᶜ ∈ countableSupClosure
       (Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) := by
  obtain ⟨A, hA, K, hK_eq, rfl⟩ := hs
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq] at hK_eq
  cases hK_eq with
  | inl hK_eq =>
    simp only [hK_eq, Set.prod_empty, Set.compl_empty]
    refine (countableSupClosure_mono
      (a := Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ι, Set.Icc a b = t}) ?_) ?_
    · intro s hs
      refine mem_image2_prod_mono (p := Set.ofPred (MeasurableSet (α := 𝓧)))
        (q := {t | ∃ a b : ι, Set.Icc a b = t}) (fun _ hs ↦ hs) ?_ hs
      exact fun _ hs ↦ Set.mem_insert_of_mem _ hs
    have h_mem_sigma := univ_mem_countableSupClosure_Icc (ι := ι)
    rw [mem_countableSupClosure_iff_iSup] at h_mem_sigma ⊢
    obtain ⟨B, hB, h_eq⟩ := h_mem_sigma
    have h_univ_prod : (Set.univ : Set 𝓧) ×ˢ (Set.univ : Set ι) = Set.univ := by simp
    rw [← h_univ_prod, ← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
    refine ⟨fun i ↦ Set.univ ×ˢ B i, fun n ↦ ?_, rfl⟩
    exact ⟨Set.univ, .univ, B n, hB n, rfl⟩
  | inr hK_eq =>
    obtain ⟨l, u, rfl⟩ := hK_eq
    have hK' := aux_Icc l u
    rw [Set.compl_prod_eq_union]
    refine supClosed_countableSupClosure ?_ ?_
    · have h := univ_mem_countableSupClosure_Icc (ι := ι)
      rw [mem_countableSupClosure_iff_iSup] at h ⊢
      obtain ⟨B, hB, h_eq⟩ := h
      rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
      refine ⟨fun i ↦ Aᶜ ×ˢ B i, fun n ↦ ?_, rfl⟩
      exact ⟨Aᶜ, hA.compl, B n, Set.mem_insert_of_mem _ (hB n), rfl⟩
    · have h := aux_Icc l u
      rw [mem_countableSupClosure_iff_iSup] at h ⊢
      obtain ⟨B, hB, h_eq⟩ := h
      rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
      refine ⟨fun i ↦ Set.univ ×ˢ B i, fun n ↦ ?_, rfl⟩
      exact ⟨Set.univ, .univ, B n, hB n, rfl⟩

lemma borel_eq_generateFrom_isCompact :
    borel ℝ = MeasurableSpace.generateFrom {s : Set ℝ | IsCompact s} := by
  refine le_antisymm ?_ ?_
  · rw [borel_eq_generateFrom_Icc]
    refine MeasurableSpace.generateFrom_mono fun s hs ↦ ?_
    obtain ⟨a, b, hab, rfl⟩ := hs
    exact isCompact_Icc
  · rw [MeasurableSpace.generateFrom_le_iff]
    exact fun _ hs ↦ hs.measurableSet

lemma borel_eq_generateFrom_Icc' (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ (l u : α), Set.Icc l u = S } := by
  rw [borel_eq_generateFrom_Icc]
  refine le_antisymm ?_ ?_
  · exact MeasurableSpace.generateFrom_mono fun s ⟨l, u, hlu, hs⟩ ↦ ⟨l, u, hs⟩
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro - ⟨a, b, rfl⟩
    rcases le_or_gt a b with hab | hab
    · exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, hab, rfl⟩
    · simp [hab]

lemma borel_eq_generateFrom_Icc'' (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom (insert ∅ { S : Set α | ∃ (l u : α), Set.Icc l u = S }) := by
  rw [MeasurableSpace.generateFrom_insert_empty]
  exact borel_eq_generateFrom_Icc' α

-- Icc variant of He 1.32 (1)

lemma isCountablySpanning_isCompact : IsCountablySpanning (IsCompact (X := ℝ)) := by
  refine ⟨fun n : ℕ ↦ Set.Icc (-n : ℝ) n, fun _ ↦ isCompact_Icc, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true, ← abs_le]
  exact ⟨⌈|x|⌉₊, Nat.le_ceil _⟩

lemma isCountablySpanning_Icc : IsCountablySpanning {t | ∃ a b : ℝ, Set.Icc a b = t} := by
  refine ⟨fun n : ℕ ↦ Set.Icc (-n : ℝ) n, fun n ↦ ⟨-n, n, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true, ← abs_le]
  exact ⟨⌈|x|⌉₊, Nat.le_ceil _⟩

lemma isCountablySpanning_insert_empty_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] :
    IsCountablySpanning (insert ∅ {t | ∃ a b : ι, Set.Icc a b = t}) := by
  have h := univ_mem_countableSupClosure_Icc (ι := ι)
  rw [mem_countableSupClosure_iff_iSup] at h
  obtain ⟨A, hA, h_eq⟩ := h
  exact ⟨A, fun n ↦ Set.mem_insert_of_mem _ (hA n), h_eq⟩

-- Icc version of He 1.32 (2)

-- Icc version of He 1.32 (2)

-- Icc version of He 1.32 (3)
-- note that here `ι` is in `Type`, not `Type*`

/-- A set `s` of a measurable space `𝓧` is measurably analytic for a measurable space `𝓚` if it
is the projection of a measurable set of `𝓧 × 𝓚`. -/
def IsMeasurableAnalyticFor (𝓚 : Type*) [MeasurableSpace 𝓚] [MeasurableSpace 𝓧] (s : Set 𝓧) :
    Prop :=
  ∃ t : Set (𝓧 × 𝓚), MeasurableSet t ∧ s = Prod.fst '' t

lemma isMeasurableAnalyticFor_of_snd {_ : MeasurableSpace 𝓚} [MeasurableSpace 𝓧]
    {s : Set 𝓧} (t : Set (𝓚 × 𝓧)) (ht : MeasurableSet t) (hst : s = Prod.snd '' t) :
    IsMeasurableAnalyticFor 𝓚 s :=
  ⟨Prod.swap ⁻¹' t, ht.preimage (by fun_prop), by ext; simp [hst]⟩

/-- A set `s` of a measurable space `𝓧` is measurably analytic if it is the projection of
a measurable set of `𝓧 × ℝ`. -/
def IsMeasurableAnalytic [MeasurableSpace 𝓧] (s : Set 𝓧) : Prop := IsMeasurableAnalyticFor ℝ s

lemma isMeasurableAnalytic_of_snd [MeasurableSpace 𝓧] {s : Set 𝓧} (t : Set (ℝ × 𝓧))
    (ht : MeasurableSet t) (hst : s = Prod.snd '' t) :
    IsMeasurableAnalytic s :=
  isMeasurableAnalyticFor_of_snd t ht hst

/-- If a set is measurably analytic for any standard Borel space `𝓚`,
then it is measurably analytic for `ℝ`. -/
lemma IsMeasurableAnalyticFor.isMeasurableAnalytic {m𝓧 : MeasurableSpace 𝓧}
    {m𝓚 : MeasurableSpace 𝓚} [StandardBorelSpace 𝓚]
    (hs : IsMeasurableAnalyticFor 𝓚 s) :
    IsMeasurableAnalytic s := by
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨Prod.map id (embeddingReal 𝓚) '' t, ?_, by ext; simp⟩
  refine MeasurableEmbedding.measurableSet_image' ?_ ht
  exact MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal 𝓚)

end MeasureTheory
