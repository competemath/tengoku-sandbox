/-
# LerayHopf.Bochner.ScalarEquicontinuity — domain-neutral scalar equicontinuity engine

Built for the torus `aubin_lions` removal (issue #23), but domain-neutral: nothing here is
torus-specific.

This file is a **domain-neutral, PDE-free, torus-free** scalar analysis engine.
It depends only on Mathlib (real analysis, uniform convergence, filters, intervals)
and introduces **no** `LerayHopf.*` import — preserving full reusability for both
the T³ and ℝ³ Galerkin applications.

## Main declaration

- `exists_uniform_subseq_of_lipschitz_family` — given a doubly-indexed family of
  real curves `f m n : ℝ → ℝ` on `[0,T]` that is (a) uniformly bounded in `m` and
  (b) per-family eventually Lipschitz in `n` (with cutoff `n₀ m`), produces ONE
  strictly monotone subsequence `φ : ℕ → ℕ` along which every family member `f m (φ ·)`
  converges uniformly on `[0,T]`.  The proof outline is Bolzano–Weierstrass on
  `ℚ ∩ [0,T]` + Cantor diagonal + eventual-Lipschitz ⇒ uniform Cauchy.

## Assumptions

No axioms are introduced (`axiom` count: 0).
Scaffold sorry count: 0.
-/

-- `ℝ` with ordered-field, metric, and uniform-space instances
-- (`Topology.Instances.Rat` → `Topology.Algebra.Ring.Real` → `Topology.UniformSpace.Real`)
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq
-- `TendstoUniformlyOn`, `TendstoUniformlyOnFilter`, uniform-space API
-- `atTop` filter on ordered types (`Filter.atTop`) and `StrictMono`
-- Sequential compactness of compact first-countable spaces (`IsCompact.tendsto_subseq`)
-- Metric characterisations of uniform/Cauchy convergence (`Metric.uniformCauchySeqOn_iff`,
-- `Metric.cauchySeq_iff`, `Metric.ball`, `cauchySeq_tendsto_of_complete`, `Real.dist_eq`)
-- Compactness of `Icc` on `ℝ` (`isCompact_Icc`) and `isCompact_univ_pi`
-- Pointwise-limit characterisation of `𝓝` on a product (`tendsto_pi_nhds`)
-- `Encodable ℚ` ⇒ `Countable ℚ`, so the rational parameter set is a countable index
-- (needed for second-countability of the sample product space)

namespace LerayHopf

open Set Filter Topology

/-! ## P0.4 (S3) — scalar compactness engine (domain-neutral)

Uniformly bounded + per-family eventually-Lipschitz countable family of real curve
sequences on `[0,T]` ⇒ ONE subsequence along which every family member converges
uniformly.  Bolzano–Weierstrass on `ℚ ∩ [0,T]` + Cantor diagonal + eventual-Lipschitz
⇒ uniform Cauchy.  Scalar-elementary; no Bochner machinery. -/

/-- Given a doubly-indexed family `f : ℕ → ℕ → ℝ → ℝ` of curves on `[0,T]` that is
uniformly bounded (`|f m n t| ≤ B m` for all `t ∈ [0,T]`) and per-family eventually
Lipschitz (`∀ m, ∃ n₀, ∀ n ≥ n₀, |f m n t - f m n s| ≤ L m * (t - s)` for `s ≤ t`
in `[0,T]`), there exists a strictly monotone subsequence `φ : ℕ → ℕ` such that for
every `m` the sequence `n ↦ f m (φ n)` converges uniformly on `[0,T]`.

The eventual-Lipschitz form of `hlip` (cutoff `n₀ m`, not all-`n`) is load-bearing:
the Galerkin application supplies the Lipschitz estimate only for `n` past the test's
band-limit cutoff (`m ≤ n` in P0.3).  Uniform convergence along a subsequence is a
tail property, so the engine absorbs the finite prefix without loss. -/
theorem exists_uniform_subseq_of_lipschitz_family
    (T : ℝ) (hT : 0 < T) (f : ℕ → ℕ → ℝ → ℝ) (B L : ℕ → ℝ)
    (hb : ∀ m n t, t ∈ Icc (0 : ℝ) T → |f m n t| ≤ B m)
    (hlip : ∀ m, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s t,
      s ∈ Icc (0 : ℝ) T → t ∈ Icc (0 : ℝ) T → s ≤ t →
      |f m n t - f m n s| ≤ L m * (t - s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ m, ∃ g : ℝ → ℝ,
        TendstoUniformlyOn (fun n t => f m (φ n) t) g atTop (Icc (0 : ℝ) T) := by
  classical
  -- Stage 1 (simultaneous Bolzano–Weierstrass).  The countable parameter set is the
  -- rationals inside `[0,T]`.  Along the product `∏_{(m,q)} [-(B m), B m]` — a compact,
  -- second-countable (hence sequentially compact) space — the sample sequence
  -- `n ↦ (m,q ↦ f m n q)` has a convergent subsequence.  Coordinatewise convergence is
  -- exactly pointwise convergence of `f m (φ ·) q` for every `m` and every rational
  -- `q ∈ [0,T]`, all along ONE subsequence `φ`.
  have hScompact : IsCompact (Set.univ.pi
      (fun j : ℕ × {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T} => Icc (-(B j.1)) (B j.1))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨a, -, φ, hφ, hconv⟩ := IsCompact.tendsto_subseq hScompact
      (x := fun n j => f j.1 n ((j.2 : ℚ) : ℝ))
      (fun n => by
        rw [mem_univ_pi]
        intro j
        simp only [mem_Icc]
        rw [← abs_le]
        exact hb j.1 n ((j.2 : ℚ) : ℝ) j.2.2)
  have hpt : ∀ (m : ℕ) (q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T}),
      Tendsto (fun n => f m (φ n) ((q : ℚ) : ℝ)) atTop (𝓝 (a (m, q))) := by
    intro m q
    simpa only [Function.comp_apply] using tendsto_pi_nhds.mp hconv (m, q)
  refine ⟨φ, hφ, ?_⟩
  intro m
  obtain ⟨n₀, hn₀⟩ := hlip m
  -- The Lipschitz constant is nonnegative (it dominates a nonnegative quantity over `t-s>0`).
  have hLnn : 0 ≤ L m := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl _, hT.le⟩
    have hTm : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨hT.le, le_refl _⟩
    have h := hn₀ n₀ (le_refl _) 0 T h0 hTm hT.le
    have hpos : (0 : ℝ) ≤ L m * (T - 0) := le_trans (abs_nonneg _) h
    nlinarith [hpos, hT]
  -- Two-sided eventual-Lipschitz estimate for the subsequenced curves.
  have hlip2 : ∀ k, n₀ ≤ k → ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
      |f m (φ k) a - f m (φ k) b| ≤ L m * |a - b| := by
    intro k hk a b ha hb
    have hk' : n₀ ≤ φ k := le_trans hk hφ.le_apply
    rcases le_total b a with hba | hab
    · have h := hn₀ (φ k) hk' b a hb ha hba
      rw [show |a - b| = a - b from abs_of_nonneg (by linarith)]
      exact h
    · have h := hn₀ (φ k) hk' a b ha hb hab
      rw [show |a - b| = b - a by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith),
        abs_sub_comm (f m (φ k) a)]
      exact h
  -- Stage 2 (dense pointwise convergence + eventual-Lipschitz ⇒ uniform Cauchy).
  have hUC : UniformCauchySeqOn (fun k t => f m (φ k) t) atTop (Icc (0 : ℝ) T) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    -- Net gap `δ`: makes the Lipschitz contribution over one net cell `≤ ε/4`.
    set δ : ℝ := ε / (4 * (L m + 1)) with hδ
    have hδpos : 0 < δ := by rw [hδ]; exact div_pos hε (by linarith [hLnn])
    have hCδ : L m * δ ≤ ε / 4 := by
      have hδdef : δ * (4 * (L m + 1)) = ε := by
        rw [hδ]; exact div_mul_cancel₀ ε (by positivity)
      nlinarith [hδpos, hLnn, hδdef]
    -- A finite `δ`-net of `[0,T]` made of rationals lying inside `[0,T]`.
    have hcover : Icc (0 : ℝ) T ⊆
        ⋃ q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T}, Metric.ball ((q : ℚ) : ℝ) δ := by
      intro t ht
      obtain ⟨htl, htr⟩ := ht
      have hab : max 0 (t - δ) < min T (t + δ) :=
        lt_min (max_lt hT (by linarith)) (max_lt (by linarith) (by linarith))
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1)
      have hqT : ((q : ℝ)) ≤ T := le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))
      refine mem_iUnion.2 ⟨⟨q, ⟨hq0, hqT⟩⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have : (q : ℝ) < t + δ := lt_of_lt_of_le hq2 (min_le_right _ _)
        linarith
      · have : t - δ < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
        linarith
    obtain ⟨Fin, hFin⟩ := isCompact_Icc.elim_finite_subcover
      (fun q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T} => Metric.ball ((q : ℚ) : ℝ) δ)
      (fun _ => Metric.isOpen_ball) hcover
    -- Pointwise Cauchy at each net rational (stage-1 convergence ⇒ Cauchy).
    have hCauchyPt : ∀ q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T}, ∃ N : ℕ,
        ∀ k ≥ N, ∀ l ≥ N,
          dist (f m (φ k) ((q : ℚ) : ℝ)) (f m (φ l) ((q : ℚ) : ℝ)) < ε / 4 := by
      intro q
      exact (Metric.cauchySeq_iff.mp (hpt m q).cauchySeq) (ε / 4) (by positivity)
    choose Nfun hNfun using hCauchyPt
    refine ⟨max n₀ (Fin.sup Nfun), fun k hk l hl t ht => ?_⟩
    have hkn₀ : n₀ ≤ k := le_trans (le_max_left _ _) hk
    have hln₀ : n₀ ≤ l := le_trans (le_max_left _ _) hl
    obtain ⟨q, hqF, hqb⟩ := mem_iUnion₂.1 (hFin ht)
    have htq : |t - ((q : ℚ) : ℝ)| < δ := by
      have h := Metric.mem_ball.1 hqb; rwa [Real.dist_eq] at h
    -- The three ε/4 pieces of the standard ε/3-style estimate.
    have e1 : |f m (φ k) t - f m (φ k) ((q : ℚ) : ℝ)| ≤ ε / 4 :=
      le_trans (le_trans (hlip2 k hkn₀ t ((q : ℚ) : ℝ) ht q.2)
        (mul_le_mul_of_nonneg_left (le_of_lt htq) hLnn)) hCδ
    have e3 : |f m (φ l) ((q : ℚ) : ℝ) - f m (φ l) t| ≤ ε / 4 :=
      le_trans (le_trans (hlip2 l hln₀ ((q : ℚ) : ℝ) t q.2 ht)
        (mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact le_of_lt htq) hLnn)) hCδ
    have hkNf : Nfun q ≤ k := le_trans (le_trans (Finset.le_sup hqF) (le_max_right _ _)) hk
    have hlNf : Nfun q ≤ l := le_trans (le_trans (Finset.le_sup hqF) (le_max_right _ _)) hl
    have e2 : |f m (φ k) ((q : ℚ) : ℝ) - f m (φ l) ((q : ℚ) : ℝ)| < ε / 4 := by
      have h := hNfun q k hkNf l hlNf; rwa [Real.dist_eq] at h
    rw [Real.dist_eq]
    have t1 := abs_sub_le (f m (φ k) t) (f m (φ k) ((q : ℚ) : ℝ)) (f m (φ l) t)
    have t2 := abs_sub_le (f m (φ k) ((q : ℚ) : ℝ)) (f m (φ l) ((q : ℚ) : ℝ)) (f m (φ l) t)
    linarith [t1, t2, e1, e2, e3, hε]
  -- The uniform limit `g`: a uniformly Cauchy sequence converges pointwise in complete `ℝ`.
  have hlim : ∀ t ∈ Icc (0 : ℝ) T, ∃ y, Tendsto (fun k => f m (φ k) t) atTop (𝓝 y) :=
    fun t ht => cauchySeq_tendsto_of_complete (hUC.cauchySeq ht)
  choose! g hg using hlim
  exact ⟨g, hUC.tendstoUniformlyOn_of_tendsto (fun t ht => hg t ht)⟩

end LerayHopf
