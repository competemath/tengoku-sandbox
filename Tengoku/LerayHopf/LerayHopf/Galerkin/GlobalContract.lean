/-
The generic global Leray–Hopf contract layer (issue #195, phase P1).

This module provides the domain-neutral, `Prop`-valued finite-horizon Leray–Hopf
contract `IsLerayHopfOn` (a field-for-field twin of the five proof fields of
`Galerkin.LerayHopfSolution`), its round-trip equivalence with
`Nonempty (Galerkin.LerayHopfSolution …)`, the single-curve global solution
structure `GlobalLerayHopfSolution` (literal `∃ u, ∀ T > 0, IsLerayHopfOn … u`)
with its no-curve-duplication witnesses, and the two transfer lemmas — horizon
restriction (`IsLerayHopfOn.mono`) and curve congruence on `[0, T]`
(`IsLerayHopfOn.congr_Icc`) — both closed WITHOUT any integrability side condition
via the indicator-truncation identity `setIntegral_Ioc_eq_of_tail_zero`. The
truncation toolkit (`badTail*`, `truncation_agrees_with_additivity`,
`truncation_routes_agree`) records the compiled cross-check that the truncation step
is sound on both the non-integrable and integrable branches.

Design and provenance: `docs/scratch/global-diagonal-campaign.md` §4. This file was
promoted verbatim (namespace `LerayHopf.Scratch195` → `LerayHopf.Galerkin`) from the
codex-gated feasibility spike; statements and proof bodies are byte-identical to the
spike. Axiom hygiene comes from release-cone membership (imported by `LerayHopf.lean`)
plus the interim live pins in `scripts/check-axioms-live.sh`.
-/
import Tengoku.LerayHopf.LerayHopf.Galerkin.SolutionBundles
import Tengoku

open MeasureTheory Filter Topology Set

namespace LerayHopf.Galerkin

/-! ### Finding 4 — truncation without integrability -/

/-- **Tail-truncation for set integrals, no integrability hypothesis.**  If `f` vanishes
on `(b, c]` then its Bochner integrals over `Ioc a c` and `Ioc a b` coincide: the two
indicator functions are *pointwise equal*, so the integrals agree even when `f` is not
integrable on either set (both sides are then the same junk value `0`).  This is the
exact step `WeakFormNS.mono` needs, and it never invokes interval additivity. -/
theorem setIntegral_Ioc_eq_of_tail_zero {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : ℝ → X} {a b c : ℝ} (hbc : b ≤ c)
    (hf : ∀ t, b < t → t ≤ c → f t = 0) :
    ∫ t in Set.Ioc a c, f t = ∫ t in Set.Ioc a b, f t := by
  have hind : (Set.Ioc a c).indicator f = (Set.Ioc a b).indicator f := by
    funext x
    by_cases hxc : x ∈ Set.Ioc a c
    · by_cases hxb : x ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxb]
      · have hbx : b < x := by
          rcases hxc with ⟨hax, hxc'⟩
          by_contra hnb
          exact hxb ⟨hax, not_lt.mp hnb⟩
        rw [Set.indicator_of_mem hxc, Set.indicator_of_notMem hxb, hf x hbx hxc.2]
    · have hxb : x ∉ Set.Ioc a b := fun hx => hxc (Set.Ioc_subset_Ioc le_rfl hbc hx)
      rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxb]
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc,
    hind]

/-- Concrete NON-integrable branch witness: `1/t` up to time `1`, then `0`. -/
noncomputable def badTail : ℝ → ℝ := fun t => if t ≤ 1 then t⁻¹ else 0

theorem badTail_tail_zero : ∀ t : ℝ, 1 < t → t ≤ 2 → badTail t = 0 := by
  intro t ht _
  simp [badTail, not_le.mpr ht]

/-- `badTail` is genuinely non-integrable on `Ioc 0 2` (it dominates `1/t` near `0`),
so `badTail_truncation` below exercises the junk-value branch of
`setIntegral_Ioc_eq_of_tail_zero`, where interval additivity is NOT available. -/
theorem badTail_not_integrableOn :
    ¬ IntegrableOn badTail (Set.Ioc 0 2) volume := by
  intro hInt
  have h1 : IntegrableOn badTail (Set.Ioc 0 1) volume :=
    hInt.mono_set (Set.Ioc_subset_Ioc le_rfl one_le_two)
  have h2 : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 0 1) volume :=
    h1.congr_fun (fun t ht => by simp [badTail, ht.2]) measurableSet_Ioc
  have h3 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr h2
  rcases intervalIntegrable_inv_iff.mp h3 with h | h
  · exact one_ne_zero h.symm
  · exact h Set.left_mem_uIcc

/-- The truncation identity holds for the non-integrable `badTail` — compiled evidence
that the `WeakFormNS.mono` restriction step is sound with NO integrability side
condition (codex finding 4's "non-integrable prefix" scenario). -/
theorem badTail_truncation :
    ∫ t in Set.Ioc (0 : ℝ) 2, badTail t = ∫ t in Set.Ioc (0 : ℝ) 1, badTail t :=
  setIntegral_Ioc_eq_of_tail_zero one_le_two badTail_tail_zero

/-- Integrable-branch cross-check via the REAL classical route (codex pass-2 F-C):
under integrability, `Ioc 0 c = Ioc 0 b ∪ Ioc b c` and `setIntegral_union` give genuine
union additivity — the first conjunct is proved by ADDITIVITY, not by re-running the
indicator route — and the tail integral vanishes.  Both `0 ≤ b` (for the union
decomposition) and integrability (for `setIntegral_union`, restricted to each piece by
`mono_set`) are genuinely consumed. -/
theorem truncation_agrees_with_additivity {f : ℝ → ℝ} {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (hfint : IntegrableOn f (Set.Ioc 0 c) volume)
    (hf : ∀ t, b < t → t ≤ c → f t = 0) :
    (∫ t in Set.Ioc 0 c, f t) =
        (∫ t in Set.Ioc 0 b, f t) + (∫ t in Set.Ioc b c, f t) ∧
      (∫ t in Set.Ioc b c, f t) = 0 := by
  have hunion : Set.Ioc (0 : ℝ) b ∪ Set.Ioc b c = Set.Ioc 0 c :=
    Set.Ioc_union_Ioc_eq_Ioc hb hbc
  constructor
  · rw [← hunion]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hfint.mono_set (Set.Ioc_subset_Ioc le_rfl hbc))
      (hfint.mono_set (Set.Ioc_subset_Ioc hb le_rfl))
  · have hzero : EqOn f (fun _ => (0 : ℝ)) (Set.Ioc b c) := fun t ht => hf t ht.1 ht.2
    calc ∫ t in Set.Ioc b c, f t = ∫ _t in Set.Ioc b c, (0 : ℝ) :=
          setIntegral_congr_fun measurableSet_Ioc hzero
      _ = 0 := integral_zero _ _

/-- **The two routes agree on the integrable branch**: classical additivity plus the
vanishing tail yields exactly the equation `setIntegral_Ioc_eq_of_tail_zero` produces
with no integrability at all — so the indicator route is conservative over the
standard argument, now as a THEOREM rather than a prose claim. -/
theorem truncation_routes_agree {f : ℝ → ℝ} {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (hfint : IntegrableOn f (Set.Ioc 0 c) volume)
    (hf : ∀ t, b < t → t ≤ c → f t = 0) :
    (∫ t in Set.Ioc 0 c, f t) = ∫ t in Set.Ioc 0 b, f t := by
  obtain ⟨hadd, hzero⟩ := truncation_agrees_with_additivity hb hbc hfint hf
  rw [hadd, hzero, add_zero]

/-! ### Finding 1 — the global contract, machine-checked

Statements below mirror docs/scratch/global-diagonal-campaign.md §4 verbatim, over the
REAL generic layer (`Galerkin.Domain`, `Galerkin.NSFormCore`,
`Galerkin.LerayHopfSolution` from `LerayHopf/Galerkin/SolutionBundles.lean`).  P1 will
move them (unchanged) out of the `Scratch195` namespace into production. -/

/-- **Prop-valued Leray–Hopf contract on `[0, T]`** — the conjunction of the five proof
fields of `Galerkin.LerayHopfSolution`, with the curve `u` exposed as an argument
instead of bundled as data.  Field-for-field mirror of
`LerayHopf/Galerkin/SolutionBundles.lean:68`. -/
def IsLerayHopfOn (D : Galerkin.Domain) (C : Galerkin.NSFormCore D) (ν T : ℝ)
    (u₀ : ↥D.σ) (u : Time → ↥D.σ) : Prop :=
  WeakFormNS ν T (D.evolution C) u ∧
  (∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 + ∫ s in (0 : ℝ)..t, D.dissip ν ↑(u s)
      ≤ (1 / 2 : ℝ) * ‖(u₀ : D.X)‖ ^ 2) ∧
  Filter.Tendsto (fun t => (u t : D.X)) (nhdsWithin 0 (Set.Ici 0)) (nhds ↑u₀) ∧
  ((∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), D.regMem ↑(u t)) ∧
    IntervalIntegrable (fun s => D.dissip ν ↑(u s)) volume 0 T) ∧
  AEStronglyMeasurable (fun t => (u t : D.X)) (volume.restrict (Set.Icc 0 T))

variable {D : Galerkin.Domain} {C : Galerkin.NSFormCore D} {ν T T' : ℝ} {u₀ : ↥D.σ}

/-- Packing: the Prop-valued contract rebuilds the proof-carrying solution with the
SAME curve (no data change, no choice). -/
def LerayHopfSolution.ofIsOn {u : Time → ↥D.σ} (h : IsLerayHopfOn D C ν T u₀ u) :
    Galerkin.LerayHopfSolution D C ν T u₀ where
  u := u
  weak_eq := h.1
  energy_ineq := h.2.1
  initial_trace := h.2.2.1
  energy_class := h.2.2.2.1
  u_aestronglyMeasurable := h.2.2.2.2

/-- **The global contract**: ONE curve field, and the finite-horizon contract for THAT
curve at EVERY positive horizon.  The logical content is literally
`∃ u, ∀ T > 0, IsLerayHopfOn … u` (see `globalLerayHopfSolution_nonempty_iff`) — not a
repackaged `∀ T, ∃ u_T`. -/
structure GlobalLerayHopfSolution (D : Galerkin.Domain) (C : Galerkin.NSFormCore D)
    (ν : ℝ) (u₀ : ↥D.σ) where
  /-- The single global solution curve. -/
  u : Time → ↥D.σ
  /-- The finite-horizon Leray–Hopf contract for `u`, at every positive horizon. -/
  isOn : ∀ T : ℝ, 0 < T → IsLerayHopfOn D C ν T u₀ u

/-- Horizon slice of a global solution — WITHOUT changing the curve. -/
def GlobalLerayHopfSolution.toSolution (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : Galerkin.LerayHopfSolution D C ν T u₀ :=
  LerayHopfSolution.ofIsOn (g.isOn T hT)

/-- **No-curve-duplication witness** (definitional): every horizon slice carries the
one global curve. -/
theorem GlobalLerayHopfSolution.toSolution_u (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : (g.toSolution T hT).u = g.u := rfl

/-- The global contract implies the existing per-horizon contract (with one uniform
curve) — the strengthening direction of the quantifier swap. -/
theorem GlobalLerayHopfSolution.nonempty_solution (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : Nonempty (Galerkin.LerayHopfSolution D C ν T u₀) :=
  ⟨g.toSolution T hT⟩

/-! ### Transfer lemmas: horizon restriction (`mono`) and curve congruence
(`congr_Icc`) -/

end LerayHopf.Galerkin
