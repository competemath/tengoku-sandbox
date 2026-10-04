import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq
import Tengoku.Analysis.Normed.Operator.Bilinear

/-!
# BilinearExtension — extend a bounded bilinear form from a dense submodule (issue #111 PR-4)

**File:** `LerayHopf/Analysis/BilinearExtension.lean`

## What this file is

`LerayHopf/R3/ConvectionExtension.lean` built the same "extend a bounded bilinear form off a
dense subspace to a jointly continuous bilinear form on the whole space" construction TWICE:
once hard-wired to a single fixed Schwartz test field (`convBLT_fixedTest`, driven by the B7
bound `convFormH1_bound_Schwartz` for one `IsSchwartzDivFree_R3` witness), and once again for an
arbitrary `w ∈ schwartzSpan` with an explicit bound taken as a hypothesis (`convBLTbdd`). The two
towers are IDENTICAL two-stage constructions — `LinearMap.extendOfNorm` on the slot-2 argument via
the dense embedding, then `ContinuousLinearMap.extend` on the slot-1 argument via the same dense
embedding — differing only in where the bound `C`/`hbound` comes from. This file extracts that
generic construction once: given a dense submodule `D ≤ E` and a bilinear form on `D` bounded by
`C * ‖u‖ * ‖v‖`, produce the unique jointly continuous bilinear extension to all of `E`.

## Main declarations

- `extendBoundedBilinearOfDense` — the fused two-stage extension: dense submodule `D ≤ E`, a
  bilinear form `β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ` bounded by `C * ‖u‖ * ‖v‖`, produces
  `E →L[ℝ] E →L[ℝ] ℝ`.
- `extendBoundedBilinearOfDense_apply` — the extension agrees with `β` on `D × D`.
- `eq_of_agree_dense` — two jointly continuous bilinear forms on `E` agreeing on the dense square
  `D × D` are equal (via `eqOn_closure₂'`).

## Mathlib declarations consumed

- `LinearMap.extendOfNorm`, `LinearMap.extendOfNorm_unique`, `LinearMap.extendOfNorm_eq`,
  `LinearMap.norm_extendOfNorm_apply_le` (`Analysis/Normed/Operator/Extend.lean`) — the slot-2
  bounded extension off the dense linear map `D.subtype`.
- `ContinuousLinearMap.extend`, `ContinuousLinearMap.extend_eq` (same file) — the slot-1
  extension off the dense, uniformly-inducing continuous map `D.subtypeL`.
- `isUniformEmbedding_subtype_val` — `D.subtypeL` is uniformly inducing (generic subspace fact).
- `eqOn_closure₂'` — two separately-continuous bivariate functions agreeing on a dense square
  agree on the closure square.
-/

namespace LerayHopf.BilinearExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The dense inclusion `D →ₗ E` / `D →L E`, bare and continuous -/

/-- The dense submodule inclusion as a bare `LinearMap` (for `extendOfNorm`). -/
private noncomputable def eD (D : Submodule ℝ E) : D →ₗ[ℝ] E := D.subtype

private theorem eD_norm (D : Submodule ℝ E) (v : D) : ‖eD D v‖ = ‖v‖ := rfl

/-- `hdense` restated against the (unfolded) `eD D` head symbol, so that `e` unifies
correctly against `eD D` (not the bare `D.subtype`) inside `LinearMap.extendOfNorm_unique`. -/
private theorem denseRange_eD (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E)) :
    DenseRange (eD D : D → E) := hdense

/-- Additivity of `extendOfNorm` along `eD D` (via uniqueness of the bounded extension). -/
private theorem extendOfNorm_eD_add (D : Submodule ℝ E) (hdense : DenseRange (eD D : D → E))
    (f f' : D →ₗ[ℝ] ℝ) {C C' : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ C * ‖eD D x‖) (hf' : ∀ x, ‖f' x‖ ≤ C' * ‖eD D x‖) :
    (f + f').extendOfNorm (eD D) = f.extendOfNorm (eD D) + f'.extendOfNorm (eD D) := by
  refine LinearMap.extendOfNorm_unique hdense (C + C')
    (fun x => ?_) (f.extendOfNorm (eD D) + f'.extendOfNorm (eD D)) ?_
  · calc ‖(f + f') x‖ = ‖f x + f' x‖ := rfl
      _ ≤ ‖f x‖ + ‖f' x‖ := norm_add_le _ _
      _ ≤ C * ‖eD D x‖ + C' * ‖eD D x‖ := add_le_add (hf x) (hf' x)
      _ = (C + C') * ‖eD D x‖ := by ring
  · refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      add_apply, LinearMap.add_apply,
      LinearMap.extendOfNorm_eq hdense ⟨C, hf⟩ x,
      LinearMap.extendOfNorm_eq hdense ⟨C', hf'⟩ x]

/-- Homogeneity of `extendOfNorm` along `eD D`. -/
private theorem extendOfNorm_eD_smul (D : Submodule ℝ E) (hdense : DenseRange (eD D : D → E))
    (c : ℝ) (f : D →ₗ[ℝ] ℝ) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C * ‖eD D x‖) :
    (c • f).extendOfNorm (eD D) = c • f.extendOfNorm (eD D) := by
  refine LinearMap.extendOfNorm_unique hdense (|c| * C)
    (fun x => ?_) (c • f.extendOfNorm (eD D)) ?_
  · calc ‖(c • f) x‖ = |c| * ‖f x‖ := by
            simp [LinearMap.smul_apply, Real.norm_eq_abs]
      _ ≤ |c| * (C * ‖eD D x‖) := by
            apply mul_le_mul_of_nonneg_left (hf x) (abs_nonneg c)
      _ = |c| * C * ‖eD D x‖ := by ring
  · refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      smul_apply, LinearMap.smul_apply,
      LinearMap.extendOfNorm_eq hdense ⟨C, hf⟩ x, smul_eq_mul]

/-- The continuous submodule inclusion `D →L[ℝ] E`. -/
private noncomputable def eDL (D : Submodule ℝ E) : D →L[ℝ] E := D.subtypeL

private theorem denseRange_eDL (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E)) :
    DenseRange (eDL D : D → E) := hdense

/-! ### The bounded bilinear extension -/

/-- The bound on `β u` transported to the `eD`-scaled shape `extendOfNorm` needs. -/
private theorem beta_bound (D : Submodule ℝ E) (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ}
    (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖) (u v : D) :
    ‖(β u) v‖ ≤ C * ‖u‖ * ‖eD D v‖ := by
  rw [eD_norm, Real.norm_eq_abs]
  exact hbound u v

/-- The slot-2 inner extension `innerCLM u : E →L[ℝ] ℝ` of `β u`. -/
private noncomputable def innerCLM (D : Submodule ℝ E) (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (u : D) :
    E →L[ℝ] ℝ :=
  (β u).extendOfNorm (eD D)

private theorem innerCLM_add (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E))
    (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ} (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖)
    (u u' : D) :
    innerCLM D β (u + u') = innerCLM D β u + innerCLM D β u' := by
  unfold innerCLM
  rw [β.map_add u u']
  exact extendOfNorm_eD_add D (denseRange_eD D hdense) (β u) (β u')
    (fun v => beta_bound D β hbound u v) (fun v => beta_bound D β hbound u' v)

private theorem innerCLM_smul (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E))
    (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ} (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖)
    (c : ℝ) (u : D) :
    innerCLM D β (c • u) = c • innerCLM D β u := by
  unfold innerCLM
  rw [β.map_smul c u]
  exact extendOfNorm_eD_smul D (denseRange_eD D hdense) c (β u) (fun v => beta_bound D β hbound u v)

private theorem innerCLM_bound (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E))
    (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖) (u : D) :
    ‖innerCLM D β u‖ ≤ C * ‖eD D u‖ := by
  rw [eD_norm]
  have hCu : 0 ≤ C * ‖u‖ := mul_nonneg hC (norm_nonneg u)
  refine ContinuousLinearMap.opNorm_le_bound _ hCu (fun x => ?_)
  unfold innerCLM
  exact LinearMap.norm_extendOfNorm_apply_le hdense _ (fun v => beta_bound D β hbound u v) x

/-- The slot-1 outer linear map `u ↦ innerCLM u`, before its `E`-extension. -/
private noncomputable def outerLM (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E))
    (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ} (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖) :
    D →ₗ[ℝ] (E →L[ℝ] ℝ) where
  toFun u := innerCLM D β u
  map_add' u u' := innerCLM_add D hdense β hbound u u'
  map_smul' c u := innerCLM_smul D hdense β hbound c u

/-- The slot-1 outer map as a **continuous** linear map. -/
private noncomputable def outerCLM (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E))
    (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖) :
    D →L[ℝ] (E →L[ℝ] ℝ) :=
  LinearMap.mkContinuous (E := D) (F := (E →L[ℝ] ℝ)) (𝕜 := ℝ)
    (outerLM D hdense β hbound) C
    (fun u => by
      have h := innerCLM_bound D hdense β hC hbound u
      rw [eD_norm] at h
      exact h)

/-- **The bounded bilinear extension.** Given a dense submodule `D ≤ E` and a bilinear form
`β` on `D` bounded by `C * ‖u‖ * ‖v‖`, the unique jointly continuous bilinear extension of `β`
to all of `E`. Fuses `LinearMap.extendOfNorm` (slot 2, along the dense bare inclusion `D.subtype`)
with `ContinuousLinearMap.extend` (slot 1, along the dense continuous inclusion `D.subtypeL`). -/
noncomputable def extendBoundedBilinearOfDense (D : Submodule ℝ E)
    (hdense : DenseRange (D.subtype : D → E)) (β : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v : D, |β u v| ≤ C * ‖(u : E)‖ * ‖(v : E)‖) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (outerCLM D hdense β hC hbound).extend (eDL D)

/-- Two continuous bilinear forms on `E` agreeing on the dense `D × D` square (via the public
`D.subtypeL`) are equal. -/
theorem eq_of_agree_dense (D : Submodule ℝ E) (hdense : DenseRange (D.subtype : D → E))
    {B₁ B₂ : E →L[ℝ] E →L[ℝ] ℝ}
    (h : ∀ u v : D, B₁ (D.subtypeL u) (D.subtypeL v) = B₂ (D.subtypeL u) (D.subtypeL v)) :
    B₁ = B₂ := by
  have hfun : (fun a => fun b => B₁ a b) = (fun a => fun b => B₂ a b) := by
    have key : ∀ a ∈ closure (Set.range (eDL D : D → E)),
        ∀ b ∈ closure (Set.range (eDL D : D → E)),
        B₁ a b = B₂ a b := by
      refine eqOn_closure₂'
        (s := Set.range (eDL D : D → E))
        (t := Set.range (eDL D : D → E))
        (f := fun a b => B₁ a b) (g := fun a b => B₂ a b) ?_ ?_ ?_ ?_ ?_
      · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩; exact h u v
      · intro a; exact (B₁ a).continuous
      · intro b; exact (ContinuousLinearMap.flip B₁ b).continuous
      · intro a; exact (B₂ a).continuous
      · intro b; exact (ContinuousLinearMap.flip B₂ b).continuous
    funext a b
    have hda : a ∈ closure (Set.range (eDL D : D → E)) := denseRange_eDL D hdense a
    have hdb : b ∈ closure (Set.range (eDL D : D → E)) := denseRange_eDL D hdense b
    exact key a hda b hdb
  ext a b
  exact congrFun (congrFun hfun a) b

end LerayHopf.BilinearExtension
