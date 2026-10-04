/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith
-/
module

public import Tengoku
/-!
# fderiv currying lemmas

Various lemmas related to fderiv on curried/uncurried functions.

-/

@[expose] public section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma fderiv_uncurry (f : X → Y → Z) (xy dxy : X × Y)
    (hf : DifferentiableAt 𝕜 (↿f) xy) :
    fderiv 𝕜 ↿f xy dxy
    =
    fderiv 𝕜 (f · xy.2) xy.1 dxy.1 + fderiv 𝕜 (f xy.1 ·) xy.2 dxy.2 := by
  have hx : (f · xy.2) = ↿f ∘ (fun x' => (x',xy.2)) := by rfl
  have hy : (f xy.1 ·) = ↿f ∘ (fun y' => (xy.1,y')) := by rfl
  rw [hx,hy]
  repeat rw [fderiv_comp (hg := by fun_prop) (hf := by fun_prop)]
  dsimp
  rw [← ContinuousLinearMap.map_add]
  congr
  repeat rw [DifferentiableAt.fderiv_prodMk (hf₁ := by fun_prop) (hf₂ := by fun_prop)]
  simp

lemma fderiv_uncurry_clm_comp (f : X → Y → Z) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 ↿f
    =
    fun xy =>
      (fderiv 𝕜 (f · xy.2) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (f xy.1 ·) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) := by
  funext xy
  apply ContinuousLinearMap.ext
  intro dxy
  rw [fderiv_uncurry]
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd']
  fun_prop

lemma fderiv_wrt_prod_clm_comp (f : X × Y → Z) (hf : Differentiable 𝕜 f) :
    fderiv 𝕜 f
    =
    fun xy =>
      (fderiv 𝕜 (fun x' => f (x',xy.2)) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (fun y' => f (xy.1,y')) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) :=
  fderiv_uncurry_clm_comp (fun x y => f (x,y)) hf

lemma fderiv_curry_clm_apply (f : X → Y →L[𝕜] Z) (y : Y) (x dx : X) (h : Differentiable 𝕜 f) :
    fderiv 𝕜 f x dx y
    =
    fderiv 𝕜 (f · y) x dx := by
  rw [fderiv_clm_apply] <;> first | simp | fun_prop

/- Helper rw lemmas for proving differentiability conditions. -/

/- Differentiability conditions. -/

@[fun_prop]
lemma fderiv_uncurry_differentiable_fst (f : X → Y → Z) (y : Y) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 fun x' => (↿f) (x', y)) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_snd (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 fun y' => (↿f) (x, y')) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_fst_comp_snd (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun y' => fderiv 𝕜 (fun x' => (↿f) (x', y')) x) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_snd_comp_fst (f : X → Y → Z) (y : Y) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun x' => fderiv 𝕜 (fun y' => (↿f) (x', y')) y) := by
  fun_prop

/- fderiv commutes on X × Y. -/
lemma fderiv_swap [IsRCLikeNormedField 𝕜] (f : X → Y → Z) (x dx : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    fderiv 𝕜 (fun x' => fderiv 𝕜 (fun y' => f x' y') y dy) x dx
    =
    fderiv 𝕜 (fun y' => fderiv 𝕜 (fun x' => f x' y') x dx) y dy := by
  have hf' : IsSymmSndFDerivAt 𝕜 (↿f) (x,y) := by
    apply ContDiffAt.isSymmSndFDerivAt (n := 2)
    · exact ContDiff.contDiffAt hf
    · simp
  have h := IsSymmSndFDerivAt.eq hf' (dx,0) (0,dy)
  rw [fderiv_wrt_prod_clm_comp, fderiv_wrt_prod_clm_comp] at h
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd', map_zero,
    add_zero, zero_add] at h
  rw [fderiv_curry_clm_apply, fderiv_curry_clm_apply] at h
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', Function.comp_apply, map_zero, ContinuousLinearMap.coe_snd',
    zero_add, add_zero] at h
  exact h
  /- Start of differentiability conditions. -/
  · fun_prop
  · fun_prop
  · exact hf.differentiable (by simp)
  · fun_prop
