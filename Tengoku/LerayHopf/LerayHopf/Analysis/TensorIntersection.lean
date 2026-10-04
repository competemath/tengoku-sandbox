import Tengoku

/-!
# TensorIntersection — the `S⊗V ∩ V⊗S = S⊗S` lemma

**File:** `LerayHopf/Analysis/TensorIntersection.lean`

A general linear-algebra fact needed for the convection-operator construction
(issue #56): inside `V ⊗ V`, the image of `S ⊗ V` and the image of `V ⊗ S`
intersect in exactly the image of `S ⊗ S`.

**Namespace note (issue #113 PR-2).** This file was relocated here from
`LerayHopf/R3/TensorIntersection.lean` (it has zero project imports and is pure
linear algebra, so it belongs in the generic `Analysis/` layer, not the R3 lane) —
but its namespace, `LerayHopf.R3.TensorIntersection`, is kept AS-IS this round for
name stability (its 3 callers reference the fully-qualified name). The path/namespace
mismatch is a known, deliberate leftover of this move, not an oversight.

This is the algebraic glue that lets a bilinear form which is determined on the
sum `(S⊗V) + (V⊗S)` of the two "edge" subspaces be reconstructed consistently:
the two prescriptions agree precisely on `S⊗S`, which is their overlap.

## Main statement

`TensorProduct.range_map_subtype_inf_range_map_subtype`:
for a field `K`, a `K`-vector space `V`, and a submodule `S : Submodule K V`,
```
LinearMap.range (TensorProduct.map S.subtype LinearMap.id)
  ⊓ LinearMap.range (TensorProduct.map LinearMap.id S.subtype)
  = LinearMap.range (TensorProduct.mapIncl S S)
```
where `TensorProduct.mapIncl S S = TensorProduct.map S.subtype S.subtype`.

## Proof strategy (idempotent projection)

`S` admits a complement `q` in `V` (`Submodule.exists_isCompl`, valid because `K`
is a (division ring / field), so `V` is a free `K`-module). `TensorProduct K V V`
requires `K` commutative, so we take `K` to be a field (matching the intended
`K = ℝ`). The associated projection
`P := S.projection q : V →ₗ[K] V` is idempotent with `range P = S` and acts as the
identity on `S` (so `P ∘ₗ S.subtype = S.subtype`).

The tensor map `T := TensorProduct.map P P` then satisfies `range T = S⊗S`, and:
- `map P id` fixes every element of `range (map S.subtype id)` (the `S⊗V` image),
- `map id P` fixes every element of `range (map id S.subtype)` (the `V⊗S` image),

so on the intersection `T x = map P id (map id P x) = x`, placing `x` in `range T = S⊗S`.

## Mathlib declarations used

- `Submodule.exists_isCompl` (needs a division ring; a field suffices)
- `Submodule.projection`, `Submodule.range_projection`,
  `Submodule.projection_apply_left`
- `TensorProduct.map`, `TensorProduct.mapIncl`, `TensorProduct.range_map`,
  `TensorProduct.map_map`, `TensorProduct.range_map_mono`
- `Submodule.map₂` monotonicity (`range_map` rewrites the tensor ranges into `map₂`)

No `sorry`, no new `axiom`.
-/

open TensorProduct LinearMap

namespace LerayHopf.R3.TensorIntersection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Auxiliary: if a projection `P : V →ₗ[K] V` restricts to the identity on a
submodule `S` (i.e. `P ∘ₗ S.subtype = S.subtype`), then the tensor map
`map P id` fixes every element of `range (map S.subtype id)`. -/
theorem map_proj_id_fix_of_mem_range
    {S : Submodule K V} {P : V →ₗ[K] V} (hP : P ∘ₗ S.subtype = S.subtype)
    {x : TensorProduct K V V}
    (hx : x ∈ LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : V →ₗ[K] V))) :
    TensorProduct.map P (LinearMap.id : V →ₗ[K] V) x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [TensorProduct.map_map, hP, LinearMap.comp_id]

/-- Auxiliary: symmetric version for the second tensor slot. -/
theorem map_id_proj_fix_of_mem_range
    {S : Submodule K V} {P : V →ₗ[K] V} (hP : P ∘ₗ S.subtype = S.subtype)
    {x : TensorProduct K V V}
    (hx : x ∈ LinearMap.range (TensorProduct.map (LinearMap.id : V →ₗ[K] V) S.subtype)) :
    TensorProduct.map (LinearMap.id : V →ₗ[K] V) P x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [TensorProduct.map_map, hP, LinearMap.comp_id]

/-- **Main lemma (issue #56).** Inside `V ⊗ V`, the image of `S ⊗ V` and the image
of `V ⊗ S` intersect in exactly the image of `S ⊗ S`.

Stated for a general `DivisionRing K`, `K`-vector space `V`, and submodule
`S : Submodule K V`. The two outer ranges are the images of `S ⊗ V` and `V ⊗ S`;
the right-hand side `range (mapIncl S S)` is the image of `S ⊗ S`. -/
theorem range_map_subtype_inf_range_map_subtype (S : Submodule K V) :
    LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : V →ₗ[K] V))
        ⊓ LinearMap.range (TensorProduct.map (LinearMap.id : V →ₗ[K] V) S.subtype)
      = LinearMap.range (TensorProduct.mapIncl S S) := by
  -- Pick a complement and the associated idempotent projection `P` onto `S`.
  obtain ⟨q, hq⟩ := S.exists_isCompl
  set P : V →ₗ[K] V := S.projection q hq with hPdef
  -- `P` restricts to the identity on `S`.
  have hPsub : P ∘ₗ S.subtype = S.subtype := by
    ext x
    simp [hPdef, Submodule.projection_apply_left hq]
  -- `range P = S`.
  have hPrange : LinearMap.range P = S := by
    rw [hPdef]; exact Submodule.range_projection hq
  -- `range (map P P) = range (mapIncl S S)`: both compute to `map₂ (mk) S S`.
  have hTrange :
      LinearMap.range (TensorProduct.map P P)
        = LinearMap.range (TensorProduct.mapIncl S S) := by
    rw [TensorProduct.range_map, TensorProduct.range_mapIncl, hPrange]
  apply le_antisymm
  · -- `⊆`: on the intersection, `map P P` fixes `x`, so `x ∈ range (map P P) = S⊗S`.
    rintro x ⟨hxSV, hxVS⟩
    have hx : TensorProduct.map P P x = x := by
      have hstep : TensorProduct.map P P x
          = TensorProduct.map P (LinearMap.id : V →ₗ[K] V)
              (TensorProduct.map (LinearMap.id : V →ₗ[K] V) P x) := by
        rw [TensorProduct.map_map]; simp
      rw [hstep, map_id_proj_fix_of_mem_range hPsub hxVS,
        map_proj_id_fix_of_mem_range hPsub hxSV]
    rw [← hTrange]
    exact ⟨x, hx⟩
  · -- `⊇`: `S⊗S ⊆ S⊗V` and `S⊗S ⊆ V⊗S`, by range monotonicity.
    apply le_inf
    · -- `range (mapIncl S S) ≤ range (map S.subtype id)`.
      refine TensorProduct.range_map_mono ?_ ?_
      · exact le_rfl
      · simp [Submodule.range_subtype]
    · -- `range (mapIncl S S) ≤ range (map id S.subtype)`.
      refine TensorProduct.range_map_mono ?_ ?_
      · simp [Submodule.range_subtype]
      · exact le_rfl

end LerayHopf.R3.TensorIntersection
