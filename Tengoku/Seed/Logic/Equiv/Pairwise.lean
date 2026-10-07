/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Tengoku.Seed.Data.FunLike.Equiv
public import Tengoku.Seed.Logic.Pairwise

/-!
# Interaction of equivalences with `Pairwise`
-/

public section

open scoped Function -- required for scoped `on` notation

/--
@isnad1 id=pairwise.1h5v.s5.04196785a777 from=seed src=0 shape=b2c7c45a vocab=b9572343
-/
lemma EmbeddingLike.pairwise_comp {X : Type*} {Y : Type*} {F} [FunLike F Y X] [EmbeddingLike F Y X]
    (f : F) {p : X → X → Prop} (h : Pairwise p) : Pairwise (p on f) :=
  h.comp_of_injective <| EmbeddingLike.injective f

/--
@isnad1 id=iff.0h5v.s5.3f32c4baefc8 from=seed src=0 shape=a4837d9a vocab=8dbc4048
-/
lemma EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
    (f : F) (p : X → X → Prop) : Pairwise (p on f) ↔ Pairwise p :=
  (EquivLike.bijective f).pairwise_comp_iff
