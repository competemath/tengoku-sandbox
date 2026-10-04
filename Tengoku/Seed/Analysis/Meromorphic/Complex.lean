/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Meromorphic.NormalForm
public import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma function is meromorphic
-/

public section

open Set Complex

lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

-- TODO: restate `MeromorphicNFOn.Gamma` when `MeromorphicNF` is defined

@[fun_prop]
lemma Meromorphic.Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

@[fun_prop]
lemma MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s :=
  Meromorphic.Gamma.meromorphicOn
