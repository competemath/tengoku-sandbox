import Tengoku
import Tengoku.Formalslt.FormalSLT.Covering.FiniteSubGaussianChaining
import Tengoku.Formalslt.FormalSLT.Probability.SubGaussianFiniteMax

/-!
# Finite Dudley chaining sum

This module records the finite n-step chaining sum used by the Dudley
bridge. It keeps the statement finite: finite outcome space, finite index
class, finite nets, and a finite scale range.

The level bound uses the one-sided finite sub-Gaussian maximum inequality
from `FormalSLT.Probability.SubGaussianFiniteMax`.
-/

namespace FormalSLT.Covering.DudleyChainingSum

open Finset
open scoped BigOperators
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Probability.SubGaussianFiniteMax

noncomputable section

variable {Ω T : Type*}

/-- Exact telescoping identity for a chain of finite-net projections. -/
theorem dudley_chaining_telescope
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (X : T → ℝ) (m : ℕ) (t t₀ : T)
    (hroot : (N 0).projection t = t₀)
    (hlast : (N m).projection t = t) :
    X t - X t₀ =
      ∑ j ∈ Finset.range m,
        (X ((N (j + 1)).projection t) - X ((N j).projection t)) := by
  let π : ℕ → T → T := fun j => (N j).projection
  have ht :
      X t =
        X t₀ + ∑ j ∈ Finset.range m,
          (X ((N (j + 1)).projection t) - X ((N j).projection t)) := by
    simpa [π, hroot] using
      chain_telescope X π m t (by simpa [π] using hlast)
  rw [ht]
  ring

end

end FormalSLT.Covering.DudleyChainingSum
