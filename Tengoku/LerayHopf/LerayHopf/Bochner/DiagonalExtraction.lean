/-
# LerayHopf.Bochner.DiagonalExtraction — abstract diagonal-subsequence machinery

Abstract, PDE-independent diagonal-subsequence lemma for a nested family of strictly
monotone extraction maps.  Fully proved (no `sorry`, no project axioms — kernel-trio
only).  Promoted verbatim from the issue #195 feasibility spike; the mathematics is
unchanged.

Given per-stage extractions `e m` (stage `m` extracts from the stage-`(m-1)` family),
the composed maps `nestedComp e m = e 0 ∘ e 1 ∘ ⋯ ∘ e m` are the absolute extractions
of each stage, and the diagonal `δ k = nestedComp e k k` is a single strictly monotone
extraction whose `m`-shifted tail refines EVERY stage: `δ (m + j) = nestedComp e m (ψ j)`
with `ψ` strictly monotone.  Consequently any limit that holds along stage `m` transfers
to the diagonal (`tendsto_diag_of_tendsto_stage`).

Depends only on mathlib's `Filter.atTop` order machinery — no PDE / analysis imports —
so it serves as the domain-neutral diagonal engine consumed by `Torus/DiagonalGalerkin.lean`.
-/
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

open Filter

namespace LerayHopf.Bochner

/-- Composed stage extraction: `nestedComp e m = e 0 ∘ e 1 ∘ ⋯ ∘ e m`.
`e (m+1)` is the stage-(m+1) extraction *relative to* stage `m`, so the absolute
extraction composes on the right. -/
def nestedComp (e : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => e 0
  | m + 1 => nestedComp e m ∘ e (m + 1)

@[simp] theorem nestedComp_zero (e : ℕ → ℕ → ℕ) : nestedComp e 0 = e 0 := rfl

@[simp] theorem nestedComp_succ (e : ℕ → ℕ → ℕ) (m : ℕ) :
    nestedComp e (m + 1) = nestedComp e m ∘ e (m + 1) := rfl

theorem nestedComp_strictMono {e : ℕ → ℕ → ℕ} (he : ∀ m, StrictMono (e m)) :
    ∀ m, StrictMono (nestedComp e m)
  | 0 => he 0
  | m + 1 => (nestedComp_strictMono he m).comp (he (m + 1))

/-- Relative extraction from stage `m` to stage `m + j`:
`tailComp e m j = e (m+1) ∘ e (m+2) ∘ ⋯ ∘ e (m+j)` (identity for `j = 0`). -/
def tailComp (e : ℕ → ℕ → ℕ) (m : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | j + 1 => tailComp e m j ∘ e (m + j + 1)

theorem tailComp_strictMono {e : ℕ → ℕ → ℕ} (he : ∀ m, StrictMono (e m)) (m : ℕ) :
    ∀ j, StrictMono (tailComp e m j)
  | 0 => strictMono_id
  | j + 1 => (tailComp_strictMono he m j).comp (he (m + j + 1))

/-- Stage decomposition: the absolute stage-(m+j) extraction factors through stage m. -/
theorem nestedComp_add (e : ℕ → ℕ → ℕ) (m : ℕ) :
    ∀ j, nestedComp e (m + j) = nestedComp e m ∘ tailComp e m j
  | 0 => rfl
  | j + 1 => by
      show nestedComp e (m + j) ∘ e (m + j + 1)
          = nestedComp e m ∘ (tailComp e m j ∘ e (m + j + 1))
      rw [nestedComp_add e m j]
      rfl

/-- The diagonal extraction `δ k = (e 0 ∘ ⋯ ∘ e k) k`. -/
def diagExtraction (e : ℕ → ℕ → ℕ) (k : ℕ) : ℕ := nestedComp e k k

theorem diagExtraction_strictMono {e : ℕ → ℕ → ℕ} (he : ∀ m, StrictMono (e m)) :
    StrictMono (diagExtraction e) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : diagExtraction e (k + 1) = nestedComp e k (e (k + 1) (k + 1)) := rfl
  have h2 : k + 1 ≤ e (k + 1) (k + 1) := (he (k + 1)).le_apply
  calc diagExtraction e k = nestedComp e k k := rfl
    _ < nestedComp e k (k + 1) := (nestedComp_strictMono he k) (Nat.lt_succ_self k)
    _ ≤ nestedComp e k (e (k + 1) (k + 1)) := (nestedComp_strictMono he k).monotone h2
    _ = diagExtraction e (k + 1) := h1.symm

/-- The `m`-shifted diagonal is an extraction of stage `m`, via the strictly
monotone reindexing `ψ j = tailComp e m j (m + j)`. -/
theorem diagExtraction_tail {e : ℕ → ℕ → ℕ} (he : ∀ m, StrictMono (e m)) (m : ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ j, diagExtraction e (m + j) = nestedComp e m (ψ j) := by
  refine ⟨fun j => tailComp e m j (m + j), ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    have h1 : tailComp e m (j + 1) (m + (j + 1))
        = tailComp e m j (e (m + j + 1) (m + j + 1)) := rfl
    have h2 : m + j + 1 ≤ e (m + j + 1) (m + j + 1) := (he (m + j + 1)).le_apply
    calc tailComp e m j (m + j)
        < tailComp e m j (m + j + 1) :=
          (tailComp_strictMono he m j) (Nat.lt_succ_self _)
      _ ≤ tailComp e m j (e (m + j + 1) (m + j + 1)) :=
          (tailComp_strictMono he m j).monotone h2
      _ = tailComp e m (j + 1) (m + (j + 1)) := h1.symm
  · intro j
    show nestedComp e (m + j) (m + j) = nestedComp e m (tailComp e m j (m + j))
    rw [nestedComp_add e m j]
    rfl

/-- **The abstract diagonal-subsequence lemma** (packaged form).  From any family of
per-stage strictly monotone extractions there is ONE strictly monotone diagonal `δ`
such that, for every stage `m`, the `m`-shifted tail of `δ` is an extraction of the
stage-`m` composed subsequence. -/
theorem exists_diagonal_extraction (e : ℕ → ℕ → ℕ) (he : ∀ m, StrictMono (e m)) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧
      ∀ m, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, δ (m + j) = nestedComp e m (ψ j) :=
  ⟨diagExtraction e, diagExtraction_strictMono he, fun m => diagExtraction_tail he m⟩

/-- **Limit-transfer workhorse:** any filter limit that holds along the stage-`m`
subsequence holds along the diagonal.  This is exactly the shape used at each fixed
time `t ∈ [0, m]` for the weak pairings `k ↦ ⟪u_{δ(k)}(t), z⟫`. -/
theorem tendsto_diag_of_tendsto_stage {α : Type*} {e : ℕ → ℕ → ℕ}
    (he : ∀ m, StrictMono (e m)) {f : ℕ → α} {l : Filter α} (m : ℕ)
    (hf : Tendsto (fun j => f (nestedComp e m j)) atTop l) :
    Tendsto (fun k => f (diagExtraction e k)) atTop l := by
  obtain ⟨ψ, hψ, hdiag⟩ := diagExtraction_tail he m
  have htail : Tendsto (fun j => f (diagExtraction e (m + j))) atTop l := by
    have hcomp : Tendsto (fun j => f (nestedComp e m (ψ j))) atTop l :=
      hf.comp hψ.tendsto_atTop
    refine hcomp.congr fun j => ?_
    rw [hdiag j]
  have hshift : Tendsto (fun j => f (diagExtraction e (j + m))) atTop l := by
    refine htail.congr fun j => ?_
    rw [Nat.add_comm m j]
  exact (tendsto_add_atTop_iff_nat m).mp hshift

end LerayHopf.Bochner
