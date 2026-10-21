/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# Problem 6: Large epsilon-light vertex subsets -- Laplacian Basics

Basic definitions: edge Laplacian, graph Laplacian, induced Laplacian,
epsilon-lightness. Fundamental properties: PSD, symmetry, equivalence
with mathlib's `lapMatrix`.

## Main definitions

- `Problem6.graphLaplacian`: graph Laplacian as sum of edge Laplacians
- `Problem6.inducedLaplacian`: Laplacian of the induced subgraph on S
- `Problem6.inducedSubgraph`: the induced subgraph on S as a `SimpleGraph V`
- `Problem6.IsEpsLight`: epsilon-lightness predicate

## Main theorems

- `Problem6.graphLaplacian_eq_lapMatrix`: equivalence with mathlib
- `Problem6.graphLaplacian_posSemidef`: graph Laplacian is PSD
- `Problem6.graphLaplacian_isHermitian`: graph Laplacian is symmetric
- `Problem6.inducedLaplacian_eq_lapMatrix`: inducedLaplacian = (inducedSubgraph G S).lapMatrix ℝ
- `Problem6.lapMatrix_loewner_mono`: Loewner monotonicity for lapMatrix
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Laplacian matrix of a simple graph, defined as ∑_{e ∈ E} L_e
    where each L_e is the edge Laplacian.
    We use the standard definition L_{ij} = deg(i) if i=j, -1 if i~j, 0 otherwise. -/
def graphLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (G.Adj i)).card : ℝ)
    else if G.Adj i j then -1
    else 0

/-- The Laplacian of the induced subgraph on S: restricting to edges within S. -/
def inducedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (fun k => i ∈ S ∧ k ∈ S ∧ G.Adj i k)).card : ℝ)
    else if G.Adj i j ∧ i ∈ S ∧ j ∈ S then -1
    else 0

/-- A set S is ε-light if εL - L_S is positive semidefinite. -/
def IsEpsLight (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (S : Finset V) : Prop :=
  (ε • graphLaplacian G - inducedLaplacian G S).PosSemidef

/-! ### The induced subgraph as a SimpleGraph V

Using Mathlib's `Subgraph.induce` and `Subgraph.spanningCoe` to construct the induced
subgraph on S as a `SimpleGraph V`, connecting to Mathlib's `lapMatrix` API. -/

/-- The induced subgraph of G on S, as a `SimpleGraph V`.
    Uses Mathlib's `Subgraph.induce` + `spanningCoe` to stay in `SimpleGraph V`. -/
noncomputable abbrev inducedSubgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : SimpleGraph V :=
  ((⊤ : G.Subgraph).induce (↑S)).spanningCoe

instance inducedSubgraph.instDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : DecidableRel (inducedSubgraph G S).Adj := by
  intro v w
  simp only [inducedSubgraph, SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj, Finset.mem_coe]
  infer_instance

omit [Fintype V] [DecidableEq V] in
/-- Adjacency in the induced subgraph:
`(inducedSubgraph G S).Adj v w ↔ G.Adj v w ∧ v ∈ S ∧ w ∈ S`.
@isnad1 id=iff.0h5v.s5.ba82c12136c1 from=translated src=- shape=45477997 vocab=0b576085
-/
lemma inducedSubgraph_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v w : V) :
    (inducedSubgraph G S).Adj v w ↔ G.Adj v w ∧ v ∈ S ∧ w ∈ S := by
  simp only [inducedSubgraph, SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj, Finset.mem_coe]
  tauto

omit [Fintype V] [DecidableEq V] in
/-- The induced subgraph is a subgraph of G.
@isnad1 id=le.0h3v.s4.19a647f2ebdc from=translated src=- shape=3316f5a4 vocab=631d6fe4
-/
lemma inducedSubgraph_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : inducedSubgraph G S ≤ G :=
  fun _ _ h => ((inducedSubgraph_adj G S _ _).mp h).1

/-- The graph Laplacian equals the Mathlib lapMatrix (degree minus adjacency).
@isnad1 id=eq.0h2v.s5.6f2c547aeb87 from=translated src=- shape=f8bad52d vocab=ed0a4650
-/
lemma graphLaplacian_eq_lapMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphLaplacian G = G.lapMatrix ℝ := by
  ext i j
  simp only [graphLaplacian, Matrix.of_apply, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
             SimpleGraph.adjMatrix, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.of_apply]
  split_ifs with h1 h2
  · -- i = j, G.Adj i j: impossible for simple graph
    subst h1; exact absurd h2 (SimpleGraph.irrefl G)
  · -- i = j, ¬G.Adj i j
    subst h1
    simp only [sub_zero]; norm_cast
    rw [← SimpleGraph.card_neighborFinset_eq_degree]; congr 1
    simp [SimpleGraph.neighborFinset_eq_filter]
  · -- i ≠ j, G.Adj i j
    norm_num
  · -- i ≠ j, ¬G.Adj i j
    norm_num

/-- The graph Laplacian is positive semidefinite.
    xᵀLx = ∑_{u~v} (x_u - x_v)² ≥ 0.
@isnad1 id=possemid.0h2v.s4.f9ce6385f853 from=translated src=- shape=816774ba vocab=c3ce9fab
-/
lemma graphLaplacian_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (graphLaplacian G).PosSemidef := by
  rw [graphLaplacian_eq_lapMatrix]
  exact SimpleGraph.posSemidef_lapMatrix ℝ G

/-! ### Loewner monotonicity for lapMatrix -/

end Problem6

end
