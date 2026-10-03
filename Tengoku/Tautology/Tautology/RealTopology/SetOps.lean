import Tengoku.Tautology.Tautology.Foundation.SetPred

/-!
# Set vocabulary, re-exported into the topology

A single import and nothing else. It brings `Tautology.Foundation.SetPred` --
subset, extensional sameness, empty, universal, complement, union,
intersection, difference, singleton on predicate-valued sets -- into this
region, so that `Tautology.RealTopology.Closed` and everything downstream can
phrase openness and closedness in set language without reaching into
`Foundation` directly.

Pure re-export module: it declares nothing. Note that the set operations
themselves are not topological and carry no field structure; they live in
`Foundation` precisely because nothing about them depends on the line.
-/
