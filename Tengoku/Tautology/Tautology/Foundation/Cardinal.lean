import Tengoku.Tautology.Tautology.Foundation.Cardinal.Maps
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Choice
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Finite
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Countable
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Pairing
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Union
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Sum
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Arithmetic
import Tengoku.Tautology.Tautology.Foundation.Cardinal.CantorBernstein
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Cantor
import Tengoku.Tautology.Tautology.Foundation.Cardinal.Continuum

/-!
# Subtree entry: cardinality

One import covering the eleven modules of `Foundation/Cardinal/`, which
develop size comparison from nothing. The order they are built in:

`Maps` fixes the vocabulary -- injections, surjections, `CardLE` by the first
and `CardGE` by the second -- and proves only what needs no choice. `Choice`
inverts maps and is the single place `Classical.choice` enters this subtree;
the two directions it establishes are not symmetric, one of them needing the
target to be nonempty. `Finite` carries two notions of finiteness, by listing
and in Dedekind's sense. `Countable` defines enumerability through partial
maps `Nat -> Option alpha`, which is what lets empty and finite types be
enumerable without special cases. `Pairing` writes down the diagonal walk of
`Nat × Nat`, and `Union`, `Sum` and `Arithmetic` all reduce to it -- countable
unions, sum types, and the enumerability of Lean's `Int` and `Rat`.
`CantorBernstein` constructs the bijection from two injections by the chain
argument, `Cantor` proves no type surjects onto its powerset, and `Continuum`
combines the two into the notion of continuum size.

Nothing in the subtree mentions an ordered field or a real number. That is
deliberate and is why the whole of it sits in `Foundation`: the results are
about types, and the two places they are used --
`Tautology.RealBootstrap.InternalCountable` for countability of the internal
rationals, and `RealCardinality` for uncountability and continuum size of the
carrier -- import this entry point and specialise.

## Role

Subtree entry. It declares nothing.
-/
