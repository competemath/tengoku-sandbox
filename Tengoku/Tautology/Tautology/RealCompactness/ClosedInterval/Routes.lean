import Tengoku.Tautology.Tautology.RealTopology.Lindelof
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.BolzanoWeierstrass
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FromNestedSequential
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FromSupSequential
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FromNestedFinite
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FromSupFinite
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FiniteToLebesgue
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.SeqToFinite
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FiniteToSeq

/-!
# Assembling the graph

Where the edges become routes. Two entry points times two families give the
four assemblies exported here: enter from the nested-interval principle or from
the supremum property, and start on the sequence side or the cover side. Each
produces a full `CompactnessPrinciples` bundle.

The file splits by what it needs. The ordered-field half assembles from
hypotheses handed in, so it stays generic; the Dedekind half restates Lindelöf
from `Tautology.RealTopology.Lindelof` and feeds the supremum entry, and that
is the point where completeness enters the assembly.

`lowerCompactnessUniverse` is bookkeeping, not mathematics. Edges that consume
covers state their conclusion at the raised universe, while a package promises
the caller's own universe; lowering means lifting an arbitrary cover, applying
the raised principle and stripping the lift off the finite list that comes
back. It appears here and again, as a twin, in
`Tautology.RealCompactness.ClosedInterval.Selected`, which does not import
this module.

## Position and role

Assembly module. It is the generic counterpart of
`Tautology.RealCompactness.ClosedInterval.Selected`: this file shows every
route that could be taken, that one takes a single path at the selected
carrier. Nothing in the library consumes these declarations directly -- they
exist to make the graph statable and checkable, which is the whole intent of
the arrangement.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace Routes

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Lowers a list of lifted indices back to plain ones; the list-level half
of the universe demotion that `lowerCompactnessUniverse` performs. -/
def downList {iota : Type u} :
    List (ULift.{max u 1, u} iota) -> List iota
  | [] => []
  | x :: xs => x.down :: downList xs

theorem mem_downList_of_mem {iota : Type u}
    {x : ULift.{max u 1, u} iota} :
    forall {xs : List (ULift.{max u 1, u} iota)},
      List.Mem x xs -> List.Mem x.down (downList xs)
  | [], h => nomatch h
  | y :: ys, h => by
      cases h with
      | head =>
          exact List.Mem.head _
      | tail _ htail =>
          exact List.Mem.tail _ (mem_downList_of_mem htail)

/-- The universe demotion tool of the region: compactness at index universe
`max u 1` implies compactness at `u`. This is bookkeeping, not mathematics
-- the cover is lifted, the finite subcover is extracted up there, and the
selected indices are lowered through `downList`. The graph needs it
because the hypothesis-carrying edges are stated at `max u 1` while the
assembled packages promise the principle at the caller's own universe. -/
def lowerCompactnessUniverse
    (hcompact :
      ClosedIntervalCompactnessPrinciple.{max u 1} F) :
    ClosedIntervalCompactnessPrinciple.{u} F where
  finite_subcover := by
    intro iota left right U hle hopen hcover
    let V : ULift.{max u 1, u} iota -> alpha -> Prop :=
      fun j => U j.down
    have hopenLift :
        forall j : ULift.{max u 1, u} iota, F.IsOpen (V j) := by
      intro j
      exact hopen j.down
    have hcoverLift :
        Covers.{max u 1} V (F.ClosedInterval left right) := by
      intro x hx
      cases hcover x hx with
      | intro i hi =>
          exact Exists.intro (ULift.up i) hi
    cases hcompact.finite_subcover left right V hle hopenLift hcoverLift with
    | intro js hjs =>
        refine Exists.intro (downList js) ?_
        intro x hx
        cases hjs x hx with
        | intro j hj =>
            refine Exists.intro j.down ?_
            exact And.intro (mem_downList_of_mem hj.left) hj.right

/-- The two bridge edges bundled into `BWCompactnessBridge`:
Bolzano-Weierstrass to compactness under Lindelof, and back under the
inverse-natural Archimedean principle and the lifted universe. Pure
assembly -- both directions forward to their files' `target`s. -/
def pureBridge :
    BWCompactnessBridge.{u} F where
  bw_to_compact :=
    SeqToFinite.target F
  compact_to_bw :=
    FiniteToSeq.target F

/-- The full `CompactnessPrinciples` package assembled from a sequential
entry: the Lindelof-carrying bridge produces compactness at `max u 1`, the
Lebesgue edge consumes it right there, and the demotion tool lowers it to
`u` for the package's own compactness slot. -/
noncomputable def packageFromSequential
    (hlind :
      LindelofPrinciple.{max u 1} F)
    (hseq : BolzanoWeierstrassSequentialPrinciple F) :
    CompactnessPrinciples.{u} F := by
  let hcompactMax :
      ClosedIntervalCompactnessPrinciple.{max u 1} F :=
    SeqToFinite.target F hlind hseq
  let hcompact :
      ClosedIntervalCompactnessPrinciple.{u} F :=
    lowerCompactnessUniverse F hcompactMax
  let hlebesgue :
      ClosedIntervalLebesguePrinciple.{u} F :=
    FiniteToLebesgue.target F hcompactMax
  exact {
    bolzano_weierstrass := {
      sequential := hseq
      accumulation := SeqToAccum.target F hseq
    }
    compactness := {
      finite_subcover := hcompact
      lebesgue_number := hlebesgue
    }
    bridge := pureBridge F
  }

/-- The mirrored assembly from a compactness entry at the lifted universe:
the reverse bridge recovers sequential Bolzano-Weierstrass, and the same
demotion and Lebesgue edge fill in the rest of the package. -/
noncomputable def packageFromFinite
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hcompactMax :
      ClosedIntervalCompactnessPrinciple.{max u 1} F) :
    CompactnessPrinciples.{u} F := by
  let hseq : BolzanoWeierstrassSequentialPrinciple F :=
    FiniteToSeq.target F hinvNat hcompactMax
  let hcompact :
      ClosedIntervalCompactnessPrinciple.{u} F :=
    lowerCompactnessUniverse F hcompactMax
  let hlebesgue :
      ClosedIntervalLebesguePrinciple.{u} F :=
    FiniteToLebesgue.target F hcompactMax
  exact {
    bolzano_weierstrass := {
      sequential := hseq
      accumulation := SeqToAccum.target F hseq
    }
    compactness := {
      finite_subcover := hcompact
      lebesgue_number := hlebesgue
    }
    bridge := pureBridge F
  }

end Routes
end Compactness
end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike
namespace Compactness
namespace Routes

universe u

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The ordered-field view of the complete field `C`, connecting the
Dedekind-complete statements of the entry points to the ordered-field
statements the graph is built on. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The Lindelof input of the supremum routes, restated from
`Tautology.RealTopology.Lindelof` in the shape the sequential-to-finite edge
consumes. This restatement is where Dedekind completeness enters the
assembly below. -/
noncomputable def lindelofPrinciple :
    IsOrderedFieldBaseLike.LindelofPrinciple.{u} (F C) where
  countable_subcover := by
    intro iota S U hopen hcover
    exact IsDedekindCompleteOrderedFieldBaseLike.lindelof
      C hopen hcover

/-- The supremum route, entered sequentially: completeness gives the
sequential principle through `FromSupSequential.target`, and the Lindelof
principle above carries it across the bridge to the full package. -/
noncomputable def fromSupSequential :
    IsOrderedFieldBaseLike.CompactnessPrinciples.{u} (F C) :=
  IsOrderedFieldBaseLike.Compactness.Routes.packageFromSequential
    (F C)
    (lindelofPrinciple C)
    (FromSupSequential.target C)

/-- The supremum route entered at the finite end: `FromSupFinite.target` gives
compactness of the complete field at the lifted universe, and the
inverse-natural Archimedean principle of `Tautology.RealBootstrap.Archimedean`
carries it back to Bolzano-Weierstrass. -/
noncomputable def fromSupFinite :
    IsOrderedFieldBaseLike.CompactnessPrinciples.{u} (F C) :=
  IsOrderedFieldBaseLike.Compactness.Routes.packageFromFinite
    (F C)
    (invNatArchimedean C)
    (FromSupFinite.target.{max u 1} C)

end Routes
end Compactness
end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
