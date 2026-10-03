import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements

/-!
# Edge: sequential Bolzano-Weierstrass gives the accumulation form

The only edge of the graph that costs nothing. Neither completeness nor an
Archimedean principle appears; the ordered-field structure suffices.

Given a bounded infinite set, the argument manufactures a repetition-free
enumeration of it -- at each stage a point outside the finite list built so
far, which infinitude guarantees -- and hands that sequence to the sequential
principle. Its limit is an accumulation point because within any radius the
convergent subsequence supplies two distinct terms, so at least one differs
from the limit. Distinctness is built into the construction rather than
extracted afterwards, which is what keeps the edge free of hypotheses.

## Position and role

Edge module of `RealCompactness/ClosedInterval/`, implementing
`BWSequentialToAccumulation` and exporting a single `target`. Consumed by
`Tautology.RealCompactness.ClosedInterval.BolzanoWeierstrass` and by
`Tautology.RealCompactness.ClosedInterval.Routes`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace SeqToAccum

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The graph edge proved by this file: the Bolzano-Weierstrass sequential
principle implies the accumulation principle. It is the only edge of the
closed-interval graph stated with no hypothesis beyond the ordered field:
the distinct points the argument needs are manufactured by the fresh-point
construction below rather than squeezed out of a limit, so nothing has to
be driven to zero. -/
def Target : Prop :=
  F.BWSequentialToAccumulation

/-- A point of `S` outside the list `xs`, read off the list-infinity of `S`
by choice. This is the step that turns "no list exhausts `S`" into a supply
of genuinely new points, one per query. -/
noncomputable def freshFromList
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    (xs : List alpha) : alpha :=
  Classical.choose (hinf xs)

theorem freshFromList_mem
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    (xs : List alpha) :
    S (freshFromList S hinf xs) :=
  (Classical.choose_spec (hinf xs)).left

theorem freshFromList_not_mem
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    (xs : List alpha) :
    Not (List.Mem (freshFromList S hinf xs) xs) :=
  (Classical.choose_spec (hinf xs)).right

/-- The points chosen up to stage `n`, most recent first. Membership in this
list is what "already used" means for the construction of `freshSeq`. -/
noncomputable def freshList
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S) :
    Nat -> List alpha
  | 0 => []
  | n + 1 =>
      freshFromList S hinf (freshList S hinf n) ::
        freshList S hinf n

/-- An enumeration of points of `S` that never repeats: the `n`-th term is
the fresh point chosen against the first `n` choices. When `S` is bounded
this is a bounded sequence, which is the shape the sequential principle
consumes. -/
noncomputable def freshSeq
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S) :
    Nat -> alpha :=
  fun n : Nat => freshFromList S hinf (freshList S hinf n)

theorem freshList_succ
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    (n : Nat) :
    freshList S hinf (n + 1) =
      freshSeq S hinf n :: freshList S hinf n :=
  rfl

theorem freshSeq_mem
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    (n : Nat) :
    S (freshSeq S hinf n) :=
  freshFromList_mem S hinf (freshList S hinf n)

theorem freshSeq_not_mem_freshList
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    (n : Nat) :
    Not (List.Mem (freshSeq S hinf n) (freshList S hinf n)) :=
  freshFromList_not_mem S hinf (freshList S hinf n)

theorem freshSeq_mem_freshList_of_lt
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    {m n : Nat}
    (hmn : m < n) :
    List.Mem (freshSeq S hinf m) (freshList S hinf n) := by
  induction n generalizing m with
  | zero =>
      have hbad : False := by omega
      exact False.elim hbad
  | succ n ih =>
      by_cases hmn_eq : m = n
      · subst hmn_eq
        rw [freshList_succ]
        exact List.Mem.head _
      · have hm_lt_n : m < n := by omega
        rw [freshList_succ]
        exact List.Mem.tail _ (ih hm_lt_n)

/-- The fresh sequence never repeats itself: a later term was chosen outside
the list that already holds every earlier term. This constructed
distinctness is what keeps the edge `Target` free of any Archimedean
hypothesis. -/
theorem freshSeq_ne_of_lt
    (S : alpha -> Prop)
    (hinf : Foundation.Cardinal.ListInfinite S)
    {m n : Nat}
    (hmn : m < n) :
    Not (freshSeq S hinf n = freshSeq S hinf m) := by
  intro h
  have hmem :
      List.Mem (freshSeq S hinf m) (freshList S hinf n) :=
    freshSeq_mem_freshList_of_lt S hinf hmn
  rw [<- h] at hmem
  exact (freshSeq_not_mem_freshList S hinf n) hmem

theorem freshSeq_bounded
    {S : alpha -> Prop}
    (hinf : Foundation.Cardinal.ListInfinite S)
    (hbdd : SetBounded F S) :
    SeqBounded F (freshSeq S hinf) := by
  cases hbdd with
  | intro left hleft =>
      cases hleft with
      | intro right hbounds =>
          refine Exists.intro left ?_
          refine Exists.intro right ?_
          intro n
          exact hbounds (freshSeq S hinf n) (freshSeq_mem S hinf n)

/-- The limit of a convergent subsequence of the fresh sequence is an
accumulation point of `S`: within any radius the subsequence offers a term
of `S` different from the limit, since among two of its terms close to the
limit at least one differs from it. -/
theorem limit_of_fresh_subsequence_is_accumulation
    {S : alpha -> Prop}
    (hinf : Foundation.Cardinal.ListInfinite S)
    {l : alpha}
    {phi : Nat -> Nat}
    (hphi : SubsequenceIndex phi)
    (hlim : SeqTendsto F (subsequence (freshSeq S hinf) phi) l) :
    AccumulationPoint F S l := by
  intro eps heps
  cases hlim eps heps with
  | intro N hN =>
      let u : Nat -> alpha := freshSeq S hinf
      let y0 := u (phi N)
      let y1 := u (phi (N + 1))
      have hy0S : S y0 := by
        exact freshSeq_mem S hinf (phi N)
      have hy1S : S y1 := by
        exact freshSeq_mem S hinf (phi (N + 1))
      have hclose0 : F.lt (dist F y0 l) eps := by
        have h := hN N (Nat.le_refl N)
        simpa [dist, subsequence, u, y0] using h
      have hclose1 : F.lt (dist F y1 l) eps := by
        have h := hN (N + 1) (Nat.le_succ N)
        simpa [dist, subsequence, u, y1] using h
      have hdistinct : Not (y1 = y0) := by
        dsimp [y1, y0, u]
        exact freshSeq_ne_of_lt S hinf (hphi N)
      by_cases hy0 : y0 = l
      · refine Exists.intro y1 ?_
        constructor
        · exact hy1S
        constructor
        · intro hy1
          have hy10 : y1 = y0 := by
            rw [hy1, hy0]
          exact hdistinct hy10
        · exact hclose1
      · refine Exists.intro y0 ?_
        constructor
        · exact hy0S
        constructor
        · exact hy0
        · exact hclose0

/-- The edge as a principle: bounded infinite sets acquire accumulation
points, given that bounded sequences acquire convergent subsequences. The
fresh sequence enumerates the set without repetition, and the limit of any
convergent subsequence of it accumulates. -/
theorem accumulationPrinciple
    (hseq : F.BolzanoWeierstrassSequentialPrinciple) :
    F.BolzanoWeierstrassAccumulationPrinciple where
  accumulation_point := by
    intro S hbdd hinf
    let u : Nat -> alpha := freshSeq S hinf
    have hu_bdd : SeqBounded F u := by
      simpa [u] using freshSeq_bounded F hinf hbdd
    cases hseq.convergent_subsequence u hu_bdd with
    | intro l hl =>
        cases hl with
        | intro phi hphi_lim =>
            exact Exists.intro l
              (limit_of_fresh_subsequence_is_accumulation F hinf
                hphi_lim.left hphi_lim.right)

/-- The exported edge `BWSequentialToAccumulation`: sequential
Bolzano-Weierstrass implies the accumulation form, over an arbitrary
ordered field and with no extra hypothesis. -/
theorem target : Target F := by
  intro hseq
  exact accumulationPrinciple F hseq

end SeqToAccum
end Compactness
end IsOrderedFieldBaseLike
end Tautology
