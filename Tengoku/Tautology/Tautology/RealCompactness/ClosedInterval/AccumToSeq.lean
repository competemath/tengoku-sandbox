import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean

/-!
# Edge: the accumulation form gives sequential Bolzano-Weierstrass

The converse edge, and it is not free: it carries an
`InvNatArchimedeanPrinciple` hypothesis. The reason is visible in one place
only -- thinning towards an accumulation point produces terms within radius
`1 / (k + 1)`, and those radii have to reach zero for the subsequence to
converge.

The argument splits on whether some value recurs at arbitrarily large indices.
If one does, its indices give a constant subsequence and no Archimedean input
is needed. If none does, the range is infinite and bounded, so the accumulation
principle applies to it; the delicate step is then forcing the principle to
return a *later* term, done by shrinking the radius below the target tolerance
while also dodging the finitely many values already used.

## Position and role

Edge module implementing `BWAccumulationToSequential`, exporting `target`. Its
machinery is reused wholesale by `Tautology.RealCompactness.LimitPointCompact`,
which needs the same thinning argument at subset level -- one of the few places
where a graph edge's internals serve a second consumer.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace AccumToSeq

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The graph edge proved by this file: the accumulation principle implies the
sequential one, modulo the inverse-natural Archimedean principle of
`Tautology.RealBootstrap.Archimedean`. The extra hypothesis is not decoration:
an accumulation point must be thinned out into an actual convergent
subsequence, the radii doing the thinning have to tend to zero, and that is
exactly what the hypothesis says. -/
def Target : Prop :=
  F.BWAccumulationToSequential

/-- The set of values taken by `u`. Restating a sequence as a set is what
lets the accumulation principle, a statement about sets, act on it. -/
def RangeSet (u : Nat -> alpha) : alpha -> Prop :=
  fun x => Exists (fun n : Nat => x = u n)

/-- The value `x` occurs in `u` at arbitrarily large indices. A frequent
value is already the limit of its own subsequence, which settles the easy
half of the case split below. -/
def ValueFrequent (u : Nat -> alpha) (x : alpha) : Prop :=
  forall N : Nat, Exists (fun n : Nat => And (N <= n) (u n = x))

theorem not_frequent_eventually_ne {u : Nat -> alpha} {x : alpha}
    (h : Not (ValueFrequent u x)) :
    Exists (fun N : Nat => forall n : Nat, N <= n -> Not (u n = x)) := by
  classical
  by_cases hex :
      Exists (fun N : Nat => forall n : Nat, N <= n -> Not (u n = x))
  · exact hex
  · have hfreq : ValueFrequent u x := by
      intro N
      by_cases hN : Exists (fun n : Nat => And (N <= n) (u n = x))
      · exact hN
      · have hbad :
            Exists (fun N0 : Nat => forall n : Nat, N0 <= n -> Not (u n = x)) := by
          refine Exists.intro N ?_
          intro n hn hnx
          exact hN (Exists.intro n (And.intro hn hnx))
        exact False.elim (hex hbad)
    exact False.elim (h hfreq)

theorem eventually_not_mem_list {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (ValueFrequent u x)) :
    forall xs : List alpha,
      Exists (fun N : Nat =>
        forall n : Nat, N <= n -> Not (List.Mem (u n) xs))
  | [] =>
      Exists.intro 0 (fun _ _ hmem => nomatch hmem)
  | x :: xs => by
      cases not_frequent_eventually_ne (u := u) (x := x) (hnone x) with
      | intro Nx hNx =>
          cases eventually_not_mem_list hnone xs with
          | intro Nxs hNxs =>
              refine Exists.intro (Nat.max Nx Nxs) ?_
              intro n hn hmem
              cases hmem with
              | head =>
                  exact hNx n (Nat.le_trans (Nat.le_max_left Nx Nxs) hn) rfl
              | tail _ htail =>
                  exact hNxs n (Nat.le_trans (Nat.le_max_right Nx Nxs) hn) htail

/-- When no value is frequent, the range cannot be exhausted by any list:
past the stage where every listed value has stopped occurring, the
sequence produces a point of the range that the list does not contain.
This is the bridge from sequence language to the list-infinity the
accumulation principle demands. -/
theorem range_listInfinite_of_no_frequent {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (ValueFrequent u x)) :
    Foundation.Cardinal.ListInfinite (RangeSet u) := by
  intro xs
  cases eventually_not_mem_list (u := u) hnone xs with
  | intro N hN =>
      refine Exists.intro (u N) ?_
      constructor
      · exact Exists.intro N rfl
      · exact hN N (Nat.le_refl N)

theorem range_bounded {u : Nat -> alpha}
    (hbdd : SeqBounded F u) :
    SetBounded F (RangeSet u) := by
  cases hbdd with
  | intro left hleft =>
      cases hleft with
      | intro right hbounds =>
          refine Exists.intro left ?_
          refine Exists.intro right ?_
          intro x hx
          cases hx with
          | intro n hn =>
              rw [hn]
              exact hbounds n

/-- An increasing run of occurrence indices of a frequent value, each
chosen by classical selection beyond the previous one. The subsequence it
cuts out of `u` is constant at `x`. -/
noncomputable def frequentIndex {u : Nat -> alpha} {x : alpha}
    (hfreq : ValueFrequent u x) : Nat -> Nat
  | 0 => Classical.choose (hfreq 0)
  | k + 1 => Classical.choose (hfreq (frequentIndex hfreq k + 1))

theorem frequentIndex_value {u : Nat -> alpha} {x : alpha}
    (hfreq : ValueFrequent u x)
    (k : Nat) :
    u (frequentIndex hfreq k) = x := by
  cases k with
  | zero =>
      exact (Classical.choose_spec (hfreq 0)).right
  | succ k =>
      exact
        (Classical.choose_spec
          (hfreq (frequentIndex hfreq k + 1))).right

theorem frequentIndex_step {u : Nat -> alpha} {x : alpha}
    (hfreq : ValueFrequent u x)
    (k : Nat) :
    frequentIndex hfreq k < frequentIndex hfreq (k + 1) := by
  have hle :
      frequentIndex hfreq k + 1 <= frequentIndex hfreq (k + 1) :=
    (Classical.choose_spec
      (hfreq (frequentIndex hfreq k + 1))).left
  omega

theorem frequentIndex_subsequence {u : Nat -> alpha} {x : alpha}
    (hfreq : ValueFrequent u x) :
    SubsequenceIndex (frequentIndex hfreq) :=
  frequentIndex_step hfreq

/-- A frequent value is the limit of the subsequence cut out by its
occurrence indices -- that subsequence is literally constant at `x`, so
this branch of the argument needs no Archimedean input at all. -/
theorem frequent_subsequence_tendsto {u : Nat -> alpha} {x : alpha}
    (hfreq : ValueFrequent u x) :
    SeqTendsto F (subsequence u (frequentIndex hfreq)) x := by
  intro eps heps
  refine Exists.intro 0 ?_
  intro n _hn
  have hval : u (frequentIndex hfreq n) = x :=
    frequentIndex_value hfreq n
  dsimp [subsequence]
  rw [hval]
  rw [abs_sub_self F x]
  exact heps

theorem dist_pos_of_ne {x y : alpha}
    (hxy : Not (x = y)) :
    F.lt F.zero (dist F x y) :=
  Tautology.IsOrderedFieldBaseLike.dist_pos_of_ne F hxy
/-- Below any positive `eps` there is a positive radius that excludes every
listed point other than `l` from the ball around `l`: finitely many
positive distances have a positive lower bound, and the construction
descends under `eps` by repeated halving. -/
theorem exists_radius_avoids_list
    (l eps : alpha)
    (heps : F.lt F.zero eps) :
    forall xs : List alpha,
      Exists
        (fun delta : alpha =>
          And (F.lt F.zero delta)
            (And (F.lt delta eps)
              (forall z : alpha,
                List.Mem z xs ->
                  Not (z = l) -> F.lt delta (dist F z l))))
  | [] =>
      Exists.intro (half F eps)
        (And.intro (half_pos F heps)
          (And.intro (half_lt_self F heps)
            (fun _ hmem _ => nomatch hmem)))
  | z :: zs => by
      cases exists_radius_avoids_list l (half F eps) (half_pos F heps) zs with
      | intro tail htail =>
          by_cases hzl : z = l
          · refine Exists.intro tail ?_
            constructor
            · exact htail.left
            constructor
            · exact lt_trans F htail.right.left (half_lt_self F heps)
            · intro y hy hyne
              cases hy with
              | head =>
                  exact False.elim (hyne hzl)
              | tail _ hyTail =>
                  exact htail.right.right y hyTail hyne
          · let dz := dist F z l
            have hdz : F.lt F.zero dz :=
              dist_pos_of_ne F hzl
            by_cases htail_le_dz : F.le tail dz
            · let delta := half F tail
              refine Exists.intro delta ?_
              constructor
              · exact half_pos F htail.left
              constructor
              · exact lt_trans F (half_lt_self F htail.left)
                  (lt_trans F htail.right.left (half_lt_self F heps))
              · intro y hy hyne
                cases hy with
                | head =>
                    exact lt_of_lt_of_le F
                      (half_lt_self F htail.left) htail_le_dz
                | tail _ hyTail =>
                    exact lt_trans F (half_lt_self F htail.left)
                      (htail.right.right y hyTail hyne)
            · have hdz_le_tail : F.le dz tail := by
                cases F.le_total dz tail with
                | inl h => exact h
                | inr h => exact False.elim (htail_le_dz h)
              let delta := half F dz
              refine Exists.intro delta ?_
              constructor
              · exact half_pos F hdz
              constructor
              · exact lt_trans F
                  (lt_of_lt_of_le F (half_lt_self F hdz) hdz_le_tail)
                  (lt_trans F htail.right.left (half_lt_self F heps))
              · intro y hy hyne
                cases hy with
                | head =>
                    exact half_lt_self F hdz
                | tail _ hyTail =>
                    exact lt_trans F
                      (lt_of_lt_of_le F (half_lt_self F hdz) hdz_le_tail)
                      (htail.right.right y hyTail hyne)

/-- The values `u` has taken up to stage `n`, most recent first: the finite
blacklist that the radius chosen in `exists_later_close_of_accumulation`
has to dodge. -/
def ValuesUpTo (u : Nat -> alpha) : Nat -> List alpha
  | 0 => [u 0]
  | n + 1 => u (n + 1) :: ValuesUpTo u n

theorem mem_valuesUpTo_of_le
    (u : Nat -> alpha)
    {m n : Nat}
    (hmn : m <= n) :
    List.Mem (u m) (ValuesUpTo u n) := by
  induction n generalizing m with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      exact List.Mem.head []
  | succ n ih =>
      by_cases hm_succ : m = n + 1
      · subst hm_succ
        exact List.Mem.head _
      · have hm_le_n : m <= n := by omega
        exact List.Mem.tail _ (ih hm_le_n)

/-- An accumulation point of the range is approached by values with
arbitrarily large indices. Shrinking the radius to dodge the finitely many
values seen so far forces the point returned by the accumulation principle
to be a genuinely later term, which is what converts an accumulation point
into a subsequence. -/
theorem exists_later_close_of_accumulation
    {u : Nat -> alpha} {l radius : alpha}
    (hacc : AccumulationPoint F (RangeSet u) l)
    (hradius : F.lt F.zero radius)
    (prev : Nat) :
    Exists
      (fun n : Nat =>
        And (prev < n) (F.lt (dist F (u n) l) radius)) := by
  cases exists_radius_avoids_list F l radius hradius
      (ValuesUpTo u prev) with
  | intro delta hdelta =>
      cases hacc delta hdelta.left with
      | intro y hy =>
          cases hy.left with
          | intro n hn =>
              refine Exists.intro n ?_
              have hy_ne_l : Not (y = l) := hy.right.left
              have hclose_y : F.lt (dist F y l) delta := hy.right.right
              have hn_gt : prev < n := by
                by_cases hle : n <= prev
                · have hmem_un : List.Mem (u n) (ValuesUpTo u prev) :=
                    mem_valuesUpTo_of_le u hle
                  have hmem_y : List.Mem y (ValuesUpTo u prev) := by
                    rw [hn]
                    exact hmem_un
                  have hdelta_lt :
                      F.lt delta (dist F y l) :=
                    hdelta.right.right y hmem_y hy_ne_l
                  exact False.elim
                    (lt_irrefl F delta (lt_trans F hdelta_lt hclose_y))
                · omega
              constructor
              · exact hn_gt
              · rw [<- hn]
                exact lt_trans F hclose_y hdelta.right.left

/-- The radius attached to stage `k`: the inverse of `k + 1`. These radii
shrink as the extraction proceeds, and driving them below every positive
quantity is precisely the Archimedean hypothesis this edge carries. -/
def invSuccRadius (n : Nat) : alpha :=
  F.inv (nat F (n + 1))

theorem invSuccRadius_pos (n : Nat) :
    F.lt F.zero (invSuccRadius F n) := by
  unfold invSuccRadius
  exact inv_pos F (nat_succ_pos F n)

theorem nat_le_nat_succ (n : Nat) :
    F.le (nat F n) (nat F (n + 1)) :=
  Tautology.IsOrderedFieldBaseLike.nat_le_nat_succ F n

theorem nat_le_nat_of_le {m n : Nat}
    (hmn : m <= n) :
    F.le (nat F m) (nat F n) := by
  induction hmn with
  | refl =>
      exact F.le_refl (nat F m)
  | step h ih =>
      exact F.le_trans ih (nat_le_nat_succ F _)

theorem inv_le_inv_of_le_pos {a b : alpha}
    (ha : F.lt F.zero a)
    (hb : F.lt F.zero b)
    (hab : F.le a b) :
    F.le (F.inv b) (F.inv a) :=
  Tautology.IsOrderedFieldBaseLike.inv_le_inv_of_le_pos F ha hb hab
theorem invSuccRadius_antitone {N n : Nat}
    (hNn : N <= n) :
    F.le (invSuccRadius F n) (invSuccRadius F N) := by
  unfold invSuccRadius
  apply inv_le_inv_of_le_pos F
  · exact nat_succ_pos F N
  · exact nat_succ_pos F n
  · exact nat_le_nat_of_le F (by omega : N + 1 <= n + 1)

/-- The extraction itself: stage `k + 1` chooses an index beyond stage `k`
whose value lands inside the `k`-th radius around the accumulation
point. -/
noncomputable def closeIndex {u : Nat -> alpha} {l : alpha}
    (hacc : AccumulationPoint F (RangeSet u) l) : Nat -> Nat
  | 0 =>
      Classical.choose
        (exists_later_close_of_accumulation F hacc
          (invSuccRadius_pos F 0) 0)
  | k + 1 =>
      Classical.choose
        (exists_later_close_of_accumulation F hacc
          (invSuccRadius_pos F (k + 1)) (closeIndex hacc k))

theorem closeIndex_step {u : Nat -> alpha} {l : alpha}
    (hacc : AccumulationPoint F (RangeSet u) l)
    (k : Nat) :
    closeIndex F hacc k < closeIndex F hacc (k + 1) := by
  exact
    (Classical.choose_spec
      (exists_later_close_of_accumulation F hacc
        (invSuccRadius_pos F (k + 1)) (closeIndex F hacc k))).left

theorem closeIndex_subsequence {u : Nat -> alpha} {l : alpha}
    (hacc : AccumulationPoint F (RangeSet u) l) :
    SubsequenceIndex (closeIndex F hacc) :=
  closeIndex_step F hacc

theorem closeIndex_close {u : Nat -> alpha} {l : alpha}
    (hacc : AccumulationPoint F (RangeSet u) l)
    (k : Nat) :
    F.lt (dist F (u (closeIndex F hacc k)) l)
      (invSuccRadius F k) := by
  cases k with
  | zero =>
      exact
        (Classical.choose_spec
          (exists_later_close_of_accumulation F hacc
            (invSuccRadius_pos F 0) 0)).right
  | succ k =>
      exact
        (Classical.choose_spec
          (exists_later_close_of_accumulation F hacc
            (invSuccRadius_pos F (k + 1)) (closeIndex F hacc k))).right

/-- The extracted subsequence converges to the accumulation point. This is
where `InvNatArchimedeanPrinciple` enters, through `small_inv_succ`: the
radii -- inverses of `k + 1` -- eventually sit below the given `eps`, and
each term was chosen inside its own radius. -/
theorem closeSubsequence_tendsto
    (hinvNat : F.InvNatArchimedeanPrinciple)
    {u : Nat -> alpha} {l : alpha}
    (hacc : AccumulationPoint F (RangeSet u) l) :
    SeqTendsto F (subsequence u (closeIndex F hacc)) l := by
  intro eps heps
  cases hinvNat.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hclose :
          F.lt (dist F (u (closeIndex F hacc n)) l)
            (invSuccRadius F n) :=
        closeIndex_close F hacc n
      have hradius_le :
          F.le (invSuccRadius F n) (invSuccRadius F N) :=
        invSuccRadius_antitone F hn
      have hlt_eps :
          F.lt (invSuccRadius F n) eps :=
        lt_of_le_of_lt F hradius_le hN
      dsimp [subsequence, dist]
      exact lt_trans F hclose hlt_eps

/-- The hard branch of the case split: when no value is frequent, the range
is infinite and bounded, the accumulation principle yields an accumulation
point of it, and the close indices turn that point into a convergent
subsequence of `u` itself. -/
theorem sequential_from_infinite_range
    (hinvNat : F.InvNatArchimedeanPrinciple)
    (haccum : F.BolzanoWeierstrassAccumulationPrinciple)
    {u : Nat -> alpha}
    (hbdd : SeqBounded F u)
    (hnone : forall x : alpha, Not (ValueFrequent u x)) :
    Exists (fun l : alpha => HasConvergentSubsequence F u l) := by
  have hrangeInf : Foundation.Cardinal.ListInfinite (RangeSet u) :=
    range_listInfinite_of_no_frequent hnone
  have hrangeBdd : SetBounded F (RangeSet u) :=
    range_bounded F hbdd
  cases haccum.accumulation_point (RangeSet u) hrangeBdd hrangeInf with
  | intro l hacc =>
      refine Exists.intro l ?_
      refine Exists.intro (closeIndex F hacc) ?_
      constructor
      · exact closeIndex_subsequence F hacc
      · exact closeSubsequence_tendsto F hinvNat hacc

/-- The edge as a principle. The argument splits on whether some value
occurs at arbitrarily large indices: a frequent value is trivially a
subsequential limit, and when there is none the range is infinite and the
accumulation principle takes over. -/
theorem sequentialPrinciple
    (hinvNat : F.InvNatArchimedeanPrinciple)
    (haccum : F.BolzanoWeierstrassAccumulationPrinciple) :
    F.BolzanoWeierstrassSequentialPrinciple where
  convergent_subsequence := by
    intro u hbdd
    classical
    by_cases hfreq :
        Exists (fun x : alpha => ValueFrequent u x)
    · cases hfreq with
      | intro x hx =>
          refine Exists.intro x ?_
          refine Exists.intro (frequentIndex hx) ?_
          constructor
          · exact frequentIndex_subsequence hx
          · exact frequent_subsequence_tendsto F hx
    · have hnone : forall x : alpha, Not (ValueFrequent u x) := by
        intro x hx
        exact hfreq (Exists.intro x hx)
      exact sequential_from_infinite_range F hinvNat haccum hbdd hnone

/-- The exported edge `BWAccumulationToSequential`, inverse-natural
Archimedean hypothesis included in the statement;
`BolzanoWeierstrass.accumulation_to_seq` forwards to it. -/
theorem target : Target F := by
  intro hinvNat hacc
  exact sequentialPrinciple F hinvNat hacc

end AccumToSeq
end Compactness
end IsOrderedFieldBaseLike
end Tautology
