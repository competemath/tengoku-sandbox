import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean
import Tengoku.Tautology.Tautology.RealBootstrap.StrictOrder
import Tengoku.Tautology.Tautology.RealBootstrap.Supremum
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Order

/-!
# Entry: the supremum property gives sequential Bolzano-Weierstrass

One of the two ways into the graph, this one straight from Dedekind
completeness. It lives in the complete-field namespace and takes no principle
as a hypothesis.

Call a right endpoint `c` a good cut when `[left, c]` catches only finitely
many terms of the sequence. Good cuts are nonempty and bounded above by the
right end, so they have a supremum, and that supremum is a cluster point of the
sequence. Thinning towards it with radii `1 / (n + 1)` produces a convergent
subsequence.

Completeness is spent exactly once, on the supremum of the good cuts. The
Archimedean fact used in the thinning step is not a hypothesis here -- it is
read off the complete-field bundle, which is what distinguishes this entry from
the nested-interval one. Finiteness is expressed with the list vocabulary of
`Tautology.Foundation.Cardinal` rather than by counting.

## Position and role

Entry module, exporting `Target`. Assembled by
`Tautology.RealCompactness.ClosedInterval.Routes` into the `fromSupSequential`
route, which the selected route does not take -- `Selected` enters through
`Tautology.RealCompactness.ClosedInterval.FromNestedSequential` instead.
This module is proved and available, not travelled.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike
namespace Compactness
namespace FromSupSequential

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The ordered field carried by the completeness bundle. Everything below
is ordered-field reasoning except one appeal to the bundle itself, the
`exists_lub` field inside `cluster_of_bounded_sequence`, and one appeal to
the Archimedean theorem that completeness proves, `invNatArchimedean` of
`Tautology.RealBootstrap.Archimedean`, inside `sequentialPrinciple`. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The promise of this entry point, in the naming convention every edge
and entry file of the region follows: the field underlying a
Dedekind-complete bundle satisfies the sequential Bolzano-Weierstrass
node. -/
def Target : Prop :=
  (F C).BolzanoWeierstrassSequentialPrinciple

/-- `l` is a cluster point of `u`: for every positive radius, however late a
stage is demanded, some term at or beyond it lies within that radius of
`l`. Weaker than convergence, since the witnessing term may change with the
radius; it is what the supremum argument naturally produces, and the
Archimedean principle upgrades it to a convergent subsequence below. -/
def SeqClusterAt (u : Nat -> alpha) (l : alpha) : Prop :=
  forall eps : alpha,
    (F C).lt (F C).zero eps ->
      forall N : Nat,
        Exists
          (fun n : Nat =>
            And (N <= n) ((F C).lt (IsOrderedFieldBaseLike.dist (F C) (u n) l) eps))

/-- The value `x` occurs at arbitrarily late positions of `u`. This is the
degenerate way to cluster at `x`, and it is how the argument disposes of a
bounded sequence with a degenerate window: there every term is forced to
equal the window's one point. -/
def ValueFrequent (u : Nat -> alpha) (x : alpha) : Prop :=
  forall N : Nat, Exists (fun n : Nat => And (N <= n) (u n = x))

/-- A frequently occurring value is a cluster point for free: the chosen
term sits at distance zero from `x`, so any radius at all serves. -/
theorem seqClusterAt_of_valueFrequent {u : Nat -> alpha} {x : alpha}
    (hfreq : ValueFrequent u x) :
    SeqClusterAt C u x := by
  intro eps heps N
  cases hfreq N with
  | intro n hn =>
      refine Exists.intro n ?_
      constructor
      · exact hn.left
      · dsimp [IsOrderedFieldBaseLike.dist]
        rw [hn.right, IsOrderedFieldBaseLike.abs_sub_self (F C) x]
        exact heps

/-- The radius schedule of the extraction: `1 / (n + 1)` at stage `n`,
positive and antitone in `n`, and eventually below any positive bound
exactly when the inverse-natural Archimedean principle holds. The successor
offset keeps stage zero at radius one. -/
def invSuccRadius (n : Nat) : alpha :=
  (F C).inv (IsOrderedFieldBaseLike.nat (F C) (n + 1))

theorem invSuccRadius_pos (n : Nat) :
    (F C).lt (F C).zero (invSuccRadius C n) := by
  unfold invSuccRadius
  exact IsOrderedFieldBaseLike.inv_pos (F C)
    (IsOrderedFieldBaseLike.nat_succ_pos (F C) n)

theorem nat_le_nat_succ (n : Nat) :
    (F C).le
      (IsOrderedFieldBaseLike.nat (F C) n)
      (IsOrderedFieldBaseLike.nat (F C) (n + 1)) := by
  have hpos : (F C).le (F C).zero (F C).one :=
    IsOrderedFieldBaseLike.zero_le_one (F C)
  have h := (F C).add_le_add_right hpos
    (IsOrderedFieldBaseLike.nat (F C) n)
  rwa [
    (F C).zero_add,
    (F C).add_comm (F C).one (IsOrderedFieldBaseLike.nat (F C) n),
    <- IsOrderedFieldBaseLike.nat_succ (F C) n
  ] at h

theorem nat_le_nat_of_le {m n : Nat}
    (hmn : m <= n) :
    (F C).le
      (IsOrderedFieldBaseLike.nat (F C) m)
      (IsOrderedFieldBaseLike.nat (F C) n) := by
  induction hmn with
  | refl =>
      exact (F C).le_refl (IsOrderedFieldBaseLike.nat (F C) m)
  | step h ih =>
      exact (F C).le_trans ih (nat_le_nat_succ C _)

theorem inv_le_inv_of_le_pos {a b : alpha}
    (ha : (F C).lt (F C).zero a)
    (hb : (F C).lt (F C).zero b)
    (hab : (F C).le a b) :
    (F C).le ((F C).inv b) ((F C).inv a) := by
  by_cases hle : (F C).le ((F C).inv b) ((F C).inv a)
  · exact hle
  · have hlt : (F C).lt ((F C).inv a) ((F C).inv b) := by
      cases (F C).le_total ((F C).inv a) ((F C).inv b) with
      | inl h => exact IsOrderedFieldBaseLike.lt_of_le_of_not_le (F C) h hle
      | inr h => exact False.elim (hle h)
    have ha_ne : Not (a = (F C).zero) :=
      IsOrderedFieldBaseLike.pos_ne_zero (F C) ha
    have hb_ne : Not (b = (F C).zero) :=
      IsOrderedFieldBaseLike.pos_ne_zero (F C) hb
    have hinvb_pos : (F C).lt (F C).zero ((F C).inv b) :=
      IsOrderedFieldBaseLike.inv_pos (F C) hb
    have hmul_lt :
        (F C).lt
          ((F C).mul a ((F C).inv a))
          ((F C).mul a ((F C).inv b)) :=
      IsOrderedFieldBaseLike.mul_lt_mul_pos_left (F C) hlt ha
    have hmul_le :
        (F C).le
          ((F C).mul a ((F C).inv b))
          ((F C).mul b ((F C).inv b)) :=
      IsOrderedFieldBaseLike.mul_le_mul_nonneg_right (F C) hab
        (IsOrderedFieldBaseLike.le_of_lt (F C) hinvb_pos)
    have hone_lt :
        (F C).lt (F C).one ((F C).mul a ((F C).inv b)) := by
      rwa [(F C).mul_inv_cancel ha_ne] at hmul_lt
    have hle_one :
        (F C).le ((F C).mul a ((F C).inv b)) (F C).one := by
      rwa [(F C).mul_inv_cancel hb_ne] at hmul_le
    exact False.elim
      ((IsOrderedFieldBaseLike.not_le_of_lt (F C) hone_lt) hle_one)

theorem invSuccRadius_antitone {N n : Nat}
    (hNn : N <= n) :
    (F C).le (invSuccRadius C n) (invSuccRadius C N) := by
  unfold invSuccRadius
  apply inv_le_inv_of_le_pos C
  · exact IsOrderedFieldBaseLike.nat_succ_pos (F C) N
  · exact IsOrderedFieldBaseLike.nat_succ_pos (F C) n
  · exact nat_le_nat_of_le C (by omega : N + 1 <= n + 1)

/-- The subsequence extracted from a cluster point: stage `k` chooses, by
classical choice, a term at or beyond one past the previous stage's index
that lies within `1 / (k + 1)` of `l`. The one-past threshold makes the
index function strictly increasing; the shrinking radius is the half of the
spec that the Archimedean principle later turns into convergence. -/
noncomputable def clusterIndex {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt C u l) : Nat -> Nat
  | 0 =>
      Classical.choose
        (hcluster (invSuccRadius C 0) (invSuccRadius_pos C 0) 0)
  | k + 1 =>
      Classical.choose
        (hcluster (invSuccRadius C (k + 1))
          (invSuccRadius_pos C (k + 1))
          (clusterIndex hcluster k + 1))

theorem clusterIndex_step {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt C u l)
    (k : Nat) :
    clusterIndex C hcluster k < clusterIndex C hcluster (k + 1) := by
  have hle :
      clusterIndex C hcluster k + 1 <= clusterIndex C hcluster (k + 1) :=
    (Classical.choose_spec
      (hcluster (invSuccRadius C (k + 1))
        (invSuccRadius_pos C (k + 1))
        (clusterIndex C hcluster k + 1))).left
  omega

theorem clusterIndex_subsequence {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt C u l) :
    IsOrderedFieldBaseLike.SubsequenceIndex (clusterIndex C hcluster) :=
  clusterIndex_step C hcluster

theorem clusterIndex_close {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt C u l)
    (k : Nat) :
    (F C).lt
      (IsOrderedFieldBaseLike.dist (F C) (u (clusterIndex C hcluster k)) l)
      (invSuccRadius C k) := by
  cases k with
  | zero =>
      exact
        (Classical.choose_spec
          (hcluster (invSuccRadius C 0)
            (invSuccRadius_pos C 0) 0)).right
  | succ k =>
      exact
        (Classical.choose_spec
          (hcluster (invSuccRadius C (k + 1))
            (invSuccRadius_pos C (k + 1))
            (clusterIndex C hcluster k + 1))).right

/-- The extracted subsequence converges to `l`. This is the only step of
the entry that consumes the Archimedean consequence of completeness:
`invNatArchimedean` makes the radii `1 / (n + 1)` eventually smaller than
the given epsilon, and antitone-ness carries the estimate from the
threshold stage to every later one. -/
theorem clusterSubsequence_tendsto
    (hinvNat : (F C).InvNatArchimedeanPrinciple)
    {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt C u l) :
    IsOrderedFieldBaseLike.SeqTendsto (F C)
      (IsOrderedFieldBaseLike.subsequence u (clusterIndex C hcluster)) l := by
  intro eps heps
  cases hinvNat.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hclose :
          (F C).lt
            (IsOrderedFieldBaseLike.dist (F C)
              (u (clusterIndex C hcluster n)) l)
            (invSuccRadius C n) :=
        clusterIndex_close C hcluster n
      have hradius_le :
          (F C).le (invSuccRadius C n) (invSuccRadius C N) :=
        invSuccRadius_antitone C hn
      have hlt_eps :
          (F C).lt (invSuccRadius C n) eps :=
        IsOrderedFieldBaseLike.lt_of_le_of_lt (F C) hradius_le hN
      dsimp [IsOrderedFieldBaseLike.subsequence, IsOrderedFieldBaseLike.dist]
      exact IsOrderedFieldBaseLike.lt_trans (F C) hclose hlt_eps

/-- A cluster point plus the inverse-natural Archimedean principle yield a
convergent subsequence, in the vocabulary of `HasConvergentSubsequence`.
This is the node-level content of the extraction half of the file. -/
theorem convergent_subsequence_of_cluster
    (hinvNat : (F C).InvNatArchimedeanPrinciple)
    {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt C u l) :
    Exists (fun L : alpha =>
      IsOrderedFieldBaseLike.HasConvergentSubsequence (F C) u L) := by
  refine Exists.intro l ?_
  refine Exists.intro (clusterIndex C hcluster) ?_
  constructor
  · exact clusterIndex_subsequence C hcluster
  · exact clusterSubsequence_tendsto C hinvNat hcluster

/-- The countdown list `N, N - 1, ..., 0` of all indices below `N`; the
witness that an index predicate bounded by `N` is listable. -/
def natListUpTo : Nat -> List Nat
  | 0 => []
  | N + 1 => N :: natListUpTo N

theorem mem_natListUpTo_of_lt :
    forall {n N : Nat}, n < N -> List.Mem n (natListUpTo N)
  | n, 0, h => by omega
  | n, N + 1, h => by
      by_cases hn : n = N
      · subst hn
        exact List.Mem.head _
      · have hnlt : n < N := by omega
        exact List.Mem.tail _ (mem_natListUpTo_of_lt hnlt)

/-- The indices below `N`, as a predicate; together with `natListUpTo` it
is how "only a prefix's worth" is said in the listability vocabulary. -/
def Prefix (N : Nat) : Nat -> Prop :=
  fun n => n < N

theorem prefix_listFinite (N : Nat) :
    Foundation.Cardinal.ListFinite (Prefix N) := by
  refine Exists.intro (natListUpTo N) ?_
  intro n hn
  exact mem_natListUpTo_of_lt hn

/-- The indices whose terms land in the window `[left, c]`. How much of the
sequence a window catches is measured as listability of this predicate, in the
cardinal vocabulary of `Tautology.Foundation.Cardinal` rather than by counting.
-/
def IndexInClosed
    (u : Nat -> alpha) (left c : alpha) : Nat -> Prop :=
  fun n => IsOrderedFieldBaseLike.ClosedInterval (F C) left c (u n)

/-- Only listably many terms of `u` land in `[left, c]`: the window catches
a thin part of the sequence. This is the finiteness half of a good cut
below, and it is exactly the property that fails for windows strictly above
the least upper bound of the good cuts. -/
def IndexFinite
    (u : Nat -> alpha) (left c : alpha) : Prop :=
  Foundation.Cardinal.ListFinite (IndexInClosed C u left c)

/-- The inductive predicate of the supremum argument: a cut `c` with
`left < c ≤ right` whose window `[left, c]` catches only listably many
terms. The cut is demanded strictly above `left` so that the least upper
bound of the good cuts sits strictly above `left` as well; the argument
then locates where the thinness of the sequence ends, and that place turns
out to be a cluster point. -/
def Good (u : Nat -> alpha) (left right c : alpha) : Prop :=
  And ((F C).lt left c)
    (And ((F C).le c right) (IndexFinite C u left c))

theorem prefix_union_index_finite {u : Nat -> alpha}
    {left c : alpha} (N : Nat)
    (hfin : IndexFinite C u left c) :
    Foundation.Cardinal.ListFinite
      (Foundation.Cardinal.SetUnion (Prefix N) (IndexInClosed C u left c)) :=
  Foundation.Cardinal.listFinite_union (prefix_listFinite N) hfin

theorem indexFinite_mono {u : Nat -> alpha} {left c d : alpha}
    (hfin : IndexFinite C u left c)
    (hdc : (F C).le d c) :
    IndexFinite C u left d := by
  apply Foundation.Cardinal.listFinite_mono hfin
  intro n hn
  exact And.intro hn.left ((F C).le_trans hn.right hdc)

theorem indexFinite_of_eventually_not {u : Nat -> alpha} {left c : alpha}
    {N : Nat}
    (h : forall n : Nat, N <= n -> Not (IndexInClosed C u left c n)) :
    IndexFinite C u left c := by
  apply Foundation.Cardinal.listFinite_mono (prefix_listFinite N)
  intro n hn
  by_cases hlt : n < N
  · exact hlt
  · have hle : N <= n := by omega
    exact False.elim (h n hle hn)

theorem dist_left_lt_of_closed_lt {x left c eps : alpha}
    (hc : (F C).lt c ((F C).add left eps))
    (heps : (F C).lt (F C).zero eps)
    (hx : IsOrderedFieldBaseLike.ClosedInterval (F C) left c x) :
    (F C).lt (IsOrderedFieldBaseLike.dist (F C) x left) eps := by
  dsimp [IsOrderedFieldBaseLike.dist]
  apply IsOrderedFieldBaseLike.abs_sub_lt_of_bounds (F C)
  · exact IsOrderedFieldBaseLike.lt_of_lt_of_le (F C)
      (IsOrderedFieldBaseLike.sub_lt_self_of_pos (F C) heps) hx.left
  · exact IsOrderedFieldBaseLike.lt_of_le_of_lt (F C) hx.right hc

theorem not_cluster_eventually_far {u : Nat -> alpha} {l : alpha}
    (hnot : Not (SeqClusterAt C u l)) :
    Exists
      (fun eps : alpha =>
        And ((F C).lt (F C).zero eps)
          (Exists
            (fun N : Nat =>
              forall n : Nat,
                N <= n ->
                  Not ((F C).lt
                    (IsOrderedFieldBaseLike.dist (F C) (u n) l) eps)))) := by
  classical
  by_cases hex :
      Exists
        (fun eps : alpha =>
          And ((F C).lt (F C).zero eps)
            (Exists
              (fun N : Nat =>
                forall n : Nat,
                  N <= n ->
                    Not ((F C).lt
                      (IsOrderedFieldBaseLike.dist (F C) (u n) l) eps))))
  · exact hex
  · have hcluster : SeqClusterAt C u l := by
      intro eps heps N
      by_cases hN :
          Exists
            (fun n : Nat =>
              And (N <= n)
                ((F C).lt
                  (IsOrderedFieldBaseLike.dist (F C) (u n) l) eps))
      · exact hN
      · have hbad :
            Exists
              (fun eps : alpha =>
                And ((F C).lt (F C).zero eps)
                  (Exists
                    (fun N : Nat =>
                      forall n : Nat,
                        N <= n ->
                          Not ((F C).lt
                            (IsOrderedFieldBaseLike.dist (F C) (u n) l) eps)))) := by
          refine Exists.intro eps ?_
          constructor
          · exact heps
          · refine Exists.intro N ?_
            intro n hn hclose
            exact hN (Exists.intro n (And.intro hn hclose))
        exact False.elim (hex hbad)
    exact False.elim (hnot hcluster)

/-- If the sequence does not cluster at `left`, a good cut exists: the
radius and stage at which the tail stays a fixed distance from `left` yield
the half-width point `left + eps / 2` as a good cut, unless it overshoots
`right`, in which case `right` itself is good. This is the nonemptiness
that the least-upper-bound argument is fed. -/
theorem exists_good_of_not_left_cluster {u : Nat -> alpha}
    {left right : alpha}
    (hlt_lr : (F C).lt left right)
    (hnot : Not (SeqClusterAt C u left)) :
    Exists (Good C u left right) := by
  cases not_cluster_eventually_far C hnot with
  | intro eps hepsRest =>
      cases hepsRest.right with
      | intro N hfar =>
          let c0 := (F C).add left (IsOrderedFieldBaseLike.half (F C) eps)
          have hhalf_pos :
              (F C).lt (F C).zero (IsOrderedFieldBaseLike.half (F C) eps) :=
            IsOrderedFieldBaseLike.half_pos (F C) hepsRest.left
          have hleft_c0 : (F C).lt left c0 := by
            have h := (F C).add_lt_add_left hhalf_pos left
            rwa [(F C).add_zero] at h
          have hc0_lt_left_eps :
              (F C).lt c0 ((F C).add left eps) := by
            unfold c0
            exact (F C).add_lt_add_left
              (IsOrderedFieldBaseLike.half_lt_self (F C) hepsRest.left) left
          by_cases hc0_le_right : (F C).le c0 right
          · refine Exists.intro c0 ?_
            constructor
            · exact hleft_c0
            constructor
            · exact hc0_le_right
            · apply indexFinite_of_eventually_not C
              intro n hn hclosed
              exact hfar n hn
                (dist_left_lt_of_closed_lt C hc0_lt_left_eps
                  hepsRest.left hclosed)
          · have hright_le_c0 : (F C).le right c0 := by
              cases (F C).le_total right c0 with
              | inl h => exact h
              | inr h => exact False.elim (hc0_le_right h)
            have hright_lt_left_eps :
                (F C).lt right ((F C).add left eps) :=
              IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
                hright_le_c0 hc0_lt_left_eps
            refine Exists.intro right ?_
            constructor
            · exact hlt_lr
            constructor
            · exact (F C).le_refl right
            · apply indexFinite_of_eventually_not C
              intro n hn hclosed
              exact hfar n hn
                (dist_left_lt_of_closed_lt C hright_lt_left_eps
                  hepsRest.left hclosed)

theorem good_upper_right {u : Nat -> alpha} {left right : alpha} :
    IsUpperBound (F C).le (Good C u left right) right := by
  intro c hc
  exact hc.right.left

theorem good_downward {u : Nat -> alpha} {left right c d : alpha}
    (hc : Good C u left right c)
    (hld : (F C).lt left d)
    (hdc : (F C).le d c) :
    Good C u left right d := by
  constructor
  · exact hld
  constructor
  · exact (F C).le_trans hdc hc.right.left
  · exact indexFinite_mono C hc.right.right hdc

theorem left_lt_lub_of_good {u : Nat -> alpha} {left right s : alpha}
    (hs : IsLeastUpperBound (F C).le (Good C u left right) s)
    (hne : Exists (Good C u left right)) :
    (F C).lt left s := by
  cases hne with
  | intro c hc =>
      exact IsOrderedFieldBaseLike.lt_of_lt_of_le (F C)
        hc.left (hs.left c hc)

/-- Windows strictly above the least upper bound catch a non-listable set
of terms: if `[left, d]` with `s < d ≤ right` caught only listably many,
`d` would itself be a good cut above `s`. This failure of thinness above
the supremum is the infinitude the cluster argument runs on. -/
theorem indexInfinite_above_lub {u : Nat -> alpha}
    {left right s d : alpha}
    (hs : IsLeastUpperBound (F C).le (Good C u left right) s)
    (hleft_s : (F C).lt left s)
    (hsd : (F C).lt s d)
    (hdr : (F C).le d right) :
    Foundation.Cardinal.ListInfinite (IndexInClosed C u left d) := by
  apply Foundation.Cardinal.listInfinite_of_not_listFinite
  intro hfin
  have hld : (F C).lt left d :=
    IsOrderedFieldBaseLike.lt_trans (F C) hleft_s hsd
  have hd_good : Good C u left right d :=
    And.intro hld (And.intro hdr hfin)
  have hds : (F C).le d s :=
    hs.left d hd_good
  exact (IsOrderedFieldBaseLike.not_le_of_lt (F C) hsd) hds

theorem indexInfinite_full {u : Nat -> alpha}
    {left right : alpha}
    (hbounds :
      forall n : Nat,
        IsOrderedFieldBaseLike.ClosedInterval (F C) left right (u n)) :
    Foundation.Cardinal.ListInfinite (IndexInClosed C u left right) := by
  intro xs
  cases Foundation.Cardinal.listInfiniteType_nat xs with
  | intro n hn =>
      exact Exists.intro n (And.intro (hbounds n) hn)

/-- A non-listable predicate escapes every listable one: some index
satisfies `S` but not `T`. This pigeonhole is what lets the cluster
argument step past the bad indices -- a stage's prefix together with a good
window -- and find a genuinely later term. -/
theorem exists_index_outside_finite {S T : Nat -> Prop}
    (hSinf : Foundation.Cardinal.ListInfinite S)
    (hTfin : Foundation.Cardinal.ListFinite T) :
    Exists (fun n : Nat => And (S n) (Not (T n))) := by
  cases hTfin with
  | intro xs hxs =>
      cases hSinf xs with
      | intro n hn =>
          refine Exists.intro n ?_
          constructor
          · exact hn.left
          · intro hT
            exact hn.right (hxs n hT)

/-- The least upper bound of the good cuts is a cluster point. Given a
radius and a stage, a good cut `c` above `s - eps` makes the union of the
stage's prefix with `[left, c]` listable; a term outside that union lies
beyond the stage, above `c`, and still below `s + eps` -- the last bound
coming from `s + eps / 2` when there is room above `s`, and from `right`
itself, using the full index set, when `s = right`. -/
theorem sup_good_is_cluster {u : Nat -> alpha}
    {left right s : alpha}
    (hbounds :
      forall n : Nat,
        IsOrderedFieldBaseLike.ClosedInterval (F C) left right (u n))
    (hne : Exists (Good C u left right))
    (hs : IsLeastUpperBound (F C).le (Good C u left right) s) :
    SeqClusterAt C u s := by
  intro eps heps N
  have hleft_s : (F C).lt left s :=
    left_lt_lub_of_good C hs hne
  have hs_le_right : (F C).le s right :=
    IsOrderedFieldBaseLike.lub_le_of_upper (F C) hs
      (good_upper_right C)
  have hs_minus_lt_s : (F C).lt ((F C).sub s eps) s :=
    IsOrderedFieldBaseLike.sub_lt_self_of_pos (F C) heps
  cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub (F C) hs hs_minus_lt_s with
  | intro c hc =>
      let Bad : Nat -> Prop :=
        Foundation.Cardinal.SetUnion (Prefix N) (IndexInClosed C u left c)
      have hbadFin : Foundation.Cardinal.ListFinite Bad :=
        prefix_union_index_finite C N hc.left.right.right
      have hc_gt : (F C).lt ((F C).sub s eps) c := hc.right
      have hc_le_s : (F C).le c s := hs.left c hc.left
      have choose_from_infinite
          {d : alpha}
          (hInf : Foundation.Cardinal.ListInfinite (IndexInClosed C u left d))
          (hd_lt : (F C).lt d ((F C).add s eps)) :
          Exists
            (fun n : Nat =>
              And (N <= n)
                ((F C).lt
                  (IsOrderedFieldBaseLike.dist (F C) (u n) s) eps)) := by
        cases exists_index_outside_finite hInf hbadFin with
        | intro n hn =>
            have hnotBad : Not (Bad n) := hn.right
            have hnotPrefix : Not (Prefix N n) := by
              intro hp
              exact hnotBad (Or.inl hp)
            have hNn : N <= n := by
              have hnotlt : Not (n < N) := hnotPrefix
              unfold Prefix at hnotlt
              omega
            have hnotClosedC : Not (IndexInClosed C u left c n) := by
              intro hcn
              exact hnotBad (Or.inr hcn)
            have hleft_un : (F C).le left (u n) := hn.left.left
            have hnot_un_le_c : Not ((F C).le (u n) c) := by
              intro hle
              exact hnotClosedC (And.intro hleft_un hle)
            have hc_lt_un : (F C).lt c (u n) := by
              cases (F C).le_total c (u n) with
              | inl hcu =>
                  exact IsOrderedFieldBaseLike.lt_of_le_of_not_le
                    (F C) hcu hnot_un_le_c
              | inr huc =>
                  exact False.elim (hnot_un_le_c huc)
            have hleft_close : (F C).lt ((F C).sub s eps) (u n) :=
              IsOrderedFieldBaseLike.lt_trans (F C) hc_gt hc_lt_un
            have hright_close : (F C).lt (u n) ((F C).add s eps) :=
              IsOrderedFieldBaseLike.lt_of_le_of_lt (F C) hn.left.right hd_lt
            refine Exists.intro n ?_
            constructor
            · exact hNn
            · dsimp [IsOrderedFieldBaseLike.dist]
              exact IsOrderedFieldBaseLike.abs_sub_lt_of_bounds
                (F C) hleft_close hright_close
      by_cases hsr : (F C).lt s right
      · let up := (F C).add s (IsOrderedFieldBaseLike.half (F C) eps)
        have hs_lt_up : (F C).lt s up := by
          have hhalf_pos :
              (F C).lt (F C).zero (IsOrderedFieldBaseLike.half (F C) eps) :=
            IsOrderedFieldBaseLike.half_pos (F C) heps
          have h := (F C).add_lt_add_left hhalf_pos s
          rwa [(F C).add_zero] at h
        have hup_lt_s_eps : (F C).lt up ((F C).add s eps) := by
          unfold up
          exact (F C).add_lt_add_left
            (IsOrderedFieldBaseLike.half_lt_self (F C) heps) s
        by_cases hup_le_right : (F C).le up right
        · have hInf :
              Foundation.Cardinal.ListInfinite (IndexInClosed C u left up) :=
            indexInfinite_above_lub C hs hleft_s hs_lt_up hup_le_right
          exact choose_from_infinite hInf hup_lt_s_eps
        · have hright_le_up : (F C).le right up := by
            cases (F C).le_total right up with
            | inl h => exact h
            | inr h => exact False.elim (hup_le_right h)
          have hright_lt_s_eps : (F C).lt right ((F C).add s eps) :=
            IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
              hright_le_up hup_lt_s_eps
          have hInf :
              Foundation.Cardinal.ListInfinite (IndexInClosed C u left right) :=
            indexInfinite_above_lub C hs hleft_s hsr ((F C).le_refl right)
          exact choose_from_infinite hInf hright_lt_s_eps
      · have hright_le_s : (F C).le right s := by
          by_cases h : (F C).le right s
          · exact h
          · have hlt : (F C).lt s right :=
              IsOrderedFieldBaseLike.lt_of_le_of_not_le (F C)
                hs_le_right h
            exact False.elim (hsr hlt)
        have hright_lt_s_eps : (F C).lt right ((F C).add s eps) := by
          have hs_lt_s_eps : (F C).lt s ((F C).add s eps) := by
            have h := (F C).add_lt_add_left heps s
            rwa [(F C).add_zero] at h
          exact IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
            hright_le_s hs_lt_s_eps
        have hInf :
            Foundation.Cardinal.ListInfinite (IndexInClosed C u left right) :=
          indexInfinite_full C hbounds
        exact choose_from_infinite hInf hright_lt_s_eps

/-- Every bounded sequence has a cluster point. A degenerate bounding
window forces the sequence to be constant, which clusters for free;
otherwise the good cuts are nonempty and bounded, and `exists_lub` -- the
completeness of the bundle, invoked here and nowhere else in this file --
supplies their least upper bound. -/
theorem cluster_of_bounded_sequence
    {u : Nat -> alpha}
    (hbdd : IsOrderedFieldBaseLike.SeqBounded (F C) u) :
    Exists (fun l : alpha => SeqClusterAt C u l) := by
  cases hbdd with
  | intro left hleft =>
      cases hleft with
      | intro right hbounds =>
          have hle_lr : (F C).le left right :=
            (F C).le_trans (hbounds 0).left (hbounds 0).right
          by_cases hlt_lr : (F C).lt left right
          · by_cases hleft_cluster : SeqClusterAt C u left
            · exact Exists.intro left hleft_cluster
            · cases exists_good_of_not_left_cluster C hlt_lr hleft_cluster with
              | intro c0 hc0 =>
                  cases C.exists_lub (Good C u left right)
                      (Exists.intro c0 hc0)
                      (Exists.intro right (good_upper_right C)) with
                  | intro s hs =>
                      exact Exists.intro s
                        (sup_good_is_cluster C hbounds
                          (Exists.intro c0 hc0) hs)
          · have hright_le_left : (F C).le right left := by
              by_cases h : (F C).le right left
              · exact h
              · have hlt : (F C).lt left right :=
                  IsOrderedFieldBaseLike.lt_of_le_of_not_le
                    (F C) hle_lr h
                exact False.elim (hlt_lr hlt)
            have hfreq : ValueFrequent u left := by
              intro N
              refine Exists.intro N ?_
              constructor
              · exact Nat.le_refl N
              · exact (F C).le_antisymm
                  ((F C).le_trans (hbounds N).right hright_le_left)
                  (hbounds N).left
            exact Exists.intro left
              (seqClusterAt_of_valueFrequent C hfreq)

/-- The sequential Bolzano-Weierstrass node holds for the field: a bounded
sequence first yields a cluster point through the supremum argument, and
the inverse-natural Archimedean principle -- here the one completeness
proves, `invNatArchimedean`, not a hypothesis -- upgrades it to a
convergent subsequence. -/
theorem sequentialPrinciple :
    (F C).BolzanoWeierstrassSequentialPrinciple where
  convergent_subsequence := by
    intro u hbdd
    cases cluster_of_bounded_sequence C hbdd with
    | intro l hcluster =>
        exact convergent_subsequence_of_cluster C
          (invNatArchimedean C) hcluster

/-- The entry point into the graph: a Dedekind-complete ordered field
satisfies the sequential Bolzano-Weierstrass node, reached through the
supremum property. The completeness bundle is the whole hypothesis side --
the Archimedean input is derived from it rather than assumed -- in contrast
with the parallel entry `FromNestedSequential`, which works over any
ordered field by taking the nested-interval and dyadic Archimedean
principles as explicit hypotheses. -/
theorem target : Target C :=
  sequentialPrinciple C

end FromSupSequential
end Compactness
end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
