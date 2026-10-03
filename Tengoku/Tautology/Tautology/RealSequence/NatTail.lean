import Tengoku.Tautology.Tautology.RealSequence.Basic
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean

/-!
# Index sequences that run to infinity

A small file about sequences of indices rather than of field elements: what it
means for one to escape every bound, and that the identity and successor
sequences do.

It exists because several later arguments -- Euler's limit, power estimates --
need to feed an index sequence into a limit statement and want that escape
property as a named hypothesis rather than as an inline `Nat` fact.

## Position and role

Implementation module over an arbitrary ordered field; completeness plays no
part.
-/

namespace Tautology

/-- An index map eventually exceeds every natural bound. This is the
divergence notion for reindexings that do not disturb convergence
(`seqTendsto_comp_natTendstoInfinity`) and that make reindexed harmonic
tails vanish. -/
def NatTendstoInfinity (k : Nat -> Nat) : Prop :=
  forall M : Nat, Eventually (fun n : Nat => M <= k n)

theorem natId_tendstoInfinity :
    NatTendstoInfinity (fun n : Nat => n) := by
  intro M
  exact Exists.intro M (fun n hn => hn)

theorem natSucc_tendstoInfinity :
    NatTendstoInfinity (fun n : Nat => n + 1) := by
  intro M
  exact Exists.intro M
    (fun n hn =>
      Nat.le_trans hn (Nat.le_succ n))

/-- Divergence to infinity passes along eventual domination: if `k n <= l n`
from some index on and `k` diverges, so does `l`. This lets an argument
replace a concrete indexing by whatever map it has produced. -/
theorem natTendstoInfinity_mono
    {k l : Nat -> Nat}
    (hk : NatTendstoInfinity k)
    (hkl : Eventually (fun n : Nat => k n <= l n)) :
    NatTendstoInfinity l := by
  intro M
  cases hk M with
  | intro Nk hNk =>
      cases hkl with
      | intro Nkl hNkl =>
          refine Exists.intro (Nat.max Nk Nkl) ?_
          intro n hn
          exact Nat.le_trans
            (hNk n (Nat.le_trans (Nat.le_max_left Nk Nkl) hn))
            (hNkl n (Nat.le_trans (Nat.le_max_right Nk Nkl) hn))

namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
