/-!
# Properties that hold from some index onwards

`Eventually P` says that `P n` holds for every `n` past some threshold. Three
facts come with it, and they are exactly the three a limit argument needs: a
property true everywhere is eventually true, an eventual property may be
weakened pointwise, and two eventual properties eventually hold together.

Only the third has content. Two properties arrive with two thresholds and the
conjunction needs one, so `Nat.max` supplies it. Every step in the library
that reads "choose `N` large enough for both" is this lemma.

## The lowest place limits are spoken of

Nothing here mentions an ordered field, a carrier or a sequence of reals; this
is a statement about `Nat` and a predicate, and that is why it can sit at the
very bottom of the dependency order. `Tautology.RealSequence.Basic` imports it
and builds convergence on it, after which it reaches the Euler--Maclaurin
applications, the arithmetic--geometric mean iteration of
`Tautology.RealElliptic.Landen.AGM`, and the exceptional sets of the
Lee--Vyborny theorem.

## The namespace does not follow the directory here

The file sits in `Tautology/Nat/` but declares `Eventually` directly under
`Tautology`, not under `Tautology.Nat` as its three neighbours do -- the full
name is `Tautology.Eventually`. The predicate is about an arbitrary property
of naturals rather than about arithmetic, so it was not filed with the
arithmetic. As elsewhere in this library, the directory records the dependency
position and the namespace the subject.

## Role

Implementation. There is no `Tautology/Nat.lean` region umbrella; each of the
four modules under `Tautology/Nat/` is imported directly by whoever needs it,
this one by `Tautology.RealSequence.Basic`.
The words this header uses in a sense particular to this library -- region,
route, waist, valve, facade, and the three kinds of aggregation module -- are
each defined once, in the header of the root module `Tautology`. This region
has no umbrella to carry that pointer, so the modules that use the vocabulary
carry it themselves.

-/

namespace Tautology

/-- `P` holds from some index onwards: some threshold `N` with `P n` whenever
`N <= n`. The threshold stays inside the `Exists`, so combining eventual
properties is combining thresholds -- which is all `Eventually.and` does. -/
def Eventually (P : Nat -> Prop) : Prop :=
  Exists (fun N : Nat => forall n : Nat, N <= n -> P n)

namespace Eventually

theorem of_forall {P : Nat -> Prop}
    (h : forall n : Nat, P n) :
    Eventually P :=
  Exists.intro 0 (fun n _ => h n)

theorem mono {P Q : Nat -> Prop}
    (hPQ : forall n : Nat, P n -> Q n)
    (hP : Eventually P) :
    Eventually Q := by
  cases hP with
  | intro N hN =>
      exact Exists.intro N (fun n hn => hPQ n (hN n hn))

/-- Two eventual properties hold together eventually; the threshold is
`Nat.max` of the two in hand. This is where two separately chosen bounds
become one, without re-proving either side. -/
theorem and {P Q : Nat -> Prop}
    (hP : Eventually P)
    (hQ : Eventually Q) :
    Eventually (fun n => And (P n) (Q n)) := by
  cases hP with
  | intro NP hNP =>
      cases hQ with
      | intro NQ hNQ =>
          refine Exists.intro (Nat.max NP NQ) ?_
          intro n hn
          exact And.intro
            (hNP n (Nat.le_trans (Nat.le_max_left NP NQ) hn))
            (hNQ n (Nat.le_trans (Nat.le_max_right NP NQ) hn))

end Eventually
end Tautology
