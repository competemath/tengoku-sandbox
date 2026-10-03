module

public import Init.Data.Nat.Lemmas

/-!
# The least natural satisfying a predicate

Well-ordering, in the form the library actually uses: `least p h` takes a
predicate and a proof that something satisfies it, and returns the smallest
such natural, with `least_spec` and `least_min` saying that it satisfies `p`
and that nothing smaller does.

The construction avoids well-founded recursion entirely. `Classical.choose h`
turns the bare existence proof into one concrete witness, which is an upper
bound on the answer; `firstAux p n` then does an ordinary bounded downward
scan below that bound. So the recursion is structural on a `Nat`, and the only
thing classical choice is used for is producing the search bound.

## Two things about the signatures that look wrong and are not

`firstAux` takes `[DecidablePred p]`, an instance argument. This library
forbids typeclasses, and this is not an exception to that: `Decidable` is a
core Lean notion, not a hierarchy of this project's own, and the restriction
is about not building an abstraction hierarchy out of classes. The point to
notice is that the obligation stops at the auxiliary function -- **`least`
itself takes no instance argument**, only `Exists p`, because it discharges
decidability internally with `classical`. Consumers therefore never have to
supply one.

**This file is one of exactly two outside `RealBasic/ModuleBackend/` that use
the Lean module system.** Of the 67 files declaring `module`, 65 are the sealed
backend subtree; the other two are this one and
`Tautology.Foundation.OrderField`. The reason is mechanical rather than
architectural: a `module` may only `public import` another `module`, and the
sealed backends need both of these, so both had to be declared that way.
`RealBasic/ ModuleBackend/Nat/Least.lean` is a one-line `public import` of this
file and nothing else.

## Position in the development

Bottom of the dependency order, on `Nat` alone, and unusually widely used:
`Tautology.RealBootstrap.RationalDensity` (least integer above a value),
`Tautology.RealSequence.BaseExpansionExistence` (the digit at each stage),
`Tautology.RealCompactness.ClosedInterval.LebesgueToFinite`,
`Tautology.RealIntegral.EqualPartition.AdditivityApprox`, and three of the
interval partition modules under `RealFunction`.

## Role

Implementation. There is no `Tautology/Nat.lean` region umbrella; this module
is imported directly by each consumer.
The words this header uses in a sense particular to this library -- region,
route, waist, valve, facade, and the three kinds of aggregation module -- are
each defined once, in the header of the root module `Tautology`. This region
has no umbrella to carry that pointer, so the modules that use the vocabulary
carry it themselves.

-/

namespace Tautology
namespace Nat

/-- The bounded scan under `least`: `firstAux p n` recurses upward on `n`,
keeping the least satisfying index seen so far and proposing the new index
itself only when the accumulated answer fails. Structural recursion on the
bound; the `[DecidablePred p]` obligation originates here and is discharged
before `least` exposes anything. -/
public def firstAux (p : _root_.Nat -> Prop) [DecidablePred p] :
    _root_.Nat -> _root_.Nat
  | 0 => 0
  | n + 1 =>
      if p (firstAux p n) then
        firstAux p n
      else
        n + 1

public theorem firstAux_le (p : _root_.Nat -> Prop) [DecidablePred p]
    (n : _root_.Nat) :
    firstAux p n <= n := by
  induction n with
  | zero =>
      unfold firstAux
      omega
  | succ n ih =>
      unfold firstAux
      by_cases h : p (firstAux p n)
      · simp [h]
        omega
      · simp [h]

/-- Correctness of the scan within range: if some satisfying index lies at
or below `n`, then the returned value satisfies `p`. The hypothesis is load
bearing -- with nothing satisfying below, the scan returns the top index `n`
itself, which is why no unconditional spec is stated. -/
public theorem firstAux_spec_of_exists (p : _root_.Nat -> Prop)
    [DecidablePred p] {n : _root_.Nat}
    (h : Exists (fun k => And (k <= n) (p k))) :
    p (firstAux p n) := by
  induction n with
  | zero =>
      cases h with
      | intro k hk =>
          have hk0 : k = 0 := by omega
          subst hk0
          unfold firstAux
          exact hk.right
  | succ n ih =>
      unfold firstAux
      by_cases hfirst : p (firstAux p n)
      · simp [hfirst]
      · simp [hfirst]
        cases h with
        | intro k hk =>
            by_cases hkn : k <= n
            · have hbad : p (firstAux p n) :=
                ih (Exists.intro k (And.intro hkn hk.right))
              exact False.elim (hfirst hbad)
            · have hk_eq : k = n + 1 := by omega
              rw [hk_eq] at hk
              exact hk.right

/-- Minimality within range: the scan returns an index at most every
satisfying `k <= n`. Together with `firstAux_spec_of_exists` this makes the
returned value the least satisfying index in range, the whole contract of
the scan. -/
public theorem firstAux_min (p : _root_.Nat -> Prop) [DecidablePred p]
    {n k : _root_.Nat}
    (hk : k <= n)
    (hpk : p k) :
    firstAux p n <= k := by
  revert k
  induction n with
  | zero =>
      intro k hk hpk
      have hk0 : k = 0 := by omega
      subst hk0
      unfold firstAux
      omega
  | succ n ih =>
      intro k hk hpk
      unfold firstAux
      by_cases hfirst : p (firstAux p n)
      · simp [hfirst]
        by_cases hkn : k <= n
        · exact ih hkn hpk
        · have hk_eq : k = n + 1 := by omega
          rw [hk_eq]
          have hle := firstAux_le p n
          omega
      · simp [hfirst]
        by_cases hkn : k <= n
        · have hbad : p (firstAux p n) :=
            firstAux_spec_of_exists p
              (Exists.intro k (And.intro hkn hpk))
          exact False.elim (hfirst hbad)
        · omega

/-- The least natural satisfying `p`, given that one exists. Classical
choice turns the existence proof into a concrete bound for the scan, so
neither well-founded recursion nor decidability is asked of the caller;
`least_spec` and `least_min` then state leastness outright, not merely below
the chosen bound. -/
public noncomputable def least (p : _root_.Nat -> Prop)
    (h : Exists p) : _root_.Nat := by
  classical
  exact firstAux p (Classical.choose h)

public theorem least_spec (p : _root_.Nat -> Prop)
    (h : Exists p) :
    p (least p h) := by
  classical
  unfold least
  exact firstAux_spec_of_exists p
    (Exists.intro (Classical.choose h)
      (And.intro (_root_.Nat.le_refl _) (Classical.choose_spec h)))

public theorem least_min (p : _root_.Nat -> Prop)
    (h : Exists p) {k : _root_.Nat}
    (hpk : p k) :
    least p h <= k := by
  classical
  unfold least
  by_cases hkle : k <= Classical.choose h
  · exact firstAux_min p hkle hpk
  · have hle := firstAux_le p (Classical.choose h)
    omega

end Nat
end Tautology
