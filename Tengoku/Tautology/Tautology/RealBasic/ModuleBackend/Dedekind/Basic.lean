module

import Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Rat

/-!
# Cuts

A `Cut` is a set of rationals that is nonempty, proper, downward closed, and
without a greatest element -- the lower half of a Dedekind cut, carried as a
predicate `Rat -> Prop` with its four conditions as fields.

Downward closure with no greatest element is what makes the representation
unique: the two halves of a cut determine each other, and forbidding a maximum
rules out the ambiguity at rational points, where the cut of `q` could
otherwise be taken with or without `q` itself. So `Cut.ext` -- two cuts with
the same members are equal -- holds without a quotient, and the Dedekind
backend is the only one of the three that is not a quotient construction.

`ofRat` embeds the rationals. Everything below builds the field operations on
cuts directly, so `Cut` is the carrier itself rather than a representative of
one.

## Position in the development

Base of the Dedekind backend, above `ModuleBackend.Rat`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind

/-- The carrier of the Dedekind backend: the lower half of a cut, carried as
a predicate on the rationals. The four fields are nonemptiness and properness,
which say that the predicate names a single position rather than none or all
of the line, and downward closure together with the absence of a greatest
element, which make the member set alone determine the cut. -/
structure Cut where
  mem : Rat -> Prop
  nonempty : Exists mem
  proper : Exists (fun q : Rat => Not (mem q))
  downward : forall {p q : Rat}, p < q -> mem q -> mem p
  no_greatest :
    forall {q : Rat}, mem q -> Exists (fun r : Rat => And (mem r) (q < r))

namespace Cut

/-- Two cuts with pointwise equivalent membership are equal. Membership is
the entire structure of a cut, so this is plain function extensionality and
no quotient is involved -- the other two backends construct their carriers as
quotients of representatives and only ever obtain equality through their
setoids. -/
theorem ext {x y : Cut} (h : forall q : Rat, x.mem q <-> y.mem q) :
    x = y := by
  cases x with
  | mk xmem xnonempty xproper xdownward xno_greatest =>
      cases y with
      | mk ymem ynonempty yproper ydownward yno_greatest =>
          dsimp at h
          have hmem : xmem = ymem := funext (fun q => propext (h q))
          subst hmem
          rfl

/-- Embeds a rational as the cut of everything strictly below it. Strictness
is what makes the result a cut: `Rat.exists_between` supplies, above any
member, a larger rational still below `a`, so the member set has no greatest
element. -/
def ofRat (a : Rat) : Cut where
  mem q := q < a
  nonempty :=
    Exists.intro (a - 1) (Tautology.RealBasic.ModuleBackend.Rat.sub_one_lt a)
  proper := Exists.intro a _root_.Rat.lt_irrefl
  downward := by
    intro p q hpq hqa
    exact Tautology.RealBasic.ModuleBackend.Rat.lt_trans hpq hqa
  no_greatest := by
    intro q hqa
    cases Tautology.RealBasic.ModuleBackend.Rat.exists_between hqa with
    | intro r hr =>
        exact Exists.intro r (And.intro hr.right hr.left)

instance : Zero Cut where
  zero := ofRat 0

instance : One Cut where
  one := ofRat 1

theorem mem_zero {q : Rat} : (0 : Cut).mem q <-> q < 0 :=
  Iff.rfl

theorem mem_one {q : Rat} : (1 : Cut).mem q <-> q < 1 :=
  Iff.rfl

/-- A member of a cut is at most any nonmember: were the nonmember smaller,
downward closure would pull it inside. This is the bridge through which later
proofs compare a cut's boundary with rational order, notably the properness
arguments of addition and multiplication. -/
theorem le_of_mem_of_not_mem {x : Cut} {a b : Rat}
    (ha : x.mem a) (hb : Not (x.mem b)) :
    a <= b := by
  have hnlt : Not (b < a) := by
    intro hba
    exact hb (x.downward hba ha)
  exact _root_.Rat.not_lt.mp hnlt

theorem exists_mem_gt_of_mem_of_mem {x : Cut} {a b : Rat}
    (ha : x.mem a) (hb : x.mem b) :
    Exists (fun c : Rat => And (x.mem c) (And (a < c) (b < c))) := by
  cases _root_.Rat.le_total (a := a) (b := b) with
  | inl hab =>
      cases x.no_greatest hb with
      | intro c hc =>
          exact Exists.intro c
            (And.intro hc.left
              (And.intro
                (Tautology.RealBasic.ModuleBackend.Rat.lt_of_le_of_lt
                  hab hc.right)
                hc.right))
  | inr hba =>
      cases x.no_greatest ha with
      | intro c hc =>
          exact Exists.intro c
            (And.intro hc.left
              (And.intro hc.right
                (Tautology.RealBasic.ModuleBackend.Rat.lt_of_le_of_lt
                  hba hc.right)))

end Cut

end Dedekind
end ModuleBackend
end RealBasic
end Tautology
