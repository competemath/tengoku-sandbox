/-!
# Gate collision fixture (issue #212 B0 codex-gate pass-7 finding 1)

NOT a scratch gate target and NOT in the release cone — this module exists only
so that `scripts/scratch_fixture_selftest.lean` (run by check-scratch-pins.sh)
can demonstrate, on a COMPILED module, that hand-written declarations whose
names lexically collide with compiler-generated companion patterns
(`P.ibelow`, `C.mk.noConfusionType`, `d.congr_simp`) or with internal-auxiliary
patterns (`P.proof_1`) are enumerated by the static olean channel
(`ModuleData.constNames`) like any other constant.  Under the retired pass-4–6
suffix classifiers these names were labeled `child`/`internal` and thereby
dodged the 54-name surface equality; under the pass-7 total-manifest gate each
would be a new frozen DECL line in scripts/scratch-manifest.expected — had they
been declared in a gate target, the byte-diff would fail regardless of label.

Do NOT add this module to the gate targets or import it from one: its whole
point is to carry deliberately collision-named junk that must stay outside the
frozen manifest.
-/

namespace LerayHopf.ScratchFixture

structure Probe where
  x : Nat

/-- Hand-written; lexically an inductive companion (`ibelow` suffix, inductive
parent) — the retired classifier labeled this `child`. -/
theorem Probe.ibelow : True := trivial

/-- Hand-written; lexically a constructor companion (`noConfusionType` suffix,
constructor parent) — the retired classifier labeled this `child`. -/
theorem Probe.mk.noConfusionType : True := trivial

def probeDef : Nat := 0

-- NOTE (negative fixture, verified empirically on this toolchain): the
-- def-parent companion suffixes (`eq_def`, `eq_unfold`, `congr_simp`) CANNOT be
-- collision-declared at all — v4.31 rejects e.g.
--   theorem probeDef.congr_simp : True := trivial
-- with "`…probeDef.congr_simp` is a reserved name".  That collision class is
-- closed upstream by the elaborator's reserved-name machinery; the three
-- declarable classes below are the ones the total-manifest gate must (and does)
-- catch.

/-- Hand-written; `Name.isInternalDetail` is purely lexical, so this reads as an
internal proof auxiliary — the retired classifier labeled this `internal`. -/
theorem Probe.proof_1 : True := trivial

/-!
## Serializer discrimination fixtures (pass-9 finding 1)

The pass-8 serializer memoized on `BEq Expr` = `Expr.eqv` (alpha-equivalence,
which ignores binder names and binder info), so a REPEATED subterm could reuse
the index of an earlier alpha-equivalent occurrence and a binder rename in the
later occurrence left the stream — hence the digest — unchanged, silently
defeating the documented "binder names included, fail-closed" property.  The
pass-9 serializer memoizes on exact structural equality (`Expr.equal` via
`ExprStructEq`).  Each pair below is alpha-EQUIVALENT (`Expr.eqv` = true — the
retired memoization would have collapsed them to identical streams) but
structurally distinct; `scripts/scratch_reader.lean` asserts per run that the
pair members' canonical digests DIFFER, and that `Expr.eqv` really does equate
them (so the fixture keeps exercising the intended collision class).
-/

/-- Baseline: the same Pi subterm repeated with the SAME binder name. -/
theorem alphaSame : ((∀ x : Nat, x = x) → True) → ((∀ x : Nat, x = x) → True) → True :=
  fun _ _ => trivial

/-- Alpha-variant of `alphaSame`: second occurrence renames the binder — the
type is `Expr.eqv`-equal to `alphaSame`'s but must digest differently. -/
theorem alphaRenamed : ((∀ x : Nat, x = x) → True) → ((∀ y : Nat, y = y) → True) → True :=
  fun _ _ => trivial

/-- Baseline: the same Pi subterm repeated with the SAME (explicit) binder info. -/
theorem binfoBase : ((∀ (n : Nat), n = n) → True) → ((∀ (n : Nat), n = n) → True) → True :=
  fun _ _ => trivial

/-- BinderInfo-variant of `binfoBase`: second occurrence makes the binder
implicit — again `Expr.eqv`-equal but must digest differently. -/
theorem binfoVariant : ((∀ (n : Nat), n = n) → True) → ((∀ {n : Nat}, n = n) → True) → True :=
  fun _ _ => trivial

end LerayHopf.ScratchFixture
