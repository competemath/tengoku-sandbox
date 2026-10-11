/-
arithUniverse — two independent kernel-arithmetic examinations (docs/jinshi.md, head K), synthetic and SELF-CONTAINED: this
file does not read the examined corpus at all, it generates its own test terms. `c : Ctx` is used only for `Finding.module`
bookkeeping, as `decide`'s own summary line already does (`c.mods.headD .anonymous`).

(A) the universe fuzzer. The kernel's sole arbiter of whether two `Sort`s are the same type is `is_equivalent`/`normalize`
over `max`/`imax`/`succ` level expressions — a purely syntactic sort-and-subsume algorithm. If it ever judges two DIFFERENT
universes equivalent, that is a direct path to a Type-in-Type-style soundness hole; if it is needlessly conservative, that
is a completeness gap (not unsound, but worth knowing). A hand-written family of level-algebra identities over a small
alphabet of params (`u, v, w`) and small offsets (0..4) — commutativity, associativity, idempotence, the zero identities,
`succ`-distributivity over `max`, subsumption of a smaller offset of the SAME param nested inside `max` (the "subsumed by
succ^k" branch the kernel's normalize must take), and the `imax _ zero` / `imax _ (succ _)` case-split boundary — is checked
two ways: against an INDEPENDENT semantic model (a level evaluated as a function from an assignment of each param to a small
`Nat`, to a `Nat` result, literally the standard max/imax/succ interpretation, checked over every assignment of `u, v, w` to
`0..4`), and against the kernel's own notion of equivalence (`isDefEq` on `Expr.sort l1 =?= Expr.sort l2`: safe, public, the
same mechanism `Jinshi/Roundtrip.lean` already calls `isDefEq` through). Every pair below is a level-algebra identity true
for every `Nat` value of its params, not only the grid checked — the grid is this file's own confirmation, not the proof.
A pair the model confirms on the grid that the kernel's `isDefEq` refuses is a `fail`, with both levels and the evaluation
trace printed: by construction this tests the kernel against this examination's OWN independent semantics, not a corpus
assumption. Zero disagreements is the expected, unremarkable outcome; the summary finding says so either way.

(B) the Nat arithmetic fuzzer. For closed `Nat` literals the kernel bypasses the recursor-based `Nat.add`/`sub`/`mul`/`pow`/
`mod`/`div`/bitwise-op definitions and computes directly with a second, independent GMP-backed C++ implementation that must
agree with the Lean-level definition bit for bit. There is only ONE Lean-level declaration per operation — the native path
is a kernel-internal `whnf` shortcut, not a second declaration — so the test is not "native op = recursive op" but: does the
proposition `a <op> b = <the literal this file independently computed in Python>` decide to `true`
(`Jinshi.decideOne`, the exact `Decidable.decide` reduction `Jinshi/Decide.lean` already runs on the tree's own theorems)?
Every expected literal below was computed with Python's arbitrary-precision arithmetic, not by hand: `Nat.sub` truncates at
zero, `Nat.div`/`Nat.mod` by `0` return `0`/`n` (Lean's own totalising definitions, not an error), and the bitwise/shift ops
match Python's `&`/`|`/`^`/`<<`/`>>` on non-negative integers exactly (`Nat` has no sign, so there is no two's-complement
subtlety to get backwards). `pow`/`shiftLeft` use exponents/shift counts up to 100 to stress the kernel's size bounds
without emitting an astronomically large decimal literal into this source file (a shift count near `UINT_MAX` itself would
produce a numeral of billions of bits — impractical for a regression test; 40/64/100 are the practical stand-ins).

Both sub-checks are heartbeat-capped per case (`Jinshi/Decide.lean`'s `decide` and `Jinshi/Mutants.lean`'s `mutantsGuard`
pattern) so a single pathological case cannot hang the run; one `fail` or `info` finding per case that is not a plain
agreement, and one summary `info` finding per run with tried/agreed/disagreed/capped counts for each sub-check.
-/
import Jinshi.Base
import Jinshi.Decide
open Lean Meta

namespace Jinshi

/-! ## a shared heartbeat guard (the pattern of `Jinshi/Decide.lean` and `Jinshi/Mutants.lean`'s `mutantsGuard`) -/

/-- heartbeats (in the option's unit of 1000) each `isDefEq`/`decideOne` check in this file may spend -/
def arithUniverseHeartbeats : Nat := 20000

/-- run `x` with its own heartbeat budget; every exception, runtime ones included, becomes `none` (capped, not a crash) -/
def arithUniverseGuard (x : MetaM α) : MetaM (Option α) :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := arithUniverseHeartbeats * 1000 }) <|
    withCurrHeartbeats <|
      tryCatchRuntimeEx (some <$> x) fun _ => pure none

/-! ## (A) the universe fuzzer -/

def uN : Name := `u
def vN : Name := `v
def wN : Name := `w

def pu : Level := Level.param uN
def pv : Level := Level.param vN
def pw : Level := Level.param wN

/-- `l` lifted by `k` applications of `succ` -/
def lsucc : Nat → Level → Level
  | 0, l => l
  | k + 1, l => Level.succ (lsucc k l)

/-- the examination's OWN ground truth, independent of Lean's level code: a level evaluated under an assignment of its
params to small `Nat`s, the standard max/imax/succ interpretation (`imax l1 l2` is `0` exactly when `l2` evaluates to `0`,
`max` otherwise). -/
partial def levelEval (assign : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => levelEval assign l + 1
  | .max l1 l2 => max (levelEval assign l1) (levelEval assign l2)
  | .imax l1 l2 =>
    let v2 := levelEval assign l2
    if v2 == 0 then 0 else max (levelEval assign l1) v2
  | .param n => assign n
  | .mvar _ => 0  -- the generator below never produces one; a defensive default only

/-- a level printed as its syntax tree, independent of any `ToString`/pretty-printer instance (safest when this file
cannot be compiled locally before it is pushed) -/
partial def levelShow : Level → String
  | .zero => "0"
  | .succ l => s!"succ({levelShow l})"
  | .max l1 l2 => s!"max({levelShow l1}, {levelShow l2})"
  | .imax l1 l2 => s!"imax({levelShow l1}, {levelShow l2})"
  | .param n => n.toString
  | .mvar _ => "?m"

/-- every assignment of `u, v, w` to `0..4`: the grid the model is checked over -/
def levelGrid : List (Nat × Nat × Nat) :=
  (List.range 5).flatMap fun a => (List.range 5).flatMap fun b => (List.range 5).map fun c => (a, b, c)

def levelAssign (a b c : Nat) (n : Name) : Nat :=
  if n == uN then a else if n == vN then b else if n == wN then c else 0

/-- `l1` and `l2` agree at every point of `levelGrid`: `none`, or the first point and values where they do not (there
should never be one below: every pair is a known level-algebra identity, true for every `Nat` value of its params, and
the grid is only this file's own confirmation of that) -/
def levelModelAgrees (l1 l2 : Level) : Option (Nat × Nat × Nat × Nat × Nat) := Id.run do
  for (a, b, c) in levelGrid do
    let assign := levelAssign a b c
    let v1 := levelEval assign l1
    let v2 := levelEval assign l2
    if v1 != v2 then return some (a, b, c, v1, v2)
  return none

/-- a handful of representative trees over `max`/`imax`/`succ`, the alphabet `u, v, w` and offsets `0..4`: commutativity,
associativity, idempotence, the zero identities, `succ`-distributivity, subsumption of a smaller offset of the SAME param
nested inside `max` (stressing the "subsumed by succ^k" branch), and the `imax _ zero` / `imax _ (succ _)` case-split
boundary, including pairs that mix two DIFFERENT params that both collapse to the same constant. -/
def levelPairs : List (String × Level × Level) :=
  [ ("max-comm-uv", Level.max pu pv, Level.max pv pu)
  , ("max-comm-vw", Level.max pv pw, Level.max pw pv)
  , ("max-assoc-uvw", Level.max (Level.max pu pv) pw, Level.max pu (Level.max pv pw))
  , ("max-idem-u", Level.max pu pu, pu)
  , ("max-idem-succ2u", Level.max (lsucc 2 pu) (lsucc 2 pu), lsucc 2 pu)
  , ("max-left-id-zero", Level.max Level.zero pu, pu)
  , ("max-right-id-zero", Level.max pu Level.zero, pu)
  , ("max-subsume-u-succu", Level.max pu (lsucc 1 pu), lsucc 1 pu)
  , ("max-subsume-u-succ4u", Level.max pu (lsucc 4 pu), lsucc 4 pu)
  , ("max-subsume-succ2u-succ4u", Level.max (lsucc 2 pu) (lsucc 4 pu), lsucc 4 pu)
  , ("max-subsume-succ3u-succ1u", Level.max (lsucc 3 pu) (lsucc 1 pu), lsucc 3 pu)
  , ("max-subsume-nested", Level.max (lsucc 3 pu) (Level.max (lsucc 1 pu) (lsucc 2 pu)), lsucc 3 pu)
  , ("succ-distrib-max-uv", Level.succ (Level.max pu pv), Level.max (Level.succ pu) (Level.succ pv))
  , ("succ-distrib-max-succ1u-v", Level.succ (Level.max (lsucc 1 pu) pv), Level.max (lsucc 2 pu) (Level.succ pv))
  , ("max-comm-offsets-mixed-params", Level.max (lsucc 2 pu) (lsucc 1 pv), Level.max (lsucc 1 pv) (lsucc 2 pu))
  , ("max-assoc-offsets-mixed", Level.max (Level.max (lsucc 1 pu) pv) (lsucc 2 pw),
     Level.max (lsucc 1 pu) (Level.max pv (lsucc 2 pw)))
  , ("imax-zero-left", Level.imax pu Level.zero, Level.zero)
  , ("imax-zero-left-succ2v", Level.imax (lsucc 2 pv) Level.zero, Level.zero)
  , ("imax-succ-eq-max-u-succv", Level.imax pu (Level.succ pv), Level.max pu (Level.succ pv))
  , ("imax-succ-eq-max-succ2u-succw", Level.imax (lsucc 2 pu) (Level.succ pw), Level.max (lsucc 2 pu) (Level.succ pw))
  , ("imax-left-zero-id", Level.imax Level.zero pu, pu)
  , ("imax-left-zero-id-succ3v", Level.imax Level.zero (lsucc 3 pv), lsucc 3 pv)
  , ("imax-idem-u", Level.imax pu pu, pu)
  , ("imax-idem-succ2w", Level.imax (lsucc 2 pw) (lsucc 2 pw), lsucc 2 pw)
  , ("imax-param-param-both-zero-case", Level.imax pu Level.zero, Level.imax pv Level.zero)
  , ("imax-nested-succ", Level.imax pu (Level.imax pv (Level.succ pw)), Level.imax pu (Level.max pv (Level.succ pw)))
  , ("imax-max-mixed-succ-nonzero", Level.imax (Level.max pu pv) (Level.succ pw), Level.max (Level.max pu pv) (Level.succ pw))
  , ("imax-zero-case-two-forms", Level.imax (Level.succ pu) Level.zero, Level.imax (lsucc 4 pv) Level.zero)
  , ("succ-collapse", lsucc 2 (lsucc 2 pu), lsucc 4 pu)
  , ("max-subsume-three-offsets-mixed-order", Level.max (lsucc 4 pu) (Level.max (lsucc 2 pu) (lsucc 3 pu)), lsucc 4 pu)
  , ("max-assoc-three-params-offsets", Level.max (Level.succ pu) (Level.max (lsucc 2 pv) (lsucc 3 pw)),
     Level.max (Level.max (Level.succ pu) (lsucc 2 pv)) (lsucc 3 pw))
  , ("imax-chain-zero", Level.imax pu (Level.imax pv Level.zero), Level.zero)
  , ("imax-chain-nonzero", Level.imax pu (Level.imax (Level.succ pv) (Level.succ pw)),
     Level.max pu (Level.max (Level.succ pv) (Level.succ pw)))
  , ("max-comm-high-offset", Level.max (lsucc 4 pu) (lsucc 4 pv), Level.max (lsucc 4 pv) (lsucc 4 pu))
  ]

def arithUniverseLevels (mod : Name) : MetaM (Array Finding × Nat × Nat × Nat × Nat) := do
  let mut out := #[]
  let mut tried := 0
  let mut agreed := 0
  let mut disagreed := 0
  let mut capped := 0
  for (label, l1, l2) in levelPairs do
    tried := tried + 1
    match levelModelAgrees l1 l2 with
    | some (a, b, c, v1, v2) =>
      -- this file's own identity does not hold on the grid: a bug in the GENERATOR, never reported as a kernel finding
      let detail := s!"universe pair `{label}` is not actually a model identity: at (u,v,w)=({a},{b},{c}), " ++
        s!"eval l1 = {v1} ≠ eval l2 = {v2} (l1 = {levelShow l1}, l2 = {levelShow l2}) — " ++
        s!"this examination's own generator is wrong here, not the kernel"
      out := out.push { check := "arithUniverse", severity := "warn", module := mod, name := Name.mkSimple label, detail }
    | none =>
      let verdict ← arithUniverseGuard (isDefEq (Expr.sort l1) (Expr.sort l2))
      match verdict with
      | some true => agreed := agreed + 1
      | some false =>
        disagreed := disagreed + 1
        let trace := ([(0, 1, 2), (1, 2, 3), (3, 4, 0)] : List (Nat × Nat × Nat)).map fun (a, b, c) =>
          s!"(u={a},v={b},w={c})↦{levelEval (levelAssign a b c) l1}"
        let detail := s!"universe pair `{label}`: l1 = {levelShow l1}, l2 = {levelShow l2} — the independent model says " ++
          s!"EQUIVALENT for every (u,v,w) in 0..4 ({", ".intercalate trace}, …) but the kernel's isDefEq on " ++
          s!"Sort l1 =?= Sort l2 says NOT EQUIVALENT: either a kernel bug (unsound over-conservatism on a " ++
          s!"case this examination can prove true independently of it) or a flaw in this model"
        out := out.push { check := "arithUniverse", severity := "fail", module := mod, name := Name.mkSimple label, detail }
      | none =>
        capped := capped + 1
        let detail := s!"universe pair `{label}` (l1 = {levelShow l1}, l2 = {levelShow l2}): isDefEq did not finish within " ++
          s!"the heartbeat cap, a resource cap rather than a disagreement"
        out := out.push { check := "arithUniverse", severity := "info", module := mod, name := Name.mkSimple label, detail }
  return (out, tried, agreed, disagreed, capped)

/-! ## (B) the Nat arithmetic fuzzer -/

/-- the kernel-accelerated `Nat` operation a case's label names (the exact names `Jinshi/Forensics.lean`'s `kernelNat`
already lists as computed by the kernel's own bignum code) -/
def natOpConst : String → Name
  | "add" => ``Nat.add
  | "sub" => ``Nat.sub
  | "mul" => ``Nat.mul
  | "div" => ``Nat.div
  | "mod" => ``Nat.mod
  | "pow" => ``Nat.pow
  | "land" => ``Nat.land
  | "lor" => ``Nat.lor
  | "xor" => ``Nat.xor
  | "shiftLeft" => ``Nat.shiftLeft
  | "shiftRight" => ``Nat.shiftRight
  | _ => ``Nat.add  -- unreachable: every label `natCases` uses is one of the above

/-- (label, op, a, b, expected): `expected` was computed independently in Python (`a_python_op_b`), not by hand — `sub`
truncates at `0`, `div`/`mod` by `0` give `0`/`a` (Lean's own total definitions), the rest match Python's operators on
non-negative integers exactly. `pow`/`shiftLeft` use exponents/counts up to 100: large enough to leave the small-literal
fast path, small enough that the expected decimal literal stays a few dozen digits. -/
def natCases : List (String × String × Nat × Nat × Nat) :=
  [ ("add-zero", "add", 0, 0, 0)
  , ("add-small", "add", 5, 7, 12)
  , ("add-2^32-1-plus-1", "add", 4294967295, 1, 4294967296)
  , ("add-2^32-plus-2^32", "add", 4294967296, 4294967296, 8589934592)
  , ("add-2^63-plus-2^63", "add", 9223372036854775808, 9223372036854775808, 18446744073709551616)
  , ("sub-zero", "sub", 0, 0, 0)
  , ("sub-underflow-small", "sub", 3, 5, 0)
  , ("sub-small", "sub", 5, 3, 2)
  , ("sub-2^32-minus-1", "sub", 4294967296, 1, 4294967295)
  , ("sub-underflow-big", "sub", 0, 9223372036854775808, 0)
  , ("mul-zero", "mul", 0, 5, 0)
  , ("mul-small", "mul", 6, 7, 42)
  , ("mul-2^32-1-times-2", "mul", 4294967295, 2, 8589934590)
  , ("mul-2^32-times-2^32", "mul", 4294967296, 4294967296, 18446744073709551616)
  , ("mul-5-times-2^63", "mul", 5, 9223372036854775808, 46116860184273879040)
  , ("div-small", "div", 7, 2, 3)
  , ("div-by-zero", "div", 5, 0, 0)
  , ("div-2^32-by-2", "div", 4294967296, 2, 2147483648)
  , ("div-2^63-by-2^32", "div", 9223372036854775808, 4294967296, 2147483648)
  , ("div-zero-by-5", "div", 0, 5, 0)
  , ("mod-small", "mod", 7, 2, 1)
  , ("mod-by-zero", "mod", 5, 0, 5)
  , ("mod-2^32-by-7", "mod", 4294967296, 7, 4)
  , ("mod-2^63-by-prime", "mod", 9223372036854775808, 1000000007, 291172004)
  , ("mod-zero-by-5", "mod", 0, 5, 0)
  , ("pow-small", "pow", 2, 10, 1024)
  , ("pow-small2", "pow", 3, 5, 243)
  , ("pow-2-exp40", "pow", 2, 40, 1099511627776)
  , ("pow-2-exp64", "pow", 2, 64, 18446744073709551616)
  , ("pow-zero-zero", "pow", 0, 0, 1)
  , ("pow-base-zero-exp", "pow", 5, 0, 1)
  , ("pow-zero-base", "pow", 0, 5, 0)
  , ("land-nibble", "land", 255, 15, 15)
  , ("land-2^32-1-self", "land", 4294967295, 4294967295, 4294967295)
  , ("land-2^32-and-1", "land", 4294967296, 1, 0)
  , ("land-zero", "land", 0, 123456789, 0)
  , ("land-2^63-1-and-2^63", "land", 9223372036854775807, 9223372036854775808, 0)
  , ("lor-nibble", "lor", 240, 15, 255)
  , ("lor-with-zero", "lor", 4294967295, 0, 4294967295)
  , ("lor-2^32-and-2^32-1", "lor", 4294967296, 4294967295, 8589934591)
  , ("lor-zero-zero", "lor", 0, 0, 0)
  , ("xor-self", "xor", 255, 255, 0)
  , ("xor-2^32-1-xor-1", "xor", 4294967295, 1, 4294967294)
  , ("xor-self-big", "xor", 4294967296, 4294967296, 0)
  , ("xor-small", "xor", 5, 3, 6)
  , ("shl-1-by-40", "shiftLeft", 1, 40, 1099511627776)
  , ("shl-1-by-64", "shiftLeft", 1, 64, 18446744073709551616)
  , ("shl-1-by-100", "shiftLeft", 1, 100, 1267650600228229401496703205376)
  , ("shl-zero", "shiftLeft", 0, 1000, 0)
  , ("shl-small", "shiftLeft", 5, 10, 5120)
  , ("shr-2^64-by-64", "shiftRight", 18446744073709551616, 64, 1)
  , ("shr-2^40-by-40", "shiftRight", 1099511627776, 40, 1)
  , ("shr-by-zero", "shiftRight", 1, 0, 1)
  , ("shr-zero-shifted", "shiftRight", 0, 100, 0)
  , ("shr-small", "shiftRight", 5, 1, 2)
  ]

def arithUniverseNat (mod : Name) : MetaM (Array Finding × Nat × Nat × Nat × Nat) := do
  let mut out := #[]
  let mut tried := 0
  let mut agreed := 0
  let mut disagreed := 0
  let mut capped := 0
  for (label, op, a, b, expected) in natCases do
    tried := tried + 1
    let opExpr := mkApp2 (mkConst (natOpConst op)) (Expr.lit (.natVal a)) (Expr.lit (.natVal b))
    let expectedExpr := Expr.lit (.natVal expected)
    let caseDetail := s!"`{a} {op} {b} = {expected}`"
    let verdict ← arithUniverseGuard do
      let stmt ← mkEq opExpr expectedExpr
      decideOne stmt
    match verdict with
    | some (some true) => agreed := agreed + 1
    | some (some false) =>
      disagreed := disagreed + 1
      let detail := s!"Nat case `{label}`: {caseDetail} does NOT decide to true: the kernel's native {op} disagrees with " ++
        s!"the expected value computed independently in Python (a kernel/native-op mismatch)"
      out := out.push { check := "arithUniverse", severity := "fail", module := mod, name := Name.mkSimple label, detail }
    | some none =>
      capped := capped + 1
      let detail := s!"Nat case `{label}`: {caseDetail} has no synthesizable Decidable instance or did not reduce to a " ++
        s!"Bool within the cap (not a disagreement)"
      out := out.push { check := "arithUniverse", severity := "info", module := mod, name := Name.mkSimple label, detail }
    | none =>
      capped := capped + 1
      let detail := s!"Nat case `{label}`: {caseDetail} hit the heartbeat cap before deciding (a resource cap, not a " ++
        s!"disagreement)"
      out := out.push { check := "arithUniverse", severity := "info", module := mod, name := Name.mkSimple label, detail }
  return (out, tried, agreed, disagreed, capped)

/-! ## entry point -/

def arithUniverse (c : Ctx) : MetaM (Array Finding) := do
  let mod := c.mods.headD .anonymous
  let (levelFindings, lTried, lAgreed, lDisagreed, lCapped) ← arithUniverseLevels mod
  let (natFindings, nTried, nAgreed, nDisagreed, nCapped) ← arithUniverseNat mod
  let detail := s!"universe: {lTried} pairs tried, {lAgreed} agree, {lDisagreed} disagree (fail), {lCapped} capped; " ++
    s!"nat-arith: {nTried} triples tried, {nAgreed} agree, {nDisagreed} disagree (fail), {nCapped} capped"
  let summary : Finding := { check := "arithUniverse", severity := "info", module := mod, name := .anonymous, detail }
  return levelFindings ++ natFindings ++ #[summary]

end Jinshi
