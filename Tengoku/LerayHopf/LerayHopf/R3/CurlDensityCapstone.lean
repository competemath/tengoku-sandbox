import Tengoku.LerayHopf.LerayHopf.R3.SchwartzDivFreeBasis
import Tengoku.LerayHopf.LerayHopf.R3.CurlDensity

/-!
# LerayHopf.R3.CurlDensityCapstone — retire `curlSchwartzDense_holds` (issue #3 / #21)

This file performs the acyclic wiring that removes the project axiom
`curlSchwartzDense_holds` from `exists_lerayHopf_r3`.  It contains NO new
mathematics: the Helmholtz/Weyl curl-density on ℝ³ is already proved
(`curlSchwartzDense_provedRoute`, sorry-free and axiom-free) in
`LerayHopf/R3/CurlDensity.lean`.  Here we only re-anchor the two downstream consumers
(`nonempty_schwartzGalerkinBasis`, `r3GalerkinScheme_exists`) to the proved theorem
instead of the axiom, and provide `curlSchwartzDense_holds` as a proved `theorem`
(rather than an `axiom`) so that all downstream names remain unchanged.

## DAG position (why this file exists)

```
GalerkinScheme.lean       (SchwartzGalerkinBasis, nonempty_r3GalerkinScheme_of_basis)
  └── SchwartzDivFreeBasis.lean   (CurlSchwartzDense def, curlSchwartz, curlSchwartzL2,
  │                                schwartzGalerkinBasis_of_curlDense C1)
  └── CurlDensity.lean    (imports SchwartzDivFreeBasis; proved curlSchwartzDense_provedRoute)
        └── CurlDensityCapstone.lean   [THIS FILE]
              (imports BOTH; re-anchors C2 / r3GalerkinScheme_exists to the proved route)
                    └── GalerkinODECapstone.lean (imports this file for nonempty_schwartzGalerkinBasis)
```

`CurlDensity.lean` imports `SchwartzDivFreeBasis.lean`, so a direct definition of
`nonempty_schwartzGalerkinBasis` or `r3GalerkinScheme_exists` in `CurlDensity.lean`
would redefine imported names — forbidden in Lean.  And `SchwartzDivFreeBasis.lean`
cannot import `CurlDensity.lean` (that would be a cycle).  The correct acyclic fix is
this file: it sits strictly DOWNSTREAM of both, sees both the proved route
(`curlSchwartzDense_provedRoute`) and the conditional deliverable C1
(`schwartzGalerkinBasis_of_curlDense`), and replaces the axiom with a proved `theorem`.

## Declarations

- `curlSchwartzDense_holds`        : THEOREM (was `axiom` in SchwartzDivFreeBasis.lean)
                                     `:= curlSchwartzDense_provedRoute`  (issue #21 / #3)
- `nonempty_schwartzGalerkinBasis` : THEOREM — C1 applied to the proved density (issue #21)
- `r3GalerkinScheme_exists`        : THEOREM — discharged former AX-G (unchanged body)

## Assumptions

No `axiom`, `opaque`, `constant`, or `unsafe` in this file.
All three declarations are proved theorems, sorry-free and axiom-free.
-/

namespace LerayHopf

/-- **The Helmholtz/Weyl curl-density, now a THEOREM (issue #3 / #21).**

Formerly `axiom curlSchwartzDense_holds : CurlSchwartzDense` in
`SchwartzDivFreeBasis.lean`, this is now proved via `curlSchwartzDense_provedRoute`
(the complete Fourier / Plancherel proof in `CurlDensity.lean`).

Named `curlSchwartzDense_holds` (same as the former axiom) so that downstream
consumers (`nonempty_schwartzGalerkinBasis`, `GalerkinODECapstone`, etc.) see no
name change.  The `axiom` form was removed from `SchwartzDivFreeBasis.lean` as part
of this restructure; `#print axioms exists_lerayHopf_r3` no longer lists
`LerayHopf.curlSchwartzDense_holds` after this wiring. -/
theorem curlSchwartzDense_holds : CurlSchwartzDense :=
  curlSchwartzDense_provedRoute

/-- **C2 (discharged via the proved density, issue #21 / #3).**  Unconditional
inhabitation of the Schwartz divergence-free basis.

Previously this theorem lived in `SchwartzDivFreeBasis.lean` and consumed the axiom
`curlSchwartzDense_holds`; it is now relocated here, below the proved route, so the
body is identical but the dependency on the axiom is replaced by a dependency on the
proved theorem `curlSchwartzDense_holds` (above).

The name is preserved so every downstream consumer (`GalerkinODECapstone.lean`) is
unchanged. -/
theorem nonempty_schwartzGalerkinBasis : Nonempty SchwartzGalerkinBasis :=
  schwartzGalerkinBasis_of_curlDense curlSchwartzDense_holds

/-- **Discharged former axiom AX-G (relocated from SchwartzDivFreeBasis.lean, issue #3).**

A Galerkin approximation-projection family on `L²_σ(ℝ³)` exists.  No longer an axiom
(was discharged in issue #21 by routing through `curlSchwartzDense_holds`); now
additionally axiom-free because `curlSchwartzDense_holds` is itself a proved theorem.

Body is unchanged: assembled from `nonempty_r3GalerkinScheme_of_basis` applied to a
basis `B` from `nonempty_schwartzGalerkinBasis`.  The name is preserved so every
downstream consumer is unchanged. -/
theorem r3GalerkinScheme_exists : Nonempty R3GalerkinScheme :=
  (nonempty_schwartzGalerkinBasis).elim fun B => nonempty_r3GalerkinScheme_of_basis B

end LerayHopf
