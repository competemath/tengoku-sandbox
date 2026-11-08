# How Tengoku stays reliable

Tengoku documents the checks used to assess its library for automated theorem proving. The checks are designed to be
exceptionally cynical of all dependencies, even the Lean 4 kernel and elaboration ecosystem. These are the methods;
[why we do it](why-cynical.md) has the case studies behind them.

## The methods

- **Two kernels.** Lean's kernel is the program that checks proofs. Every day the whole compiled library is exported and
  checked again by [nanoda](https://github.com/ammkrn/nanoda_lib), an independent kernel that shares no code with Lean
  ([independent-check.yml](../.github/workflows/independent-check.yml)). A bug in Lean's kernel would have to fool both.
- **Translations are checked.** A translated statement is accepted only once the kernel has verified that it implies
  the original. That gate is part of
  [Emissary](https://github.com/competemath/emissary-archangel), the translation factory.
- **Almost no axioms.** A trusted theorem may rest only on Lean's three standard axioms; `sorry` and `native_decide`
  are refused ([axiom_scan.py](../scripts/ci/axiom_scan.py)).
- **No vacuous theorems.** A theorem whose assumptions contradict each other proves nothing. The gate searches for
  these ([vacuity.py](../scripts/ci/vacuity.py)), and a theorem it flags needs an explicit acknowledgement.
- **Code cannot be run in the environment.** A record cannot carry `#eval`, `unsafe`, `initialize` or a new `axiom`
  ([the lint](bundle-lint.md)).
- **Nothing is trusted for where it came from.** Every theorem records its source, licence, credit and tier, and
  `trusted` means the tree builds with it and it passes the checks above.
- **Every change is gated.** A change is a pull request, checked, then built by a merge queue against the whole
  compiled library ([how a theorem gets in](how-a-pr-flows.md)). The checks are public and anyone can re-run them.
