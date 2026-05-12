# Strengthening Phase SM1R Audit

Status: generated regular/variable provenance layer for the reset AR12a-SMOKE path.

Implemented files:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedMainPath.lean`
- Updated import surfaces:
  - `CNNA/PillarA/Arithmetic/BuildAll.lean`
  - `CNNA/PillarA/Arithmetic/Notation.lean`

SM1R scope:

- Introduces `GeneratedMainPath` over a generated `SubstrateClass` carrier.
- Provides `regularGeneratedMainPath` for `ConcreteSubstrate.RegularCell b`.
- Provides `variableGeneratedMainPath` for `LevelVariableSubstrate.LevelVariableCell β`.
- Provides `RegularVariableGeneratedPathPair` with `sameGeneratedToCPipeline` and `noArithmeticSpecialVariation` witnesses.
- Provides `policyProvenanceHook` and `weightProvenanceHook` as proof-carrying provenance hooks, not as numeric oracle data.
- Provides explicit `noCutSpecCarrierClaim` and `noMatrixDataYet` theorems.
- Provides `SM1RGeneratedVariationLedger` as the post-SM1R ledger surface.
- Exposes SM1R names in `Arithmetic/Notation.lean` under `StrengtheningSM1R`.

Discipline:

- SM1R does not import `CutSpec`, `BoundaryPorts`, matrix modules, Dirichlet, DtN, MultiSchur, Charpoly, discriminant, CM, or target-anchor modules.
- SM1R does not construct matrix data, Dirichlet data, interior blocks, inverses, DtN data, generalized DtN data, MultiSchur data, characteristic polynomials, discriminants, CM data, or L2/L3 anchor data.
- The regular and variable sides are both generated-main-path consumers of the same `generatedBranchFamily`/`generatedBranchToC` construction pattern.
- The variable path is explicitly ledgered as not being an arithmetic special variation.
- Policy and weight hooks are intentionally deferred to later entrywise phases; they are not free weights and cannot justify an SM3 formula without entry lemmas.

Negative/discipline checks on the newly added Lean file:

- no `sorry`
- no `admit`
- no new `axiom`
- no `noncomputable`
- no `classical`
- no `@[simp]`
- no `CutSpec.full`
- no matrix, determinant, inverse, Dirichlet, DtN, MultiSchur, charpoly, CM, or discriminant object introduced in SM1R

Tool limitation:

- Lean/lake is not available in this execution container; the build must be validated locally by the user.
