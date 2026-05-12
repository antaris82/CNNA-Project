# Strengthening Phase SM0 Audit

Status: implementation scaffold for AR12a-SMOKE reset, built from the AR12a baseline.

Implemented files:

- `CNNA/PillarA/ToC/GeneratedBranchFamily.lean`
- `CNNA/PillarA/Arithmetic/Smoke/GeneratedSource.lean`
- Updated import surfaces:
  - `CNNA/PillarA/ToC/BuildAll.lean`
  - `CNNA/PillarA/Arithmetic/BuildAll.lean`
  - `CNNA/PillarA/Arithmetic/Notation.lean`

SM0 scope:

- Establishes the generated full-level carrier `generatedBranchFamily Cell` as a `DirectedFamily`.
- Provides regular and level-variable generated carriers via `RegularCell b` and `LevelVariableCell β`.
- Provides theorem-level carrier equalities to `Finset.univ`.
- Provides non-singleton witnesses at successor levels under the genuine branching assumptions `0 < b` and `0 < β L`.
- Exposes a Smoke ledger that records:
  - AR12a-baseline scaffold status,
  - no `CutSpec.full` import in the Smoke core,
  - carrier origin from the `SubstrateClass` level carrier,
  - no matrix data before SM3 entry lemmas,
  - no positive import continuity from old SM1--SM3d.

Negative/discipline checks on the newly added files:

- no `sorry`
- no `admit`
- no new `axiom`
- no `noncomputable`
- no `classical`
- no `@[simp]`
- no `CutSpec.full`
- no matrix, determinant, inverse, Dirichlet, DtN, or discriminant object introduced in SM0

Tool limitation:

- Lean/lake is not available in this execution container; the build must be validated locally by the user.

## Patch SM0.1

The first SM0 archive accidentally declared witness-valued constructions as `theorem`.
Lean requires theorem declarations to have a `Prop` target.  The non-singleton witnesses
are data, not propositions, so the four affected declarations are now `def`:

- `regularGeneratedFamily_nonSingletonAtSucc`
- `variableGeneratedFamily_nonSingletonAtSucc`
- `regularGeneratedSmokeCarrier_nonSingletonAtSucc`
- `variableGeneratedSmokeCarrier_nonSingletonAtSucc`

No mathematical content was weakened.  The witness structure remains proof-carrying:
`left`, `right`, membership in the full generated carrier, and `left ≠ right`.
