# Strengthening Phase SM3eR Re-Run Audit

Status: SM3eR-r3c patch prepared after the green SM3eR-r3b cancellation-surface build.

Updated Lean modules:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTraceCancellationDerivation.lean`
- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`

Previously implemented r0-r3b obligations remain present:

- product entries are defined only from `H.candidateMatrix`
- no use of `candidateMatrix_from_candidateEntry E` in the Re-Run module
- separate left and right product entries remain:
  - `generatedInteriorBlock W * H.candidateMatrix`
  - `H.candidateMatrix * generatedInteriorBlock W`
- r3a normal forms still expand the products entrywise into finite sums over `GeneratedInteriorIndex A`
- r3b still exposes the six cancellation fields only through `GeneratedInteriorSM3db7RTraceCancellationInvariant` and `GeneratedInteriorSM3db7RProductCancellationLedger`
- `provenTwoSidedInvFromSM3db7R` is still only available from a proof-carrying `GeneratedInteriorSM3db7RProductIdentityProof`

Implemented r3c obligations:

- new source status:
  - `SM3eRr3cTraceCancellationSourceStatus`
- new derivation status:
  - `SM3eRr3cTraceCancellationDerivationStatus`
- new ledger status:
  - `SM3eRr3cTraceCancellationDerivationLedgerStatus`
- new r4 gate status:
  - `SM3eRr3cR4GateStatus`
- new source object:
  - `GeneratedInteriorSM3db7RTraceCancellationSource`
- new derivation object:
  - `GeneratedInteriorSM3db7RTraceCancellationDerivation`
- new r3c ledger object:
  - `SM3eRr3cTraceCancellationDerivationLedger`
- source constructor from the existing SM3db7R handoff:
  - `GeneratedInteriorSM3db7RTraceCancellationSource.fromSM3dbChain`
- invariant constructor from the r3c derivation:
  - `traceCancellationInvariant_from_SM3dbChain`
- normal-form cancellation projections:
  - `leftNormalFormCancellation_from_traceDerivation`
  - `rightNormalFormCancellation_from_traceDerivation`
- product-cancellation ledger constructor:
  - `productCancellationLedger_from_traceCancellationDerivation`
- r3c ledger constructor:
  - `SM3eRr3cTraceCancellationDerivationLedger.fromTraceCancellationDerivation`
- regular/variable source constructors:
  - `regularTraceCancellationSource_from_SM3dbChain`
  - `variableTraceCancellationSource_from_SM3dbChain`
- regular/variable invariant constructors from derivation witnesses:
  - `regularTraceCancellationInvariant_from_SM3dbChain`
  - `variableTraceCancellationInvariant_from_SM3dbChain`

Provenance threaded in the r3c source:

- SM3cR InteriorBlock profile via `GeneratedInteriorBlockStructureProfile.fromEntryLemmas W`
- SM3db2R local-step status via `T.localStepOf i`
- SM3db2R row/column residual provenance via the trace fields
- SM3db3R trace source and finite termination status via `T.sourceStatus_eq` and `T.terminationStatus_eq`
- SM3db4aR accumulated-entry source via `H.accumulatedSourceStatus_eq_SM3db4aR`
- SM3db5R matrix-export source via `H.sourceStatus_eq_SM3db5R`
- SM3db6R shape/source separation via `H.shapeSeparationStatus_eq_SM3db6R` and `H.sourceSeparationStatus_eq_SM3db6R`
- SM3db7R consumption gate via `H.consumptionGateStatus_eq`
- handoff matrix entries via `H.candidateMatrixEntry_eq_accumulatedTraceValue`
- r3a left/right product normal forms via `generatedInteriorSM3db7RLeftProductEntry_eq_sum_accumulated` and `generatedInteriorSM3db7RRightProductEntry_eq_sum_accumulated`

Mathematical boundary of this r3c patch:

- r3c now separates the source/provenance layer from the cancellation derivation layer.
- The source layer is unconditionally constructed from the existing SM3db7R handoff.
- The cancellation invariant is constructed only from a proof-carrying `GeneratedInteriorSM3db7RTraceCancellationDerivation`.
- The derivation object still requires the six normal-form cancellation proofs as data; this avoids pretending that the current accumulated-entry formula automatically proves the identity equations.
- No `GeneratedInteriorSM3db7RProductIdentityProof` is constructed by r3c.
- No `TwoSidedInv` is constructed by r3c.
- No `InteriorEliminationCertificate` is constructed by r3c.
- No `InteriorEliminationData` is constructed by r3c.
- No DtN/GeneralizedDtN/MultiSchur data is introduced by r3c.
- No charpoly/factor/discriminant target data is introduced by r3c.
- No new candidate-entry formula, free entry table, free matrix, `Matrix.inv`, SM3daR fallback, or external inverse oracle is introduced.

Important precision point:

This patch implements the r3c handoff/derivation architecture positively and makes the r4 input discipline explicit: r4 may consume the unconditional `ProductCancellationLedger` only after a proof-carrying r3c derivation exists. Because Lean was not executed here, the user's local build remains the source of truth. If the build is green but the six normal-form proofs cannot be inhabited from the present SM3db2R--SM3db4aR definitions, the plan-prescribed next step is the minimal upstream strengthening phase (`SM3db4bR`, `SM3db3aR`, or `SM3db2aR`), not a patch inside r4/r5.

Forbidden patterns checked textually in the new r3c module:

- no `@[simp]`
- no `noncomputable`
- no `classical`
- no `Matrix.inv`
- no `candidateMatrix_from_candidateEntry`
- no direct SM3daR candidate-matrix fallback
- no positive `InteriorEliminationCertificate` construction
- no positive `InteriorEliminationData` construction

Lean was not executed in this environment; the local build remains the source of truth.
