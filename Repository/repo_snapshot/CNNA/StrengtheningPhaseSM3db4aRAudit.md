# Strengthening Phase SM3db4aR Audit

## Scope

SM3db4aR inserts the positive accumulated TraceEvaluation / AccumulatedEntryFold layer after the green-but-partial SM3db4R shell and before any SM3db5R matrix export.

## Added Lean module

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorAccumulatedTraceEvaluation.lean`

## Build integration

- `CNNA/PillarA/Arithmetic/BuildAll.lean` imports the new module before `Notation`.
- `CNNA/PillarA/Arithmetic/Notation.lean` imports the new module and exposes the `StrengtheningSM3db4aR` aliases and main constructors.

## Plan-point checklist

- `GeneratedInteriorAccumulatedTraceEvaluation`: added.
- `GeneratedInteriorAccumulatedEntryFold`: added.
- `accumulatedEntry_from_eliminationTrace`: added.
- `accumulatedEntry_uses_pivotData`: added.
- `accumulatedEntry_uses_localSteps`: added.
- `accumulatedEntry_uses_residualData`: added.
- `accumulatedEntry_respects_foldUpdateOrder`: added.
- `inverseCandidateEntry_source_is_accumulatedTraceEvaluation`: added.
- `sm3db4R_not_only_localResidualWrapper`: added as explicit structural status ledger.
- `noFreeEntryTable_for_accumulatedEntryFold`: added.
- `noExternalInverseOracle_for_accumulatedEntryFold`: added.

## Negative boundaries retained

SM3db4aR does not introduce:

- `Matrix.inv`
- matrix export
- left/right product proof
- `TwoSidedInv`
- `InteriorEliminationCertificate`
- `InteriorEliminationData`
- DtN / GeneralizedDtN / MultiSchur data
- charpoly, factorization, discriminant, L=2/L=3 target data
- operative `noncomputable`
- `classical`
- global `@[simp]`

## Technical caveat

This phase gives a structural accumulated-entry layer. It records that the candidate entry is built from pivot contribution, local step contribution, residual contribution, and fold/update-order contribution, rather than directly exposing the old local row-residual projection. It is still not a two-sided inverse and must not be consumed as such. SM3db5R may only export this accumulated candidate entry as a matrix; SM3eR remains the first phase allowed to attempt product validation.
