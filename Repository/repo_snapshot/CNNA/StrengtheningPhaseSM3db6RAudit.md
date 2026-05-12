# Strengthening Phase SM3db6R Audit

SM3db6R implements the positive shape/source-separation layer after the green SM3db5R matrix export.

## Added Lean module

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorInverseCandidateShapeSeparation.lean`

## Added core objects

- `GeneratedInteriorInverseCandidateShapeSeparation`
- `inverseCandidateShapeSeparation_from_matrix`
- `inverseCandidateEntry_not_SM3daR_candidateEntry`
- `inverseCandidateEntry_not_interiorBlock_or_involutiveBlockProof`
- `inverseCandidateMatrix_not_interiorBlock_or_involutiveBlockProof`
- `inverseCandidateMatrix_not_only_localResidualWrapper`
- `inverseCandidateMatrix_entry_eq_accumulatedTraceValue_afterShapeSeparation`
- `SM3dbRShapeSeparationLedger`
- `sm3dbRShapeSeparationLedger`

## Build integration

- `CNNA/PillarA/Arithmetic/BuildAll.lean` imports the new module after SM3db5R.
- `CNNA/PillarA/Arithmetic/Notation.lean` imports the new module and exposes the `StrengtheningSM3db6R` aliases and main constructors.

## Plan-point checklist

- The shape gate consumes the already constructed SM3db5R matrix.
- The matrix is still traced entrywise to SM3db4aR `generatedInteriorAccumulatedEntryValue`.
- The gate records that the source is SM3db4aR accumulated-entry data, not a fresh free table.
- The gate records no SM3daR CandidateEntry fallback.
- The gate records no InteriorBlock fallback without a later involutive-block proof gate.
- The old SM3db4R local-residual-only wrapper is kept excluded via the SM3db4aR accumulated-entry status.
- No product validation is introduced.
- No `Matrix.inv` is introduced.
- No `TwoSidedInv`, `InteriorEliminationCertificate`, or `InteriorEliminationData` is introduced.
- No DtN, GeneralizedDtN, MultiSchur, charpoly, factor, discriminant, L=2, or L=3 target data is introduced.
- The next gate is recorded as SM3db7R handoff after shape separation.

## Local build status

Not run here. ChatGPT cannot execute Lean in this environment; the user performs the authoritative local `lake build`.
