# Strengthening Phase SM3db5R Audit

SM3db5R implements the positive matrix-export layer after SM3db4aR.

## Added Lean module

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorInverseCandidateMatrix.lean`

## Added core objects

- `inverseCandidateMatrix_from_accumulatedEntry`
- `GeneratedInteriorInverseCandidateMatrix`
- `inverseCandidateMatrix_from_inverseCandidateEntry`
- `inverseCandidateMatrix_from_eliminationTrace`
- `inverseCandidateMatrix_entry_eq_accumulatedEntry`
- `inverseCandidateMatrix_entry_eq_inverseCandidateEntry`
- `inverseCandidate_profile_eq_SM3cR_SM3dR_source`
- `noTwoSidedInv_for_SM3dbR`
- `noInteriorEliminationCertificate_for_SM3dbR`
- `noInteriorEliminationData_for_SM3dbR`
- `SM3db5RGeneratedInteriorInverseCandidateMatrixLedger`

## Discipline checks

- The exported matrix is entrywise `SM3db4aR` accumulated-entry data.
- No new candidate-entry formula is introduced.
- No free matrix table is introduced.
- No `Matrix.inv` is introduced.
- No two-sided inverse proof is introduced.
- No `InteriorEliminationCertificate` or `InteriorEliminationData` is introduced.
- No DtN, GeneralizedDtN, MultiSchur, charpoly, factor, discriminant, L=2, or L=3 target data is introduced.
- The next gate is recorded as SM3db6R shape/source separation.

## Local build status

Not run here. ChatGPT cannot execute Lean in this environment; the user performs the authoritative local `lake build`.
