# SM3eRq GeneratedInverseCandidateExecEntrySource Audit

Status: implemented as the positive source/bridge layer after SM3bq and SM3dbRToSM3eRHandoff.

Implemented file:
- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInverseCandidateExecEntrySourceSM3eRq.lean`

BuildAll insertion:
- after `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- before `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`

Derived-only source path:
- `generatedInteriorBlockEntryExecSM3eRq` reuses the SM3bq Dirichlet Exec matrix restricted to interior indices.
- The four accumulated-entry components are exposed operationally via block-derived Exec entries:
  - pivot contribution,
  - local-step contribution,
  - residual contribution,
  - fold-update-order contribution.
- `generatedInverseCandidateEntryExecSM3eRq` and `generatedInverseCandidateMatrixExecSM3eRq` are entrywise from those component sources.

Bridge obligations exposed:
- candidate entry Exec to `generatedInteriorAccumulatedEntryValue T i j`.
- candidate matrix Exec to `generatedInteriorAccumulatedEntryValue T i j`.
- candidate matrix Exec to `H.candidateMatrix i j`.
- candidate matrix Exec to `M.matrix i j`.

Plan boundary preserved:
- no `@[simp]` attribute added.
- no `noncomputable` added.
- no `classical` added.
- no scalar inverse, no `Matrix.inv`, no `field_simp`, no `mul_inv_cancel`.
- no product proof, no `TwoSidedInv`, no `InteriorEliminationCertificate`, no boundary Schur operator, no DtN/MultiSchur, no charpoly/discriminant/Heegner data.

Static limitation:
- Lean was not executed in this environment; local build verification remains with the user.
