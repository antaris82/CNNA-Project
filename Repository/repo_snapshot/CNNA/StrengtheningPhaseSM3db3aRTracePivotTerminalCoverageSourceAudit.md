# SM3db3aR TracePivotTerminalCoverageSource Audit

Status: implemented as a positive trace/pivot coverage exposure and exact terminal-coverage audit.

Implemented Lean module:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR.lean`

Core outputs:

- `GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`
- `GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR`
- `GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR`
- `SM3db3aRTracePivotTerminalCoverageSourceLedger`
- regular/variable abbreviations and constructors

Formal role:

- Exposes per-index trace/pivot/local-step coverage from `GeneratedInteriorEliminationTrace`.
- Binds coverage to `SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps`.
- Reuses the existing `SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps` carried by the r3c1c block-fold invariance.
- Does not construct the unconditional r3c1d terminal coverage source, because terminal fold/residual identity is still not exposed by the existing SM3db4aR API.
- Marks the next positive sharpening as `SM3db4aTTerminalFoldResidualCoverage`.

Negative gates kept closed:

- no `GeneratedInteriorAccumulatedEntryCancellationInvariant`
- no `ProductIdentityProof`
- no `TwoSidedInv`
- no `InteriorEliminationData`
- no DtN/GeneralizedDtN/MultiSchur data
- no Charpoly/Factor/Discriminant target data
- no `Matrix.inv`, no scalar inverse construction, no free matrix/table/oracle
