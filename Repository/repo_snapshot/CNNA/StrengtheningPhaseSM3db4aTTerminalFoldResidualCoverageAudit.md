# SM3db4aT TerminalFoldResidualCoverage Audit

Status: implemented as a positive terminal SM3db4aR fold/residual exposure and exact missing-source audit.

Implemented Lean module:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT.lean`

Core outputs:

- `GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT`
- `SM3db4aTTerminalFoldResidualCoverageLedger`
- regular/variable abbreviations and constructors

Formal role:

- Consumes the SM3db3aR `GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR`.
- Re-exposes the terminal fold state as the SM3db4aR `GeneratedInteriorAccumulatedEntryFold` already carried by r3c1c.
- Re-exposes terminal residual and fold/update-order contributions from the SM3db4aR accumulated fold layer.
- Binds the fold source to `SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps`.
- Binds the trace/pivot side to `SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps`.
- Audits that the current SM3db4aR API still does not expose the left/right terminal identity fields required to construct the unconditional r3c1d `TerminalCoverageSource`.
- Marks the next positive sharpening as `sm3db4aUExposeTerminalFoldResidualIdentityFields`.

Negative gates kept closed:

- no `GeneratedInteriorAccumulatedEntryCancellationInvariant`
- no `ProductIdentityProof`
- no `TwoSidedInv`
- no `InteriorEliminationData`
- no DtN/GeneralizedDtN/MultiSchur data
- no Charpoly/Factor/Discriminant target data
- no `Matrix.inv`, no scalar inverse construction, no free matrix/table/oracle

Plan consequence:

SM3db4aT closes the local terminal fold/residual audit branch, but it does not yet free `SM3eR-r3c1d-full`, `SM3eR-r3c1e`, r3c2, r4, r5, or SM3fR. A further SM3db4aR-near source phase must expose the actual terminal left/right identity fields before r3c1d can export the unconditional terminal coverage source.
