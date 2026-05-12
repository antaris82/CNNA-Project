# SM3db4aU TerminalFoldResidualIdentityFields Audit

Status: implemented as a positive SM3db4aT consumer and exact missing-source audit for the terminal identity fields.

Implemented Lean module:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU.lean`

Adjusted consumer module:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldTerminalIdentityR3c1d.lean`

Core outputs:

- `GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU`
- `GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU`
- `SM3db4aUTerminalFoldResidualIdentityFieldsLedger`
- regular/variable abbreviations and constructors
- r3c1d adapter `GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d.fromSM3db4aUTerminalIdentityFieldCertificate`

Formal role:

- Consumes the SM3db4aT `GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT` rather than duplicating its terminal fold/residual exposure.
- Rebinds the terminal fold state, terminal residual contribution, terminal fold/update-order contribution, r3c1c invariance, and SM3db3aR trace/pivot coverage to their existing proof-carrying sources.
- Audits the precise current gap: the current SM3db4aR/SM3db4aT API exposes terminal fold/residual/fold-order data, but not the six left/right terminal identity fields required by r3c1d.
- Separates the missing-source audit from a conditional identity-field certificate. The certificate is only a bridge once the six identity proofs have been supplied by a later derived source.
- Provides the r3c1d-compatible adapter only for the certificate, not for the missing-source audit.

Required missing fields for the next positive source phase:

- `leftBlockFold_eq_identity`
- `rightBlockFold_eq_identity`
- `leftBlockFold_diagonal`
- `leftBlockFold_offdiag`
- `rightBlockFold_diagonal`
- `rightBlockFold_offdiag`

Negative gates kept closed:

- no `GeneratedInteriorAccumulatedEntryCancellationInvariant`
- no `ProductIdentityProof`
- no `TwoSidedInv`
- no `InteriorEliminationData`
- no DtN/GeneralizedDtN/MultiSchur data
- no Charpoly/Factor/Discriminant target data
- no `Matrix.inv`, no scalar inverse construction, no free matrix/table/oracle

Plan consequence:

SM3db4aU is audit-closed if the local build is green, but it does not release unconditional `SM3eR-r3c1d-full`. The next positive source phase must derive the terminal left/right identity equations from the terminal fold/residual/fold-order layer, or expose an even narrower missing definition at the SM3db4aR boundary.
