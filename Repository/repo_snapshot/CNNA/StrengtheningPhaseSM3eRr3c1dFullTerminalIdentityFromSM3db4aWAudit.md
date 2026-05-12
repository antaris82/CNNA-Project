# Strengthening Phase SM3eR-r3c1d-full — TerminalIdentity from SM3db4aW

## Phase classification

H-phase: adapter/export from the SM3db4aW terminal coverage export into the existing r3c1d TerminalIdentity interface.

## Implemented file

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull.lean`

## Positive payload

- `terminalIdentityR3c1d_from_SM3db4aWExport`
- `regularTerminalIdentityR3c1dFromSM3db4aWExport`
- `variableTerminalIdentityR3c1dFromSM3db4aWExport`
- `regularTerminalIdentityR3c1dFromSM3db4aWSource`
- `variableTerminalIdentityR3c1dFromSM3db4aWSource`
- `terminalIdentityLedgerR3c1dFromSM3db4aW`
- `SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger`
- `sm3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger`

## Source discipline

The phase consumes the SM3db4aW-exported `regularTerminalCoverageSource` and `variableTerminalCoverageSource` and applies the already existing `SM3eRr3c1dTerminalIdentityLedger.fromRegularAndVariableTerminalCoverage` constructor.

## No-output gates

This phase does not construct:

- `GeneratedInteriorAccumulatedEntryCancellationInvariant`
- `GeneratedInteriorSM3db7RProductCancellationLedger`
- `ProductIdentityProof`
- `TwoSidedInv`
- `InteriorEliminationData`
- DtN, GeneralizedDtN, MultiSchur, Charpoly, factor or discriminant data

## Import discipline

No new mathlib import was introduced. The new file imports only the immediate W-export module.
