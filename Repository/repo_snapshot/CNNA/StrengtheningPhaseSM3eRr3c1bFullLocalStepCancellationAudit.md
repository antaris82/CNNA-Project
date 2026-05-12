# Strengthening Phase SM3eR-r3c1b-full Audit: LocalStepCancellation

## Status

Implemented as a local Smoke layer after `SM3eR-r3c1b1`.

## Added Lean module

`CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorLocalStepCancellationR3c1bFull.lean`

The module imports only:

`CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`

No new mathlib import is introduced in this phase.

## Positive payload

The phase introduces:

- `GeneratedInteriorLocalStepCancellationR3c1bFull`
- `GeneratedInteriorLocalStepCancellationR3c1bFull.fromBridge`
- `GeneratedInteriorLocalStepCancellationR3c1bFull.fromOperationalDegreeReciprocalSource`
- left and right residual-zero accessors
- left and right bridge-equals-kernel accessors
- left and right local-step cancellation accessors
- regular and variable abbreviations/constructors
- `SM3eRr3c1bFullLocalStepCancellationLedger`

The construction consumes a proof-carrying `GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1` witness. It does not rebuild the r3c1b1 bridge inside the core constructor.

## Derived-only source chain

The local cancellation is obtained from the r3c1b1 bridge fields:

- `leftLocalSchurResidual_eq_zero_from_SM3db2aR`
- `rightLocalSchurResidual_eq_zero_from_SM3db2aR`
- `leftKernelLocalSchurResidualBridge_eq_kernel`
- `rightKernelLocalSchurResidualBridge_eq_kernel`

The subtraction-form local cancellation fields are then closed by explicit `calc` proofs using the bridge equality and `sub_self`.

## Explicit non-outputs

The phase carries status fields preventing accidental escalation:

- no fold induction
- no terminal coverage/identity gate
- no ProductIdentityProof
- no TwoSidedInv
- no InteriorEliminationData
- no DtN/GeneralizedDtN/MultiSchur data
- no charpoly/factor/discriminant/L2-L3 arithmetic target

## Next phase

`SM3eR-r3c1c` is marked as next only as a FoldInvariance phase. This audit does not mark r3c1d, r3c1e, r3c2, r4, r5, or SM3fR as active.

## Constraint check

- no `@[simp]`
- no `noncomputable`
- no `classical`
- no `Matrix.inv`
- no scalar inverse construction
- no `mul_inv_cancel`
- no `field_simp`
- no global simplification surface
- no large index eliminator
- no new free cancellation fields in the exported constructor
