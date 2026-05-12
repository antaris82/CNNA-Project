# SM3eR-r3c1b1 Audit: BlockFoldKernel-to-LocalSchurResidualBridge

## Implemented files

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1.lean`
- `CNNA/PillarA/Arithmetic/BuildAll.lean`

## Scope

`SM3eR-r3c1b1` is implemented as the local bridge from the `r3c1a` block-fold kernels to the `SM3db2aR` local Schur residual layer, with the per-pivot scale witness exported through `SM3db2fR`.

The phase consumes:

- `GeneratedInteriorBlockFoldNormalFormR3c1a`
- `GeneratedOperationalDegreeReciprocalSourceSM3db2fR`
- `GeneratedInteriorTracePivotScaleWitnessSM3db2bR`
- `GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`
- `GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR`

## Guarantees

The bridge records left and right kernel-source equations against `generatedInteriorLeftBlockFoldKernel` and `generatedInteriorRightBlockFoldKernel`, and left and right local Schur residual equations through the `SM3db2aR` trace-local invariant.

The bridge proves that adding the local Schur residual to a left or right kernel entry leaves that kernel entry unchanged. This is a local residual-neutrality bridge only; it is not a block-fold identity, not a fold induction, and not a terminal identity proof.

## Explicit non-goals

The phase introduces no new scale, no new reciprocal datum, no `Matrix.inv`, no `ProductIdentityProof`, no `TwoSidedInv`, no `InteriorEliminationData`, no DtN/GeneralizedDtN/MultiSchur data, and no charpoly/factor/discriminant target.

## Next phase

The next unlocked phase is `SM3eR-r3c1b-full`, which may consume this bridge to prove the local step-cancellation layer. `SM3eR-r3c1c`, `r3c1d`, `r3c1e`, unconditional `r3c2`, `r4`, `r5`, and `SM3fR` remain blocked.
