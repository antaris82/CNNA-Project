# SM3db2bR Per-Pivot Regularity Audit

Basis: green `SM3db2aR` patch.

Implemented module:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR.lean`

Updated modules:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR.lean`
- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`

## Phase meaning

`SM3db2bR` is not a matrix inverse, not a product identity phase, and not an r3c1b-full proof. It opens the exact per-pivot regularity gate between the relative `SM3db2aR` local Schur invariant and the later `SM3eR-r3c1b1` BlockFold-kernel bridge.

## Positive content

The new file proves the available trace-level pivot-entry provenance:

- every trace pivot entry is the corresponding generated interior block diagonal entry;
- every such diagonal entry is the generated Dirichlet degree entry;
- every trace pivot entry is identified as the regularity target for a later scale witness;
- if a proof-carrying `pivotScale` witness is supplied for every trace pivot, together with left/right scale equations, then it gives a `GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR` for every pivot;
- from those regularity witnesses it constructs `GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR`.

Important correction: the operational path does not define `pivotScale := pivotEntry⁻¹` over `ℝ`. Real scalar inversion has no executable code in Lean, so a nonzero witness alone is not enough for this computable phase.

## Remaining gate

The current code still does not prove an unconditional executable scale witness

```lean
∀ pivot,
  Σ scale : ℝ,
    scale * (T.localStepOf pivot).stepUpdate.pivotEntry = 1 ∧
    (T.localStepOf pivot).stepUpdate.pivotEntry * scale = 1
```

from the generated degree/adjoining-provenance alone. The new requirement object makes this explicit and routes the next phase to a degree/scale-witness proof if this is not already available.

## Forbidden data not introduced

The patch introduces no `Matrix.inv`, no scalar `⁻¹`, no free matrix inverse, no `TwoSidedInv`, no `ProductIdentityProof`, no `InteriorEliminationData`, no DtN/GeneralizedDtN/MultiSchur data, and no arithmetic target data.
