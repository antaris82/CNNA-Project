# Strengthening Phase S9d Audit

## Scope of this patch

This patch hardens `Finite/GibbsStateSeed.lean` at the exact point named by S9d in the plan.
It does **not** yet close unitary, dynamical, or channel semantics. Instead it moves the public
Gibbs seed off the analytic spectral mirror and onto the already-closed S9 ladder

`StateSpace -> MatrixExponential -> GibbsStateSeed`

by consuming the executable approximation surface introduced in S9c.

## What changed

### `Finite/GibbsStateSeed.lean`

The operative public Gibbs surface is now explicit on the `ExecComplex` strand:

- `execDensityOperator`
- `weightPolicy`, `thermalAxis`
- `gibbsApproxUnnormalizedAt`
- `weightedGibbsApproxUnnormalized`
- `gibbsApproxUnnormalized`
- `gibbsApproxPartitionFunctionAt`
- `weightedGibbsApproxPartitionFunction`
- `gibbsApproxPartitionFunction`
- `GibbsApproxPartitionWitness`
- `gibbsApproxState`

with direct closure lemmas tying the default public Gibbs approximation back to
`MatrixExponential.defaultThermalApproxAt` and `StateSpace.execTraceNormalize`.

### Thermal provenance

The public default Gibbs approximation is no longer opened through mirror eigenvalues.
It is now visibly tied back to the already-carried foundational thermal data:

- `gibbsApproxUnnormalizedAt` consumes a `ThermalAxis`
- `weightedGibbsApproxUnnormalized` consumes a `WeightPolicy`
- `gibbsApproxUnnormalized` closes the loop back to the policy already carried by the upstream
  S9 path

This is the S9d requirement that the standard thermal surface be rebound to `WeightPolicy.thermal`
instead of silently reusing the analytic mirror.

### Explicit nonzero witness instead of public fallback

The operative approximate Gibbs state does **not** hide a zero-branch. Instead it requires an
explicit witness

- `GibbsApproxPartitionWitness`

containing

- a rational scalar value,
- a proof that the executable approximate partition trace equals that rational scalar,
- and a proof that the scalar is nonzero.

So the current S9d closure chooses the plan-allowed route

> theorematic nonzeroness proof **or** explicit required witness

and exposes the witness openly until a stronger general nonzeroness theorem is available.

### Mirror isolation remains explicit

The mirror-side Gibbs constructions remain present only as explicitly named analysis / bridge
surface:

- `mirrorGibbsWeight`, `mirrorGibbsDiagonal`
- `mirrorDiagonalPartitionFunction`
- `mirrorEigenvectorUnitaryMatrix`
- `mirrorGibbsUnnormalized`, `mirrorPartitionFunction`, `mirrorGibbsState`
- `mirrorThermalCandidate`

The important change is that the **public default Gibbs path no longer needs them**.

## What S9d still does not close

This patch does **not** yet:

- prove a general theorematic nonzeroness result for the approximate Gibbs partition function,
- sharpen Schrödinger vs. Heisenberg propagation laws,
- add proof-carrying dynamics semantics,
- or add Kraus / Choi / CPTP channel structure.

Those remain the explicit targets of S9e-S9g.
