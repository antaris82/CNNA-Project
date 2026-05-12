# Strengthening Phase S9b Audit

## Scope of this patch

This patch hardens the first S9 module named explicitly in the plan: `Finite/StateSpace.lean`.
It does **not** yet claim closure of the full S9 ladder. Instead it closes the public state-space
surface to the extent required by S9b and propagates the resulting naming/normalization discipline
into the already-open mirror consumers.

## What changed

### `Finite/StateSpace.lean`

The operative public surface is now explicit and proof-carrying on the `ExecComplex` strand:

- `execDensityOperator`
- `execTrace`
- `execIsTraceOne`
- `execTraceNormalize`
- `execPureStateVector` / `execBasisStateVector`
- `execPureProjector` / `execBasisProjector`

with accompanying closure lemmas for basis vectors, Hermiticity of executable projectors,
trace-one for executable projectors, and normalization of the executable pure projector.

The mirrored `ℂ` side is named explicitly as mirror-only surface:

- `mirrorState`, `mirrorObservable`, `mirrorDensityOperator`
- `mirrorStateContract`, `mirrorObservableContract`
- `mirrorGenerator`, `mirrorInner`, `mirrorStateNormSq`
- `mirrorTrace`, `mirrorIsTraceOne`, `mirrorTraceNormalize`
- `mirrorIsPositive`, `mirrorPositiveCone`
- `mirrorPureStateVector`, `mirrorPureProjector`

### Removal of the public zero-fallback

The old public normalization shape

`if Z = 0 then ρ else Z⁻¹ • ρ`

has been removed. Both operative and mirror normalization now require an explicit nonzero witness.
This is the central semantic change of S9b: normalization is no longer allowed to hide a silent
public fallback branch.

### Downstream compatibility adjustments

To keep the already-green S9 scaffold aligned with the sharpened state-space semantics:

- `Finite/GibbsStateSeed.lean` now takes an explicit nonzero witness for `mirrorGibbsState`
- `Finite/MatrixExponential.lean` consumes `mirrorGenerator`
- `Finite/DynamicsAdapter.lean` and `Finite/ChannelSeed.lean` now speak explicitly of
  `mirrorState`, `mirrorObservable` and `mirrorDensityOperator`

## What S9b still does not close

This patch does **not** yet:

- replace the analytic matrix exponential by a finite executable approximation surface,
- construct the operative Gibbs path,
- prove nonzeroness of the Gibbs partition function,
- sharpen Schrödinger/Heisenberg propagation semantics,
- or add Kraus/Choi/CPTP structure.

Those remain the explicit follow-up tasks for S9c and later S9x phases.


## S9b rest closure in this follow-up patch

The remaining projector-side witness obligations inside `Finite/StateSpace.lean` are now
made explicit rather than left implicit in later consumers:

- `execPureStateVector_ne_zero` and `mirrorPureStateVector_ne_zero`
- `execPureProjector_apply_same` and `mirrorPureProjector_apply_same`
- `execPureProjector_ne_zero` and `mirrorPureProjector_ne_zero`
- `execPureProjector_trace_ne_zero` and `mirrorPureProjector_trace_ne_zero`
- `mirrorPureProjector_traceNormalize`

This matters for the exact S9b requirement that the old public zero-fallback is not merely
removed syntactically, but replaced by proof-carrying nonzero data for the relevant projector
case. The Gibbs nonzero question remains open on purpose and is deferred to later S9 phases.
