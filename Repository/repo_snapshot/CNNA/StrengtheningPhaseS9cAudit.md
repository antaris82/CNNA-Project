# Strengthening Phase S9c Audit

## Scope of this patch

This patch hardens `Finite/MatrixExponential.lean` exactly at the point named by S9c in the plan.
It does **not** yet close Gibbs, dynamical, or channel semantics. Instead it removes the public
operative dependence on the analytic placeholder surface `NormedSpace.exp` and replaces it by an
explicit finite computable approximation ladder on the `ExecComplex` strand.

## What changed

### `Finite/MatrixExponential.lean`

The operative public surface is now explicitly approximation-based:

- `execGenerator`
- `weightPolicy`, `thermalAxis`, `thermalBetaQ`
- `scaledGeneratorApprox`
- `expApproxTerm`
- `expApprox`
- `evolutionApproxAt`
- `thermalApproxAt`
- `weightedThermalApproxAt`
- `defaultThermalApproxAt`

This means the public product path no longer exports `NormedSpace.exp` as its operative exponential.
Instead, finite partial sums over the executable matrix strand are the visible operative interface.

The analytic complex exponential remains only as explicitly named mirror surface:

- `mirrorExp`
- `mirrorGeneratorExp`
- `mirrorScaledGenerator`
- `mirrorEvolutionAt`
- `mirrorThermalAt`

### Thermal provenance

The operative thermal path is now visibly tied to the existing foundational thermal data:

- `thermalApproxAt` consumes a `ThermalAxis`
- `weightedThermalApproxAt` consumes a `WeightPolicy`
- `defaultThermalApproxAt` closes the loop back to the policy already carried by the upstream
  Dirichlet / spectral path

This makes the rational `β`-dependence explicit on the operative side instead of reopening a naked
real-parameter generator surface.

### Direct downstream semantic cleanup

`Finite/UnitaryEvolution.lean` now refers explicitly to `mirrorGenerator` rather than the previously
ambiguous `generator` name from `MatrixExponentialStrong`. This keeps the analytic unitary layer
visibly on the mirror side while the operative approximation ladder stays separate.

## What S9c still does not close

This patch does **not** yet:

- construct the operative Gibbs state,
- prove nonzeroness of the Gibbs partition function,
- sharpen Schrödinger vs. Heisenberg propagation laws,
- or add Kraus / Choi / CPTP structure.

Those remain the explicit follow-up targets of S9d–S9g.
