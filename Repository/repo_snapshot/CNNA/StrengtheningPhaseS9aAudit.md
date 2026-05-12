# Strengthening Phase S9a Audit

## Scope of this patch

This S9a patch does **not** yet claim closure of the finite state / exponential / Gibbs /
dynamics / channel block. Instead it performs the first hardening step required by the plan:
the already green S9 scaffold is classified file- and definition-sharply into

- public operative `ExecComplex` surface,
- public mirror / bridge audit surface over `ℂ`,
- and purely internal helper material.

The patch keeps the existing green ladder

`StateSpace -> MatrixExponential -> {GibbsStateSeed, UnitaryEvolution} -> DynamicsAdapter -> ChannelSeed`

but makes the mirror status of the still-open analytic layer explicit in code via explicit public `mirror*` names.

## Code-side consequence

### `Finite/StateSpace.lean`

- operative public surface kept explicit:
  - `execState`, `execObservable`
  - `execStateContract`, `execObservableContract`
  - `execGenerator`, `execInner`, `execStateNormSq`
- mirror public audit surface now named explicitly:
  - `mirrorTrace`, `mirrorTraceNormalize`
  - `mirrorIsPositive`, `mirrorPositiveCone`
  - `mirrorPureStateVector`, `mirrorPureProjector`
- no new hidden fallback path is introduced

### `Finite/MatrixExponential.lean`

- the current `NormedSpace.exp`-based layer remains mirror-only
- explicit mirror audit names added:
  - `mirrorExp`, `mirrorGeneratorExp`
  - `mirrorScaledGenerator`, `mirrorEvolutionAt`, `mirrorThermalAt`
- the operative generator is still upstream in the closed S8 `ExecComplex` path

### `Finite/GibbsStateSeed.lean`

- every currently noncomputable public thermal object is now mirrored explicitly:
  - `mirrorGibbsWeight`, `mirrorGibbsDiagonal`
  - `mirrorDiagonalPartitionFunction`
  - `mirrorEigenvectorUnitaryMatrix`
  - `mirrorGibbsUnnormalized`, `mirrorPartitionFunction`, `mirrorGibbsState`
  - `mirrorThermalCandidate`
- no claim is made yet that a public operative Gibbs surface already exists

### `Finite/UnitaryEvolution.lean`

- the propagator / conjugation layer is classified as mirror-only in the current S9a state
- explicit mirror names added:
  - `mirrorSkewGenerator`, `mirrorBackwardSkewGenerator`
  - `mirrorPropagator`, `mirrorInversePropagator`
  - `mirrorHeisenbergConjugation`, `mirrorSchrodingerConjugation`

### `Finite/DynamicsAdapter.lean`

- the current state / density / observable action maps are classified as mirror consumers
- explicit mirror names added:
  - `mirrorSchrodingerState`, `mirrorSchrodingerDensity`, `mirrorHeisenbergObservable`
  - `mirrorStarAlgDynamicsSeed`

### `Finite/ChannelSeed.lean`

- the current packaged channels remain mirror-side algebraic seeds
- explicit mirror names added:
  - `mirrorSchrodingerChannel`, `mirrorHeisenbergChannel`
  - `mirrorChannelPackage`, `mirrorChannelCompose`

## Residual whitelist ledger after this patch

The six S9 files still carry the same 28 public `noncomputable def` as open S9x work items.
This is deliberate: S9a is a classification-and-audit phase, not yet the elimination phase.
After this patch they are semantically named and auditable instead of being mixed into an implicitly public surface.

Current residual public `noncomputable def` by file:

- `Finite/StateSpace.lean`: 2
  - `mirrorTrace`, `mirrorTraceNormalize`
- `Finite/MatrixExponential.lean`: 4
  - `mirrorExp`, `mirrorGeneratorExp`, `mirrorEvolutionAt`, `mirrorThermalAt`
- `Finite/GibbsStateSeed.lean`: 8
  - `mirrorGibbsWeight`, `mirrorGibbsDiagonal`, `mirrorDiagonalPartitionFunction`,
    `mirrorEigenvectorUnitaryMatrix`, `mirrorGibbsUnnormalized`, `mirrorPartitionFunction`,
    `mirrorGibbsState`, `mirrorThermalCandidate`
- `Finite/UnitaryEvolution.lean`: 6
  - `mirrorSkewGenerator`, `mirrorBackwardSkewGenerator`, `mirrorPropagator`,
    `mirrorInversePropagator`, `mirrorHeisenbergConjugation`, `mirrorSchrodingerConjugation`
- `Finite/DynamicsAdapter.lean`: 4
  - `mirrorSchrodingerState`, `mirrorSchrodingerDensity`, `mirrorHeisenbergObservable`,
    `mirrorStarAlgDynamicsSeed`
- `Finite/ChannelSeed.lean`: 4
  - `mirrorSchrodingerChannel`, `mirrorHeisenbergChannel`, `mirrorChannelPackage`,
    `mirrorChannelCompose`

All of these residual public `noncomputable def` belong, after the present S9a classification, to the
mirror / bridge audit surface. None of them is to be read as a second operative generator path.

## What S9a still does **not** close

This patch does **not** yet:

- eliminate the public `noncomputable` residue,
- replace `NormedSpace.exp` by a public finite computable approximation surface,
- remove the `if Z = 0 then ... else ...` normalization fallback,
- prove nonzero partition-function facts for the relevant Gibbs/projector cases,
- repair the later channel/CPTP/Kraus/Choi semantics,
- or settle the Heisenberg-/Schrödinger-side refinement work.

Those remain explicit follow-up targets for S9b and the later S9x phases.
