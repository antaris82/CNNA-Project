# Strengthening Phase S9 Audit

## Scope of this patch

This patch opens the S9 finite post-spectral seed block that the plan places immediately after the
closed S8 algebraic spectral root.

The patch adds the six new finite modules named in the plan:

- `CNNA/PillarA/Finite/StateSpace.lean`
- `CNNA/PillarA/Finite/MatrixExponential.lean`
- `CNNA/PillarA/Finite/GibbsStateSeed.lean`
- `CNNA/PillarA/Finite/UnitaryEvolution.lean`
- `CNNA/PillarA/Finite/DynamicsAdapter.lean`
- `CNNA/PillarA/Finite/ChannelSeed.lean`

and wires them into:

- `CNNA/PillarA/Finite/BuildAll.lean`
- `CNNA/PillarA/Finite/Notation.lean`
- `CNNA/PillarA/Notation.lean`

## What is added

### 1. `Finite/StateSpace.lean`

- first S9 consumer of `Finite/SpectralBridge`
- explicit finite state / observable / density carriers
- canonical state- and observable-contract surfaces
- trace and trace-normalization helpers
- explicit positive-cone predicate on the mirrored complex side
- canonical pure basis vector / projector surface

### 2. `Finite/MatrixExponential.lean`

- explicit local analytic island over the mirrored complex matrix side
- `NormedSpace.exp`-based matrix exponential surface
- scaled generator, finite evolution, and thermal exponential seeds
- zero-time normalization theorems

### 3. `Finite/GibbsStateSeed.lean`

- eigenvalue-based Gibbs-weight surface over the S8 mirror
- diagonal thermal seed in the eigenbasis
- unnormalized Gibbs operator in the original basis via the unitary eigenbasis matrix
- partition-function and trace-normalized Gibbs candidate surface
- explicit separation between thermal candidate and later physical interpretation

### 4. `Finite/UnitaryEvolution.lean`

- finite skew-generator shell using `- i t H`
- forward / backward propagator seeds
- explicit Heisenberg and Schrödinger conjugation shells
- zero-time identities

### 5. `Finite/DynamicsAdapter.lean`

- state-vector, density-operator and observable-side action maps
- bundled `StarAlgDynamicsSeed` pre-surface
- zero-time identities for all three action sides

### 6. `Finite/ChannelSeed.lean`

- explicit algebraic channel package carrying Schrödinger and Heisenberg maps
- channel composition shell
- zero-time channel identities

## Deliberate restriction

This patch is intentionally a first S9 opening, not a claim that the entire S9 gate is already closed.
In particular it does **not** yet prove:

- full finite positivity/completeness theorems for the entire density cone,
- CPTP / Kraus / Choi theorems,
- KMS statements,
- Lindbladian generators,
- or any spectral-regime recovery claim beyond the already closed S8 algebraic root.

The matrix-exponential and Gibbs/unitary layers are therefore exposed as explicit finite seed surfaces,
with their local analytic dependence visible in code instead of being hidden behind a fake computable
wrapper.

## Architectural consequence

The finite side now has an explicit post-spectral ladder:

`SpectralBridge -> StateSpace -> MatrixExponential -> {GibbsStateSeed, UnitaryEvolution} -> DynamicsAdapter -> ChannelSeed`

This means later pillars no longer need to start from raw finite matrices when they want finite state,
thermal, dynamical or basic channel seeds. The S9 block can now be sharpened phasewise instead of
being reconstructed ad hoc downstream.
