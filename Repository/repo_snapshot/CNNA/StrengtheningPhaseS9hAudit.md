# Strengthening Phase S9h Audit

## Scope

Phase S9h closes the full S9 ladder

- `CNNA/PillarA/Finite/StateSpace.lean`
- `CNNA/PillarA/Finite/MatrixExponential.lean`
- `CNNA/PillarA/Finite/GibbsStateSeed.lean`
- `CNNA/PillarA/Finite/UnitaryEvolution.lean`
- `CNNA/PillarA/Finite/DynamicsAdapter.lean`
- `CNNA/PillarA/Finite/ChannelSeed.lean`
- `CNNA/PillarA/Finite/BuildAll.lean`
- `CNNA/PillarA/Finite/Notation.lean`
- `CNNA/PillarA/Notation.lean`

under the S9h closure criterion from the current plan: operative S9 surface computable, mirror islands
explicit and local, no new `classical` residue, no blanket `@[simp]` surface, no return to a public
`NormedSpace.exp` path, no public Gibbs dependence on mirror eigen-decomposition, and a real
Kraus/Choi/CPTP attachment surface on `ChannelSeed`. The plan states that only at this point may
S9 be marked closed. See the S9h row and the S9x closure table in the uploaded plan PDF. fileciteturn3file0

## Code delta in this patch

### 1. Code-primacy cleanup on the active S9 path

The six active S9 Lean modules were stripped of in-code explanatory doc comments so that the checked
Lean source remains the only repo-internal truth source and prose stays external. This follows the
plan's code-primacy / documentation-separation rule already recorded in the uploaded plan. fileciteturn2file0

### 2. Notation completion on the public S9 surface

Both notation layers now expose the operative Gibbs witness type as
`FiniteGibbsApproxPartitionWitness`, so the witness-based executable Gibbs normalization surface is
not hidden behind raw nested names.

Touched files:

- `CNNA/PillarA/Finite/Notation.lean`
- `CNNA/PillarA/Notation.lean`

## Grep-style audit summary

### Import chain

The active S9 dependency chain remains forward-only:

- `StateSpace -> SpectralBridge`
- `MatrixExponential -> StateSpace`
- `GibbsStateSeed -> MatrixExponential`
- `UnitaryEvolution -> MatrixExponential`
- `DynamicsAdapter -> UnitaryEvolution`
- `ChannelSeed -> DynamicsAdapter`

This matches the intended ladder

`StateSpace -> MatrixExponential -> {GibbsStateSeed, UnitaryEvolution} -> DynamicsAdapter -> ChannelSeed`

recorded in the plan's S9 progression note. fileciteturn3file1

### `noncomputable def`

Across the six S9 modules there remain 28 public `noncomputable def`, but in the current source all
of them are explicitly mirror-side and named under `mirror*` prefixes:

- `StateSpace`: 2
- `MatrixExponential`: 4
- `GibbsStateSeed`: 8
- `UnitaryEvolution`: 6
- `DynamicsAdapter`: 4
- `ChannelSeed`: 4

This matches the S9h closure requirement that mirror islands remain local and explicit rather than
feeding the operative generator surface. The operative exported path itself is computable.

### `classical` / `@[simp]`

Within these six S9 modules the current source grep is:

- `classical`: 0 hits
- `@[simp]`: 0 hits

So the S9 block does not currently reopen blanket simp surfaces or explicit classical shortcuts.

### Matrix exponential path

`NormedSpace.exp` still occurs only inside the explicit mirror island of
`Finite/MatrixExponential.lean`; the operative public path is carried by

- `scaledGeneratorApprox`
- `expApproxTerm`
- `expApprox`
- `evolutionApproxAt`
- `thermalApproxAt`
- `weightedThermalApproxAt`

which is exactly the S9c/S9h requirement from the plan. fileciteturn3file2turn3file4

### Gibbs path

Public executable Gibbs data are carried by

- `gibbsApproxUnnormalizedAt`
- `weightedGibbsApproxUnnormalized`
- `gibbsApproxUnnormalized`
- `gibbsApproxPartitionFunctionAt`
- `weightedGibbsApproxPartitionFunction`
- `gibbsApproxPartitionFunction`
- `GibbsApproxPartitionWitness`
- `gibbsApproxState`

The mirror eigenvalue / eigenvector path remains explicitly segregated under `mirror*` names, so the
operative Gibbs surface no longer depends publicly on the mirror eigen-decomposition. This is the
exact S9d/S9h criterion from the plan. fileciteturn3file4

### Dynamics / channel path

`UnitaryEvolution` already separates Schrödinger and Heisenberg by the propagator / inverse-propagator
pair, `DynamicsAdapter` binds state / density / observable motion over the same approximation axis,
and `ChannelSeed` exports the explicit algebraic package with

- `krausFamily`
- `choiMatrix`
- `isTracePreserving`
- `isPositive`
- `isCompletelyPositive`
- `isCPTP`

plus the unitary single-Kraus seed and identity / zero-time / composition theorems. That is the S9g
surface which S9h audits as the closed channel basis. fileciteturn3file4

## What this patch does not overclaim

This patch is an S9h source-level closure pass and audit artifact. It does **not** claim:

- a verified local `lake build`, because the uploaded workspace snapshot does not include the full
  Lean toolchain / pinned mathlib checkout;
- later OQS, Lindblad, KMS or semigroup closure beyond the finite algebraic S9 seed surface;
- any extension of S8 into Kesten-McKay, RG, gap-as-mass or other regime-recovery claims.

The latter is explicitly forbidden by the current plan text. fileciteturn3file1

## Deliverable status

This patch is the best-effort S9h implementation possible on the uploaded source snapshot:

- active S9 code comments removed from the six S9 modules,
- operative Gibbs witness notation exposed in both notation layers,
- explicit S9h audit record added.

A green build still needs to be checked inside the real pinned repo/toolchain environment.
