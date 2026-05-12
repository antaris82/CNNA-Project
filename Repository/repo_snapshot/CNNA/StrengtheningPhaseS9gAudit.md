# Strengthening Phase S9g Audit

## Scope

Phase S9g hardens `CNNA/PillarA/Finite/ChannelSeed.lean` from a thin package shell into an explicit
finite algebraic channel pre-surface over the operative `ExecComplex` strand.

## Files touched

- `CNNA/PillarA/Finite/ChannelSeed.lean`
- `CNNA/PillarA/Finite/Notation.lean`
- `CNNA/PillarA/Notation.lean`

## What was added

### 1. Explicit Kraus surface

`ChannelSeedStrong` now carries an explicit nested `KrausFamily` structure with:

- finite Kraus index type,
- executable Kraus operators,
- Schrödinger-side Kraus action,
- Heisenberg-side Kraus action,
- identity family,
- single-Kraus family,
- composed Kraus family.

This moves the channel seed away from a mere wrapper around `DynamicsAdapterStrong`.

### 2. Explicit unitary single-Kraus seed

`UnitarySingleKrausSeed` packages the algebraic special case of a single executable channel operator
with both-sided inverse laws:

- `star operator * operator = 1`
- `operator * star operator = 1`

From this seed the file now derives:

- an explicit single-Kraus family,
- Schrödinger/Heisenberg actions,
- identification with the Kraus actions,
- a trace-preservation theorem on the executable side.

### 3. Algebraic channel package

`AlgebraicChannelPackage` now exposes the S9g public attachment points:

- `schrodinger`
- `heisenberg`
- `krausFamily`
- `choiMatrix`
- `isTracePreserving`
- `isPositive`
- `isCompletelyPositive`
- `isCPTP`

The package is buildable from either a raw Kraus family or a unitary single-Kraus seed.

### 4. Explicit theorem surface required by the plan

The following named theorems were added on the operative side:

- identity laws:
  - `identity_schrodinger`
  - `identity_heisenberg`
  - `identity_isTracePreserving`
- zero-time laws:
  - `zeroTime_schrodinger`
  - `zeroTime_heisenberg`
  - `zeroTime_isTracePreserving`
- unitary single-Kraus trace preservation:
  - `unitarySingleKraus_isTracePreserving`
- composition laws:
  - `comp_schrodinger`
  - `comp_heisenberg`
  - `comp_zeroTime_left_schrodinger`
  - `comp_zeroTime_right_schrodinger`
  - `comp_zeroTime_left_heisenberg`
  - `comp_zeroTime_right_heisenberg`

This is the proof-carrying closure target of S9g itself. Full audit closure of remaining S9 issues is
reserved for S9h.

### 5. Mirror isolation preserved

The analytic `ℂ` side remains explicitly isolated under the `mirror*` names:

- `MirrorAlgebraicChannelPackage`
- `mirrorSchrodingerChannel`
- `mirrorHeisenbergChannel`
- `mirrorChannelPackage`
- `mirrorChannelCompose`

So the file does not introduce a second operative generator path.

### 6. Notation integration

The notation layers now expose the new public channel objects:

- `FiniteKrausFamily`
- `FiniteUnitarySingleKrausSeed`
- `FiniteAlgebraicChannelPackage`

## What S9g does **not** claim

This phase does not yet claim:

- full OQS semantics,
- Lindblad closure,
- semigroup closure beyond the finite algebraic composition surface,
- complete proof that every operative channel package constructed downstream is CPTP,
- global S9 audit closure.

Those questions remain for later phases, especially S9h and later pillar consumers.

## Rule-discipline check

Intended discipline of this patch:

- no new top-level bridge path,
- no new public mirror generator,
- notation consumed on the public active path,
- finite executable surface stays explicit,
- channel semantics remain pre-OQS and algebraic,
- the channel layer consumes `DynamicsAdapterStrong` rather than rebuilding dynamics from scratch.

## Important limitation

This audit text records the intended S9g implementation delta. In the current workspace the Lean
toolchain (`lake`, `lean`, pinned mathlib checkout) is not present, so this phase could not be build-
verified here. The code changes are therefore a best-effort source patch against the uploaded green
S9f snapshot, not a confirmed green S9g build.
