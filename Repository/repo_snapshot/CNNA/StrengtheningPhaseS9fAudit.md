# Strengthening Phase S9f Audit

## Scope of this patch

This patch hardens `Finite/DynamicsAdapter.lean` from a thin mirror-side wrapper into an
operative, proof-carrying S9f pre-surface over the executable `ExecComplex` strand.
It does **not** yet claim closure of the channel side (`S9g` / `S9h`), but it does close the
adapter-local requirements stated for S9f:

- state-, density- and observable-side dynamics are exposed on the same operative axis,
- the common propagator / inverse-propagator provenance is explicit,
- null-time laws are available on the operative surface,
- composition laws are pulled through on the operative surface,
- and an explicit `StarAlgDynamicsSeed` package is exported and wired into the notation spine.

## Code-side consequence

### `Finite/DynamicsAdapter.lean`

The file now exports a genuinely operative adapter layer:

- operative carrier aliases:
  - `execState`
  - `execObservable`
  - `execDensityOperator`
  - `execStateContract`
  - `execObservableContract`
- operative action maps:
  - `schrodingerState`
  - `schrodingerDensity`
  - `heisenbergObservable`
- proof-carrying package:
  - `StarAlgDynamicsSeed`
  - `starAlgDynamicsSeed`
- explicit operative theorems:
  - `schrodingerState_zero`
  - `schrodingerDensity_zero`
  - `heisenbergObservable_zero`
  - `schrodingerState_comp`
  - `schrodingerDensity_comp`
  - `heisenbergObservable_comp`
- explicit star / adjoint-form transport on the operative matrix side:
  - `schrodingerDensity_star`
  - `heisenbergObservable_star`

The mirror-side analytic surface is kept, but remains clearly named and isolated via the
existing `mirror*` definitions.

### Notation wiring

The new packaged dynamics surface is wired into both notation spines via

- `FiniteStarAlgDynamicsSeed` in `Finite/Notation.lean`
- `FiniteStarAlgDynamicsSeed` in `PillarA/Notation.lean`

so the S9f object is not merely local helper structure but a consumable public seed.

## Architectural effect

The adapter is no longer just a pass-through from `UnitaryEvolutionStrong` to later channel code.
Instead it is now the first place where the executable finite dynamics package is bundled with its
state and algebra contracts. This keeps S9f local to the adapter boundary and avoids pushing this
proof-carrying glue either backward into `UnitaryEvolution` or forward into `ChannelSeed`.

## What S9f still does **not** close

This patch does **not** yet:

- introduce Kraus / Choi / CPTP channel semantics,
- prove a full unitary or *-automorphism statement for the finite approximation path,
- or close the remaining channel-level seed obligations.

Those remain the explicit targets of `S9g` and `S9h`.
