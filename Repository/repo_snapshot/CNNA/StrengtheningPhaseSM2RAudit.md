# Strengthening Phase SM2R Audit

## Scope

SM2R adds the generated finite approximant core for the AR12a-SMOKE reset path after SM1R.

## Added Lean module

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedApproximantCore.lean`

## Positive outputs

- `Smoke.GeneratedApproximantStrong`
- `Smoke.regularGeneratedApproximantStrong`
- `Smoke.variableGeneratedApproximantStrong`
- `Smoke.GeneratedTruncationWitness`
- `Smoke.GeneratedFiniteCarrierAPI`
- `Smoke.SM2RGeneratedApproximantLedger`

## Provenance checks represented in code

- route is `generatedToCSubstrate`
- approximant is the SM1R main path approximant
- approximant equals the generated main path truncation at `p.L_max`
- cutoff is controlled by `p.L_max`
- carrier inside cutoff is derived from the SM1R main path carrier
- carrier inside cutoff is `Finset.univ`
- carrier above cutoff is empty
- `Fintype`, `DecidableEq`, and membership decidability are forwarded from `SubstrateClass`

## Negative fences represented in code

- no BoundaryPorts in the SM2R core
- no CutSpec in the SM2R core
- no matrix data
- no Dirichlet data
- no DtN data
- no discriminant or L2/L3 target data

## Import discipline

The SM2R core imports only:

```lean
import CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath
```

Thus it stays below `CNNA.PillarA.Finite.Approximant`, `BoundaryPorts`, `CutSpec`, `DirichletLaplacian`, `DtN`, `Coupling`, and matrix-specific modules.

## Local build note

No Lean executable is available in this environment. The file was prepared for the user's local `lake build` check.
