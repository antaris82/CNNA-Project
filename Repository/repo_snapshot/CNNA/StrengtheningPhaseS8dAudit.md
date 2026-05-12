# Strengthening Phase S8d Audit

## Scope of this patch

This S8d patch strengthens `CNNA/PillarA/Finite/SpectralBridge.lean`
as the explicit one-way bridge between

- the public executable `ExecComplex` spectral strand in
  `CNNA/PillarA/Finite/SpectralDecomposition.lean`, and
- the analytic `ℂ`-mirror strand in
  `CNNA/PillarA/Finite/SpectralDecompositionC.lean`.

The bridge does not create a second generator surface. It exposes only
explicit transfer statements and proof-carrying certificates.

## What is added on the bridge strand

- bridge-side transferred shadows
  - `execTrace` / `complexTrace`
  - `execDeterminant` / `complexDeterminant`
  - `execCharDetEval` / `complexCharDetEval`
  - `complexCharDetMatrix`
- bridge-side controlled coordinate / projector shadows
  - `complexCoordinateSpectralValue`
  - `complexCoordinateProjector`
  - `complexCoordinateProjectorSelfCommutator`
- explicit transfer theorems
  - matrix identification
  - Hermiticity transfer
  - Frobenius / shift transfer
  - trace transfer
  - determinant transfer
  - characteristic-determinant evaluation transfer
  - coordinate-value transfer
  - coordinate-projector Hermiticity / self-commutator transfer
- proof-carrying bridge certificates
  - `SpectralShadowBridgeCertificate`
  - `CoordinateProjectorBridgeCertificate`
- reference / variation constructors in `StrengtheningS8d`

## Deliberate restriction

This patch does **not** expose the analytic `ℂ`-mirror as a directly consumable
production API.

In particular, later consumers still have to enter the mirror only through the
bridge theorems and certificates. No downstream module should import the mirror
strand as a silent replacement for the executable public surface.

## Immediate architectural consequence

The S8d bridge now carries the first explicit theorematic identification that
both strands concern the same A-generated Dirichlet operator. This closes the
first transfer layer requested by the plan without pretending that the general
computable Hermitian spectral package of S8e/S8f is already available.
