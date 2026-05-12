# Strengthening Phase S8b Audit

## Scope of this patch

This S8b patch strengthens `CNNA/PillarA/Finite/SpectralDecomposition.lean`
on the public executable `ExecComplex` strand without introducing any public
`noncomputable def`.

## What is added on the executable public strand

- `spectralTrace`
- `spectralDeterminant`
- `spectralCharDetMatrix`
- `spectralCharDetEval`
- `SpectralShadow` / `spectralShadow`
- `SpectralCertificate` / `spectralCertificate`
- `coordinateSpectralValue`
- `coordinateSpectralResidual`
- `CoordinateSpectralCandidate` / `coordinateSpectralCandidate`
- `coordinateProjector`
- `coordinateProjector_isHermitian`
- `coordinateProjector_selfCommutator_zero`
- `CoordinateProjectorCertificate` / `coordinateProjectorCertificate`

## Deliberate restriction

This patch does **not** expose mathlib's `Polynomial`, `Matrix.charpoly`,
`Matrix.charmatrix`, or any public polynomial-valued characteristic object on
`ExecComplex`, because on the pinned toolchain those constructions remain
noncomputable and would leak a forbidden public `noncomputable` dependency into
S8b.

Instead, S8b now exposes the strictly executable characteristic-determinant
**evaluation shadow**

- `λ ↦ det (λ I - A)`

over rational `λ`, still on the public `ExecComplex` strand.

## Immediate architectural consequence

The fully explicit polynomial core should be built in the executable branch as a
CNNA-owned algebraic layer (the plan's `ExecSpectral/PolynomialCore` and
`ExecSpectral/CharpolyCore`) and can then be pulled forward once it is locally
closed and build-stable.

This keeps S8b green while preserving the intended S8e direction.
