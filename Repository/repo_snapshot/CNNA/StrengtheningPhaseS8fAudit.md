# Strengthening Phase S8f Audit

## Scope of this patch

This S8f patch closes the public operative spectral root by turning the already green
visible `ExecSpectral/*` follow-block back into a single proof-carrying public API on
`CNNA/PillarA/Finite/SpectralDecomposition.lean`.

To avoid an import cycle, the former S8a/S8b file content is moved unchanged into
`CNNA/PillarA/Finite/SpectralDecompositionCore.lean`. The public
`Finite/SpectralDecomposition.lean` now consumes that core plus the explicit S8e
follow-block.

## What is added

- `Finite/SpectralDecompositionCore.lean`
  - unchanged green S8a/S8b operative root surface extracted into a stable core layer
- `Finite/SpectralDecomposition.lean`
  - public consumer layer over `ExecSpectral/*`
  - explicit operative follow-block accessors
    - `execPolynomialCore`
    - `execCharpolyCore`
    - `execRootIsolation`
    - `execEigenvectorKernel`
    - `execProjectorCore`
    - `execCertificates`
  - theorematic provenance chain for the public consumer stack
  - `CoordinateAlgebraicSpectralPackage`
    - rational isolation window
    - executable kernel candidate
    - projector data and proof-carrying certificates
  - `AlgebraicSpectralPackage`
    - public bundled operative shadow/certificate
    - explicit attachment of the visible S8e follow-block
- notation updates in
  - `CNNA/PillarA/Finite/Notation.lean`
  - `CNNA/PillarA/Notation.lean`
- `StrengtheningS8f` reference / variation constructors

## Deliberate restriction

This patch still does **not** claim a closed fully general computable eigenbasis algorithm for arbitrary
finite executable Hermitian matrices. The public S8 surface now exports the most general proof-carrying
computable algebraic package that is actually available from the visible CNNA-owned executable stack,
while the analytic `ℂ` mirror remains external to the operative production API.

## Immediate architectural consequence

The remaining spectral boundary is now explicitly confined to the visible executable
follow-block itself rather than being smeared across the public API. Later strengthening can sharpen
that follow-block internally, while downstream consumers already see a single operative
proof-carrying spectral package over `ExecComplex`.
