# Strengthening Phase S8c Audit

## Scope of this patch

This S8c patch strengthens `CNNA/PillarA/Finite/SpectralDecompositionC.lean`
on the analytic `ℂ`-mirror strand only.

The executable public strand remains `CNNA/PillarA/Finite/SpectralDecomposition.lean`.
The bridge discipline remains unchanged: later consumers must continue to use
`CNNA/PillarA/Finite/SpectralBridge.lean` for any controlled transfer back into
proof-carrying downstream logic.

## What is added on the analytic mirror strand

- import of `Mathlib.Analysis.Matrix.Spectrum`
- local mirrored `ℂ`-matrix spectral data
  - `eigenvalues`
  - `eigenvectorBasis`
  - `eigenvectorUnitary`
  - `eigenvalueDiagonal`
- explicit mirror-side theorems
  - eigenvector equation via `mulVec_eigenvectorBasis`
  - `eigenvalues_mem_spectrum_real`
  - `unitaryDiagonalization`
  - `spectral_theorem`
  - `charpoly_eq`
  - `roots_charpoly_eq_eigenvalues`
  - `splits_charpoly`
  - `det_eq_prod_eigenvalues`
  - `trace_eq_sum_eigenvalues`
- reference / variation constructors in `StrengtheningS8c`

## Deliberate restriction

All newly introduced spectral objects on this strand are explicitly local
`noncomputable def`s.

No new public executable spectral API is added to the `ExecComplex` strand here,
and this patch does **not** reinterpret the analytic mirror as a second generator.

## Immediate architectural consequence

The S8c mirror now carries the mathlib-provided Hermitian spectral package over the
mirrored Dirichlet operator in one isolated place. This is the intended input for
S8d, where transfer theorems must be stated explicitly over the injective bridge
instead of allowing direct downstream consumption of the mirror layer.
