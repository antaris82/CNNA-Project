# CNNA Strengthening Phase S8a audit

Stand of this audit: first S8a architecture pass on top of the uploaded green S7b tree and aligned with the plan dated 17 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S8a closure target

S8a is the architectural opening move of the S8 spectral-root block.
It does **not** yet claim the full proof-carrying spectral package of ordered eigenvalues, projectors, orthogonality, completeness, and downstream export theorems.
Its job is narrower and more structural:

- `Finite/SpectralDecomposition` must become the **public operative ExecComplex surface**.
- the analytic `ℂ`-path must be split off into an explicit mirror module instead of leaking into the operative API.
- all comparison between both sides must run through an explicit bridge module.

This is the direct S8 analogue of the already established MatrixNorms dual-strand discipline.

## 2. What this implementation changes

This pass adds three new finite modules.

- `CNNA/PillarA/Finite/SpectralDecomposition.lean`
  introduces `SpectralDecompositionStrong` as the operative S8 root shell over `DirichletLaplacianStrong`.
  It exposes only computable `ExecComplex` data: a rational-weight-derived executive matrix, Frobenius data, zero test, shift surface, and a Hermitian certificate on the Exec side.

- `CNNA/PillarA/Finite/SpectralDecompositionC.lean`
  introduces `SpectralDecompositionCStrong` as the separate analytic mirror shell.
  At this stage it only mirrors the operative matrix into `ℂ` and exports the mirrored Hermitian contract.

- `CNNA/PillarA/Finite/SpectralBridge.lean`
  introduces `SpectralBridgeStrong` as the explicit bridge shell between both sides.
  The current bridge proves the matrix-level identification with `ExecComplexBridge.mapMatrix` and transfers Frobenius / shift comparisons through the already existing bridge infrastructure.

In addition, the finite `BuildAll` and notation layers are extended so that the new S8a architecture is part of the active public tree.

## 3. Why this is the right first S8 shape

The plan requires spectral, state, thermal, and dynamical seeds to remain publicly computable, with any unavoidable noncomputability strictly localized and justified by the whitelist.
At the same time it explicitly forbids a silent second generator path over `ℂ`; the analytic side is allowed only as a bridge-controlled mirror of an already closed operative ExecComplex definition.

Therefore the first safe S8 step is not "attach mathlib spectral theorem directly to the public S8 module", but

- operative Exec shell first,
- analytic mirror second,
- bridge third.

That keeps the future full spectral package compatible with the plan instead of forcing a later architectural rollback.

## 4. What this pass still does not claim

This pass does **not** yet prove that the operative S8 surface already provides

- ordered eigenvalues,
- eigenvectors,
- spectral projectors,
- completeness,
- or the final A-seeded export theorems required by the plan-level S8 closure criterion.

It also does **not** yet prove the sharpened bridge statement that the current Exec matrix is theorematically identical to the existing real-valued Dirichlet matrix entry-by-entry.
The present S8a bridge closes only the Exec ↔ `ℂ` mirror split.

Those stronger statements belong to the next S8 sharpening steps.

## 5. Regression conditions after S8a

Treat the following as regressions if they appear:

- reintroducing `noncomputable` public definitions into `Finite/SpectralDecomposition.lean`,
- importing the analytic mirror directly into later finite seeds instead of going through `SpectralBridge`,
- or letting the `ℂ`-mirror become a silent replacement for the operative Exec surface.

## 6. Recommended next continuation after a green S8a build

After a green S8a build, the next safe continuation is to sharpen the bridge and only then attach the first actual spectral data package.
In concrete terms:

- first prove the theorematic alignment between the new Exec matrix and the pre-existing real Dirichlet matrix,
- then add the analytic noncomputable spectral data on the mirror side,
- and only after that decide which parts can be reflected back as operative certificates, candidates, or exact seeds on the Exec side.
