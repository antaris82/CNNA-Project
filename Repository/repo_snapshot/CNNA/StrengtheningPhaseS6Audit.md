# CNNA Strengthening Phase S6 audit

Stand of this audit: prepared for the S6 implementation pass on top of the uploaded green S5 tree and aligned with the plan dated 12 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S6 closure target

S6 closes the shift / stabilization / closure bottleneck directly above the S5 binary DtN stage.
It must not let a raw `epsilon : ℝ` drift further through the production path as an undocumented primitive.
It must also not silently switch the active generator to an analytic mirror strand.

Concretely the phase target is:

- `DtNStabilized` no longer exposes a bare `epsilon` field but a visible `RegularizationPolicy`.
- the stabilization shift is derived from the computable MatrixNorms productiv side,
  not from a C-mirror artifact,
- and `ParameterClosure` / `RegularizationClosure` carry that provenance forward explicitly.

## 2. What this implementation changes

This pass reshapes the S6 modules as follows.

- `DtNStabilizedStrong` is now `source + policy` instead of `source + epsilon`.
- `epsilon` remains available as a theorem-backed derived projection via
  `regularizationPolicy.epsilonReal`, so downstream code does not need a semantic rewrite.
- A computable `comparisonOperator : Matrix _ _ ExecComplex` is introduced on the active path.
  It is boundary-shaped and policy-bound; it uses the released rational weight seed of the upstream
  Dirichlet policy rather than any analytic mirror matrix.
- `regularizationShiftQ` is computed as
  `regularizationPolicy.canonicalShift comparisonOperator`, hence through
  `MatrixNorm.Exec` / `RegularizationPolicy` and not through the analytic C strand.
- `ParameterClosureStrong` and `RegularizationClosureStrong` now re-export the
  regularization policy, comparison operator, rational shift and the induced real shift.
- S6 family builders are added for
  `referenceFullDtNStabilized`, `variationFullDtNStabilized`,
  `referenceFullParameterClosure`, `variationFullParameterClosure`,
  `referenceFullRegularizationClosure`, and `variationFullRegularizationClosure`.

## 3. Why the comparison operator is shaped this way

The uploaded S5 tree still exposes the public DtN boundary operator as an `ℝ`-matrix.
At this point the active path does **not** yet carry a released executable entrywise operator surface
whose coefficients live directly in the public `ExecComplex` strand.
Because of that, an exact entrywise reuse of the raw boundary operator inside `MatrixNorm.Exec`
is not presently available without introducing a new hidden conversion seam.

This pass therefore uses the strongest currently legal active-path object that is both computable and
already proof-carrying:

a boundary-shaped `ExecComplex` comparison operator built from

- the finite boundary carrier of the S5 DtN object, and
- the rational released weight seed `constantWeightQ` of the upstream `WeightPolicy`.

That keeps the shift provenance on the computable productiv side and prevents the generator from
silently depending on the analytic mirror strand. It is an S6 closure of the public architecture
boundary, not yet the final word on the sharpest possible comparison surface.

## 4. What this pass still does not claim

This pass does **not** claim that the comparison operator is already the final mathematically sharp
stabilization comparator for all later spectral work.
What it closes is the S6 architecture requirement:
primitive regularization data is no longer drifting through the active path as an untyped raw real,
and the shift now comes from the computable MatrixNorms strand.

A later strengthening step may still replace the current comparison operator by a strictly sharper
released executable operator proxy once that proxy is genuinely available on the active path.

## 5. Regression conditions after this pass

Treat the following as regressions if they appear:

- reintroducing a raw public `epsilon : ℝ` field into `DtNStabilizedStrong`,
- computing the active stabilization shift from `MatrixNorm.Analytic` or from a C-side mirror object,
- carrying a free shift value through `ParameterClosureStrong` or `RegularizationClosureStrong`,
- bypassing `RegularizationPolicy` with ad hoc real regularization parameters on the S6 builders,
- or moving the S6 comparison logic into later coupling / handoff modules instead of keeping it local
  to the S6 stabilization boundary.


Update (post-green review): the provisional off-diagonal comparison surface was sharpened to a full ExecComplex complete-graph Laplacian on the boundary carrier. The diagonal is now the induced degree and the off-diagonal entries are the negative constant policy weight. This stays derived-only from `(boundaryVertex, WeightPolicy)` and is more operator-near than the earlier flat comparison surface while remaining fully on the computable ExecComplex path.
