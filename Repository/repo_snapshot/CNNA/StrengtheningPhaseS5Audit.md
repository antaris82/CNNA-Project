# CNNA Strengthening Phase S5 audit

Stand of this audit: prepared for the S5 implementation pass on top of the uploaded green S4 tree and aligned with the plan dated 12 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S5 closure target

S5 closes the first two generator bottlenecks after the now shared S4 finite box path.
It must not replace the generic operator path with a reference-only shortcut.
Instead it must make two things explicit on the same active `Approximant -> DirichletLaplacian -> DtN` chain:

- `DirichletWeight` is no longer a free middle-field but is bound to a visible policy / builder surface.
- `InteriorInverse` is no longer allowed to survive as a public generator-side type or as an explicit S5 builder argument.

## 2. What this implementation adds

This pass keeps the existing P11/P12 mathematics, but changes the generator interlock.
It adds:

- a policy-bound `DirichletLaplacianStrong` surface with `source + policy` instead of `source + free weight`,
- explicit builders `DirichletLaplacianStrong.ofApproximant` and S5 reference / variation specializations,
- a classified `InteriorEliminationMode` for the binary DtN stage,
- a public `InteriorEliminationData` contract exposing only `interiorSolve`, `boundaryOperator` and the corresponding correctness theorems,
- a `DtNStrong.ofEliminationData` builder over exactly that abstract elimination surface,
- S5 reference / variation DtN specializations that no longer take an inverse witness explicitly,
- and an internal private inverse witness used only as a local implementation aid inside `DtN/DtN.lean`.

## 3. Why this is the right S5 shape

The plan requires the generator to vary over `(Substrate, WeightPolicy, Cutoff)` and forbids free operator witnesses from drifting through the production path.
Binding the Dirichlet stage to `WeightPolicy` does exactly that: downstream consumers only see the released policy law, not an arbitrary weight matrix.

The DtN side is now closed at the intended S5 abstraction boundary.
Publicly visible are only

- the classified elimination mode,
- the solve surface,
- the induced boundary operator surface,
- and their proof-carrying correctness theorems.

The old inverse witness has been pushed fully behind the public edge:
there is no public `InteriorInverse` type anymore, no public `DtNStrong` inverse field, and no reference / variation S5 builder with an explicit inverse argument.
That matches the plan's fallback rule: if an inversion witness still exists at this stage, it may survive only as a local internal implementation detail.

## 4. What this pass still does not claim

This pass does **not** yet prove that the public elimination contract is populated canonically by a fully derived constructive algorithm for every legal generator instance.
What S5 closes is the public architecture boundary: inverse data no longer leaks through the generator surface.
The stronger provenance closure of the elimination contract itself remains subsequent work.

Likewise this pass does **not** yet internalize the stabilization / closure side.
That remains the S6 obligation.

## 5. Regression conditions after this pass

Treat the following as regressions if they appear:

- reintroducing a free `weight` field into `DirichletLaplacianStrong`,
- reintroducing a public `InteriorInverse`-style type or an explicit inverse argument on the S5 DtN builders,
- reintroducing a public `interiorInverse` field into `DtNStrong`,
- exporting inverse matrices on the notation surface as if they were the real binary DtN interface,
- bypassing the S4 reference / variation approximant path with a new operator-only smoke route,
- or letting `DtNStabilized` consume anything other than the proof-carrying `boundaryOperator` surface of the reshaped `DtNStrong` stage.
