# v32 Heuristic Lattice Test Matrix Lock

## What changed

v32 integrates post #97 from the astronews thread as a planning and test obligation, not as a generator definition. The post describes a b-ary address construction, the 120-degree Eisenstein and 90-degree Gauss spiral profiles, level-3/level-4 closure targets, and the distinction between hierarchical overlays and spiral angle dependence.

## New decision gate

- `1.1.1.1.0.9` - Heuristic Eisenstein/Gauss lattice test-matrix boundary and ordering lock

This gate is green because it is a planning decision, not a Lean implementation.

## New future phases

- `8.5` - Eisenstein/Gauss heuristic lattice test matrix: static branching and L_max sweep
- `8.6` - Dynamic branching and code-defined b lattice test-matrix extension
- `8.7` - Heuristic lattice test-matrix closeout and public-boundary audit

## New objects / proof dossiers

- `LEG28` - Heuristic Eisenstein/Gauss lattice test-matrix boundary contract
- `L09` - Static branching Eisenstein/Gauss lattice test matrix
- `L10` - Dynamic branching and L_max lattice test sweep
- `M08` - Eisenstein/Gauss CM and j special-value test targets
- `BR10` - Hierarchical versus spiral embedding collision and closure audit

## Required future test-matrix dimensions

- code-defined branching `b`, not the forum drawing convention
- static branch rows, including at least `b = 2` if legal in the code
- dynamic branch rows if the generated branch-family route exposes them
- `L_max` rows spanning at least `1, 2, 3, 4` plus later sanity rows
- angle profiles: Eisenstein `120 deg`, Gauss `90 deg`
- rational cosines: `-1/2` and `0`
- closure-depth targets: Eisenstein level `3`, Gauss level `4`
- finite address counts and collision/overlay relation witnesses
- CM targets: `rho` and `i` in mirror/comparison layer
- discriminant targets: `D = -3`, `D = -4`
- j targets: `0`, `1728` as comparison integers after `M05`

## Boundary rules

- The geometry is a test target, not a source of the generator.
- `b` must be the code-defined branching object.
- Complex coordinates, `tau`, `sqrt(D)`, and analytic `j` evaluation remain outside the operational ExecComplex path unless a rational/integer invariant is explicitly exported.
- The test matrix must consume the canonical generator and must not implement a parallel tree generator.

## Validation

- 172 phases
- 182 objects
- 172 scratch-pad records
- 182 proof dossiers
- exactly one active cursor: `1.1.1.1.1`
- no white phases before the active cursor
- PDF compiled twice with `pdflatex`: 198 pages
- selected pages rendered for visual QA: 1, 4, 96, 119
- no Lean build executed or claimed
