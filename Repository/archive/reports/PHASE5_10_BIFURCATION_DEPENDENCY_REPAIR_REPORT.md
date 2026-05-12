# v37 Phase 5-10 bifurcation and dependency repair

## What was corrected

The v36 roadmap contained a real derivation-order error: finite spectral and physical objects were effectively placed behind, or inside, the modular-form/j path. That was not justified by their source data. In particular, `SP0`, `SP1`, and `P00`-`P06` consume finite boundary-matrix/operator/regime data from Phase 4.1 and adjacent Schur/BoundaryOperator profiles, not modular forms, q-expansions, Hilbert class polynomials, or analytic j-evaluation.

v37 introduces an explicit phase-path split after Phase 4:

- **Path A**: number theory -> lattice geometry -> modular/j -> theta/L-function/class-number-formula far targets.
- **Path B**: finite spectral profile -> finite operator algebra/star/state/dynamics/channel -> heat/spectral geometry -> transfermatrix -> late Schur/CD bridge objects.

## New governance lock

- **1.1.1.1.0.14**: Phase 5-10 dependency bifurcation lock.
- **LEG33**: Phase 5-10 bifurcation and dependency repair contract.
- **GNG20**: no artificial phase bottleneck or phase-title/object mismatch.

## Main phase ownership after repair

- **Phase 5** now owns base number theory from the operational discriminant: `N00`-`N07`.
- **Phase 6** now owns units, class group, class number, ideals, Heegner/PID/UFD indicator, prime splitting and character: `N08`-`N15`.
- **Phase 7** now owns CM lattice geometry: `L00`-`L07`.
- **Phase 8** now owns modular forms, j and heuristic/sentinel test rows: `M00`-`M08`, `L09`, `L10`, `BR10`.
- **Phase 9** now owns analytic/theta far targets: `L08`, `N16`, `N17`.
- **Phase 10** now owns spectral/physical/transfer/late bridge consumers: `SP0`-`SP5`, `P00`-`P06`, `TM0`-`TM2`, `BR08`, `BR09`, `CD8`, `CD9`.

## Important dependency changes

- `SP0`, `SP1`, and `P00`-`P06` now sit under Phase 10 and depend on Phase 4.1 and regime data, not Phase 8/9.
- `M00`, `M01`, `M06`, and `M07` moved from Phase 10 to Phase 8.
- `L08`, `N16`, and `N17` moved from Phase 10/misc placement to Phase 9.
- `TM0`-`TM2` remain in Phase 10 but are explicitly Schur/transfer objects, not modular-form objects.
- `10.6` and `10.7` were turned into routing notes pointing to Phase 13, because advanced AQFT consumer objects `P07`-`P16` are already owned by the Pillar-B roadmap.

## Validation

- 187 phases
- 197 objects
- 187 scratchpad records
- 197 proof-dossier records
- exactly one active cursor: `1.1.1.1.1`
- no white phase before the active cursor
- generated tables rebuilt from the YAML master
- PDF compiled with `pdflatex` twice
- no Lean build was executed or claimed
