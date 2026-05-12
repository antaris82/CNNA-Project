# v34 Regime-Typed Heegner / General Test Matrix Report

## Purpose

v33 made the Eisenstein/Gauss rows sentinel rows inside a general early finite computation test matrix. v34 adds the missing semantic axis: regime typing. The early test matrix now separates generic finite coverage, noOuter/empty-set REAL-root sentinel candidates, and HasOuter/complement-projection or comparison rows.

## Main planning correction

Eisenstein/Gauss are no longer just late special examples. They are now planned as early sentinel hypotheses for the closed noOuter/empty-set REAL-root branch, while all additional class-number-one/Heegner/CM targets remain HasOuter/complement-projection or comparison rows unless noOuter provenance is derived.

This prevents the false inference:

`h(D)=1` or external Heegner-list membership => closed/noOuter regime.

The correct planning rule is:

CNNA regime status must be derived from Pillar-A source/regime data. Number-theoretic class-number-one status and CM/j special values are consumer-side comparison data until the regime tag is proved.

## Added planning artifacts

- Green decision gate: `1.1.1.1.0.11 - Regime-typed early test matrix and Heegner-projection lock`.
- Future test phase: `4.0.2 - Regime-typed finite computation test matrix: noOuter-root sentinel versus HasOuter projection rows`.
- Future classification phase: `7.2.1 - Heegner/class-number-one regime classification after class-number data`.
- New objects: `LEG30`, `O08`, `N18`, `BR11`, `BR12`.
- New global guardrail: `GNG17 - no Heegner/class-number-one membership as closed noOuter evidence`.
- New workflow: `Regime-typed Heegner/CM finite test matrix workflow`.
- New format decision: `Regime split for Heegner/CM test rows`.

## Test semantics now planned

The general early test matrix must contain generic finite rows first. Sentinel rows are then regime-tagged:

- `noOuter-root / closed candidate`: likely Eisenstein and Gauss sentinels only, pending derivation.
- `HasOuter / complement projection`: other Heegner/class-number-one/CM rows by default.
- `comparison-only`: any row with mirror-only tau, sqrt(D), analytic j, or external class-number data before CNNA derivation.

## Validation

`generate_tables.py` generated tables successfully from one YAML master with 177 phases, 189 objects, 177 scratch-pad records, and 189 proof dossiers. The PDF was compiled twice with `pdflatex` and selected pages were rendered. No Lean build was run.
