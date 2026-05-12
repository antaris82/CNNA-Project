# V1.19 Phase Status Release Policy Report

## Scope

V1.19 implements the rule that unreleased direct Lean-derivation phases must be red/locked by default. White status is now reserved for non-direct-Lean work such as refactoring, tooling, infrastructure, documentation, comparison, packaging, and generated-secondary workflows.

## Changes

- Converted 81 phases from `W` to `R` because their scratchpad `phase_type` was `derivation`.
- Kept green phases unchanged.
- Kept the unique yellow active cursor unchanged: `1.1.1.1.5`.
- Kept orange phase `1.1.1.2` unchanged.
- Added `DBR13`, `GNG31`, `SCF50`, workflow `Phase status release and red-lock workflow`, and phase `20.13`.
- Patched `scripts/generate_tables.py` so:
  - exactly one active `Y` phase is required;
  - red phases are no longer treated as active;
  - any future `phase_type = derivation` with `Phase status = W` fails validation.

## Release rule

A red derivation phase may become yellow or orange only after a pre-implementation release check references the prerequisite already-derived Lean objects/proof dossiers. This check must show why the phase is now implementable rather than merely desired.

## Validation

- `python3 scripts/generate_tables.py` must pass.
- Status counts must show zero white derivation phases.
- No Lean source under `Repository/repo_snapshot/CNNA` was modified.
- No Lean build is claimed.
