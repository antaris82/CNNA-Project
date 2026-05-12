# v29 Architecture Decision Locks Report

## What changed

v29 integrates the six validation findings as explicit pre-implementation planning decisions before the active module-manifest gate.

## New closed infrastructure gates

- `1.1.1.1.0.2` - EXEC-2 rational-boundary and mirror-only algebraic irrationality contract.
- `1.1.1.1.0.3` - Refactor regression protocol and incremental migration policy.
- `1.1.1.1.0.4` - Lean/mathlib version baseline and upgrade-gate policy.
- `1.1.1.1.0.5` - Phase-type-specific scratchpad schema and governance-depth review gate.
- `1.1.1.1.0.6` - Phase 3 to Phase 4 consumer-contract direction lock.

The unique active phase remains `1.1.1.1.1`.

## New/updated policy decisions

- EXEC-2: operational `ExecComplex` remains a rational `Q x Q` path. Algebraic irrationalities live in mirror/non-operational layers unless reduced to a separately proved rational/integer invariant.
- Refactor mode: wrapper-first incremental migration with migration metrics and local full-build evidence before closeout.
- Version mode: Lean 4.28.0/mathlib baseline freeze unless an explicit phase-boundary upgrade gate is opened.
- Scratchpad mode: every phase has `phase_type` and type-specific evidence obligations.
- Governance mode: after the first real code-change/refactor phase, perform a governance-depth retrospective; global guardrails remain, but later phase granularity may be flattened if justified.
- Consumer-contract mode: Phase 3.6 exports the boundary/operator shape needed by Phase 4.1; Phase 4.1 consumes it without reconstructing Schur/DtN internals.

## New objects and proof dossiers

- `LEG20` - EXEC-2 rational ExecComplex boundary policy.
- `LEG21` - Refactor regression and incremental migration protocol.
- `LEG22` - Lean/mathlib version migration policy.
- `LEG23` - Phase-type-specific scratchpad schema and governance retrospective.
- `LEG24` - Phase 3 to Phase 4 consumer-contract direction.

All five have generated proof-dossier entries.

## Affected existing objects

The ExecComplex/computable-path text was tightened for `O06`, `L00`, `L02`, `L04`, `M05`, and `SP0` to prevent algebraic irrational data from entering the operational `Q x Q` path without a proved rational/integer return invariant.

## Generator/schema changes

`scripts/generate_tables.py` now validates and renders the new scratchpad fields:

- `phase_type`
- `phase_type_specific_contract`
- `refactor_regression_protocol`
- `refactor_migration_metrics`
- `lean_mathlib_version_policy`
- `exec_complex_boundary_policy`
- `consumer_contract_direction`
- `governance_overhead_review`

## Validation

- Generated tables from one YAML master: 159 phases, 168 objects, 159 scratch-pad records, 168 proof-dossier records.
- Exactly one active cursor: `1.1.1.1.1`.
- No white phases precede the active cursor in natural order.
- PDF compiled with `pdflatex` twice: 182 pages.
- Sample render checks were produced for representative pages. Full all-page render was too slow in this environment, so no full-render claim is made.
- No Lean build was executed or claimed.
