# v26 global no-go guardrail update

## What changed

The operational no-go list is no longer phase-local scratchpad content. It is now a top-level global planning/workflow invariant in `masters/cnna_roadmap_master.yaml` under `global_no_go_guardrails`.

## New phase

Inserted before the active implementation-manifest gate:

- `1.1.1.1.0 - Global no-go guardrail contract and inheritance lock` — status `G`

The active phase remains:

- `1.1.1.1.1 - Implementation module manifest and semantic placement gate` — status `Y`

No white phase precedes the active phase on the active branch.

## New object

Added:

- `LEG13 - Global no-go guardrail contract`

`LEG13` has a proof dossier documenting the infrastructure: top-level guardrail table, workflow inheritance rule, scratchpad inheritance field, and generated table validation.

## Global rules now tracked

The top-level table records these rules:

1. no `@[simp]` attributes in the operational path
2. no `noncomputable` in the operational path
3. no `classical` helper unless isolated in allowed mirror/non-operational layer
4. no `Matrix.inv` or external inverse oracle in operational derivations
5. no free formula without proof-carrying entry structure
6. no consumer-side patch when the missing structure belongs earlier
7. no premature obstruction before a serious positive construction attempt
8. no phase-semantic public API names
9. no fragile rewrite chain when a structural constructor/projection proof is available
10. do not delete legacy status enums during quarantine
11. do not let Phase 3+ import `Legacy.StatusGates`
12. do not treat old TeX/PDF files as maintained roadmap sources

## Generator/schema changes

`scripts/generate_tables.py` now requires and renders `global_no_go_guardrails`. Every scratchpad record is required to carry `global_no_go_inheritance`.

Phase-local `no_go_guardrails` are interpreted as local addenda only. They may add stricter constraints but cannot weaken the global rules.

## Verification

- YAML-to-table generation succeeded.
- PDF compiled twice with `pdflatex`.
- PDF rendered at low DPI for 112 pages.
- No Lean build was run or claimed.
