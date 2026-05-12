# Phase 1.1.1.1.2 closeout: reuse/duplication audit and canonical generator policy

## Result

Phase `1.1.1.1.2` is closed as a planning/API-hygiene gate. It does not introduce or move Lean source code. The next active cursor is `1.1.1.1.3`.

## Implemented changes

- `masters/cnna_roadmap_master.yaml`
  - Bumped planning metadata to v41.
  - Set Phase `1.1.1.1.2` to green/closed.
  - Set Phase `1.1.1.1.3` to yellow/active.
  - Updated LEG11 as a documented, closed generated-policy gate.
  - Updated the LEG11 proof dossier.
  - Added the generated-source reuse/duplication ledger rows RD01-RD07.

- `scripts/generate_tables.py`
  - Requires the top-level `reuse_duplication_ledger` section.
  - Validates required ledger columns and decision classes.
  - Generates `tables/reuse_duplication_ledger.tex` and `tables/reuse_duplication_ledger_table.tex`.
  - Exports `generated_exports/reuse_duplication_ledger.generated.tsv`.

- `CNNA_Planning_and_Documentation_Tool_v41_Reuse_Duplication_Generator_Policy_A3_English.tex/.pdf`
  - Adds the reuse/duplication ledger and canonical generator policy as its own PDF section.
  - Records the v41 closeout and active cursor shift.

- `README.md`
  - Documents the v41 content note and next active phase.

## Generator-policy conclusions

- The generated ToC/smoke canonical seam is `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource` plus `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`.
- The downstream generated Schur/DtN/arithmetic chain consumes that seam and must not be duplicated by a parallel generator.
- `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory` and `ActionFormatDecision` are a separate existing action-candidate seam, not a duplicate smoke generator.
- `scripts/generate_tables.py` and `scripts/build_export_script_v1.8.py` are artifact/audit generators only; they are not CNNA mathematical generators.
- Future Phase 5/O07/generator-like implementations must classify their relation to the ledger before adding code.

## Verification

- `python3 scripts/generate_tables.py` completed successfully.
- `pdflatex` completed successfully twice for the v41 PDF.
- Render inspection was performed on the generated PDF around the new reuse/duplication ledger section.
- No Lean source file was modified by this phase.
- The prior Lean build was user-reported green; no new Lean build was executed or claimed here.

## Active next phase

`1.1.1.1.3`: object and quantities proof-documentation infrastructure gate.
