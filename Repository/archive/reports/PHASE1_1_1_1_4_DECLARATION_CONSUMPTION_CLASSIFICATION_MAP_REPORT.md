# Phase 1.1.1.1.4 report - Declaration consumption classification map

## Closed phase

- Phase: `1.1.1.1.4`
- Object: `LEG5` - Declaration consumption classification map
- Status after this package: green/closed
- Next active cursor: `1.1.1.2`

## What changed

- Added the top-level YAML section `consumption_classification_map` with the exact allowed class set.
- Extended `scripts/generate_tables.py` to validate the class policy and generate classification records from:
  - `repo_inventory/raw_export/modules.json`
  - `repo_inventory/raw_export/symbol_references/declarations.json`
  - `repo_inventory/raw_export/symbol_references/references.json`
  - `repo_inventory/raw_export/architectural_core/sink_taxonomy.json`
  - the object register and proof-dossier rows.
- Closed `LEG5` in the object register and proof-dossier infrastructure.
- Advanced the unique active phase to `1.1.1.2`.

## Generated artifacts

- `tables/consumption_classification_map.tex`
- `tables/consumption_classification_map_policy_table.tex`
- `tables/consumption_classification_map_summary_table.tex`
- `generated_exports/consumption_classification_map.generated.tsv`
- `generated_exports/module_consumption_records.generated.tsv`
- `generated_exports/declaration_consumption_records.generated.tsv`
- `generated_exports/object_consumption_classification.generated.tsv`
- `CNNA_Planning_and_Documentation_Tool_v43_Declaration_Consumption_Classification_Map_A3_English.tex/.pdf`

## Governance rule closed

The classifier separates semantic consumption from BuildAll/import reachability. It also blocks a previously dangerous shortcut: a blue object cannot become `final-output` or `public-wrapper` just because proof-carrying code exists. Registered blue objects are classified as `blue-semantic-correction` and must pass through Phase `1.1.1.2` before public API exposure is considered.

## Lean source status

No Lean source file was changed. The user reported the pre-phase Lean build green. This package does not claim a new Lean build from this environment.
