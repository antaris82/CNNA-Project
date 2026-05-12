# V1.14 README workflow-orientation report

V1.14 replaces the chronological README with a current operational manual for the CNNA planning/documentation tool.

## Changes

- Rewrote `README.md` as a non-chronological current manual.
- Documented manual generation commands for tables, full documentation, context documentation, inventory refresh, and cleanup.
- Documented ChatGPT-assisted workflow use explicitly.
- Corrected the assistant-workflow claim: this package was developed/tested with ChatGPT, not Claude.
- Explained where the actual value of the tool lies: standardized, extensible workflows over the Single-YAML-Master state.
- Added workflow scalability rules and the database/interactive-map vision in compact form.
- Preserved Lean-primary/generated-secondary/expert-review discipline.

## Verification

- No Lean source was changed.
- `masters/cnna_roadmap_master.yaml` was updated with phase `20.9`, object `DBR9`, proof dossier `proof:DBR9`, scratchpad record, and V1.14 latest-change overview.
- `python3 scripts/generate_tables.py` was run successfully after the update.

## Status

Closed as documentation/tooling update. The active mathematical/content cursor remains `1.1.1.1.5`.
