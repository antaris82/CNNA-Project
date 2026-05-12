# V1.20 Documentation Section Explanations and Module Manifest Appendix Report

## Scope

V1.20 addresses two documentation-readability issues:

1. The old `Implementation module manifest and semantic placement gate` looked like a second phase table.
2. Major sections/tables needed concise static explanations of what data they display, where the data comes from, and why it is shown.

## Implemented changes

- Moved and renamed the module manifest section to `Technical appendix: module-change manifest and semantic placement gate`.
- Clarified that the appendix is not a phase-release table and is used only for concrete Lean module/API/import-surface changes.
- Added static section explanations to the full documentation generator.
- Added static per-section explanations to the context documentation generator.
- Tightened static text in selected table fragments, including the phase table and module-change manifest table.
- Added DBR14, GNG32, SCF51, workflow policy and scratchpad records.

## Boundary

Only static explanatory prose changed. Table rows remain dynamic and are still generated from the Single YAML Master or generated TSV/JSON exports. Lean code, phase release status, context matching semantics and object/proof records were not changed except for the new V1.20 documentation-tooling records.

## Validation expectations

- `python3 scripts/generate_tables.py` succeeds.
- `python3 scripts/generate_full_document.py --compile` succeeds.
- `python3 scripts/generate_context_doc.py "DtN Matrix" --profile dtn-matrix --slug dtn_matrix` succeeds.
- Generated full TeX contains the technical appendix title after the phase/scratchpad sections.
- Generated context TeX contains static `Purpose and source` paragraphs.
- No Lean source under `Repository/repo_snapshot/CNNA` is changed.
