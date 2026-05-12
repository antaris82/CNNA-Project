# V1.23 PDF Font Scale Report

## Scope

This update implements the user request to make generated-document text one size larger. The change is limited to generated-secondary PDF/TeX documentation layout. It does not modify Lean source code, YAML row semantics, context filtering, object definitions, phase status, proof status, or database/public-view semantics.

## Changed files

- `Repository/scripts/generate_full_document.py`
- `Repository/scripts/generate_context_doc.py`
- `Repository/scripts/generate_tables.py`
- `Repository/scripts/build_export_script_v1.8.py`
- `Repository/masters/cnna_roadmap_master.yaml`
- `README.md`

## Typography rule

- Full/context PDFs now use `11pt` A3 landscape document classes.
- Explicit generated TeX size commands are bumped one step: `tiny -> scriptsize`, `scriptsize -> footnotesize`, `footnotesize -> small`, `small -> normalsize`.
- Generated DOT graph labels controlled by the tool are bumped by one point where applicable.

## Validation expectations

- `python3 scripts/generate_tables.py` succeeds.
- `python3 scripts/generate_full_document.py --compile` succeeds.
- A representative context PDF compiles successfully.
- Generated TeX contains `documentclass[11pt,...]` and larger table text commands.
- Representative generated PDF pages render without obvious clipping/black-glyph failure.
- No Lean source under `Repository/repo_snapshot/CNNA` is changed.
