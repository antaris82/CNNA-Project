# Tool V1.10 - Graph arrow-direction conventions

## Scope

This update clarifies the meaning of arrows in the two graph figures embedded under the front `Stats` / module-inventory section.

## Changes

- Advanced `metadata.tool_version` from `V1.09` to `V1.10`.
- Kept the Lean-code data timestamp fixed at `2026-05-10T05:51:42+02:00`.
- Added explicit text under Graph A:
  - `A -> B` means at least one module in group `A` imports or depends on a module in group `B`.
  - The arrow points from consumer/importer to required dependency.
  - Graph A is a technical import/dependency graph, not a semantic derivation graph.
- Added explicit text under Graph B:
  - `A -> B` means `B` is the next curated semantic construction step derived from `A` along the robust core mainline.
  - The arrow points in the intended derived-only construction direction.
  - Graph B is a semantic mainline view, not a complete Lean import graph.
- Updated `latest_change_overview` and README accordingly.

## Validation

- `python3 -m py_compile scripts/generate_tables.py scripts/generate_context_doc.py`
- `python3 scripts/generate_tables.py`
- Recompiled the full V1.10 PDF with `pdflatex` twice.
- Regenerated the DtN Matrix context documentation with `scripts/generate_context_doc.py`.
- Verified by text extraction that the Graph A / Graph B arrow-convention paragraphs appear on page 3.
- Rendered page 3 of the V1.10 PDF for visual inspection.

## Lean source status

No Lean source file was changed. No Lean build is claimed for this documentation/display update.
