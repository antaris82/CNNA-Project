# V1.17 License, root README and credit-surface report

Status: completed tooling/documentation update.

## Scope

V1.17 closes the package-entry surface around licensing, README placement and visible credits.

## Changes

- Added root `LICENSE` with dual project-authored licensing:
  - documentation/prose/generated reports/PDFs: CC BY 4.0
  - Lean/Python/tool/source code: MIT
- Kept the maintained `README.md` only in the package root.
- Removed duplicate `README.md` files from `Repository/` and `Repository/repo_inventory/raw_export/`.
- Added visible credits:
  - Editor: Jan Seeck (antaris)
  - Assistant: ChatGPT (OpenAI)
- Added the minimum tested assistant setup:
  - ChatGPT Plus account with GPT-5.5
- Updated full and context documentation generators so generated PDFs expose the editor/assistant credits.
- Updated the cleanup policy so accidental `Repository/README.md` copies are not retained as active documentation roots.

## Verification

- `python3 scripts/generate_tables.py` succeeds.
- Full PDF compiles under `Repository/generated_docs/full/` with visible credits.
- DtN context PDF compiles under `Repository/context_docs/dtn_matrix/` with visible credits.
- `find . -name README.md` returns only the package-root README.
- No Lean source under `Repository/repo_snapshot/CNNA` was edited.
- No Lean build was run or claimed.

## Truth-status boundary

Licensing and credits are generated-secondary governance metadata. They do not change the CNNA truth-status rule: Lean code is the primary formal source; documentation, generated PDFs, reports, graphs, tables and context slices remain review aids requiring discipline-specific expert review.
