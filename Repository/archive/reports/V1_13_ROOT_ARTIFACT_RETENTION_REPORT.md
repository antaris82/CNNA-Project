# V1.13 Root artifact retention and cleanup report

## Decision

The repository root is source-oriented. `README.md` stays in the root as the human entry point. Historical Markdown reports are archived under `archive/reports/`. Full-document PDFs, TeX wrappers, and LaTeX build byproducts are disposable generated-secondary artifacts and are not retained in the root package.

## Rationale

The maintained planning source is `masters/cnna_roadmap_master.yaml`. Generated tables, exports, full PDFs, context documents, and graph views are secondary surfaces. Retaining old PDFs/TeX files in the root makes generated artifacts look like sources and obscures the Lean-primary / YAML-master discipline.

## Implemented changes

- Added `DBR8`, `GNG27`, `SCF46`, Phase `20.8`, proof dossier `proof:DBR8`, a workflow-policy row, and implementation-scaling row `1.1.1.5.12`.
- Added `scripts/generate_full_document.py` to generate the full PDF/TeX under `generated_docs/full/` on demand.
- Added `scripts/clean_generated_root_artifacts.py` to move root Markdown reports to `archive/reports/` and delete root PDF/TeX/LaTeX byproducts.
- Added `.gitignore` rules for disposable generated documentation products.
- Moved historical root Markdown reports into `archive/reports/`.
- Removed root PDF/TeX/LaTeX build products from the package root.

## Verification

- `python3 scripts/generate_tables.py` succeeded.
- `python3 scripts/generate_full_document.py --compile` succeeded in `generated_docs/full/` before disposable outputs were removed from the package.
- First pages of the generated full PDF were spot-rendered.
- `python3 scripts/clean_generated_root_artifacts.py --apply` produced `generated_exports/root_artifact_cleanup.generated.json`.
- Final root check: only `README.md` and `.gitignore` remain as root files.

No Lean source was changed and no Lean build is claimed.
