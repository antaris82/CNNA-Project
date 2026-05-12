# V1.18 Section Pagebreak Layout Report

## Scope

This update implements the user requirement that every generated documentation section starts on a new page. The change is limited to generated-secondary PDF/TeX documentation layout. It does not modify Lean source code, context-filter semantics, object definitions, phase semantics, or proof status.

## Changed files

- `Repository/scripts/generate_full_document.py`
- `Repository/scripts/generate_context_doc.py`
- `Repository/masters/cnna_roadmap_master.yaml`
- `README.md`

## Layout rule

Generated full and context documentation now load `etoolbox` and prepend `\clearpage` to top-level `\section` commands. This covers normal and starred section commands emitted by the documentation generators.

## Validation expectations

- `python3 scripts/generate_tables.py` succeeds.
- `python3 scripts/generate_full_document.py --compile` succeeds.
- `python3 scripts/generate_context_doc.py "DtN Matrix" --profile dtn-matrix --slug dtn_matrix` succeeds.
- Generated TeX contains `\pretocmd{\section}{\clearpage}{}{}`.
- Representative generated PDF pages render without visible title/TOC/front-matter breakage.
- No Lean source under `Repository/repo_snapshot/CNNA` is changed.
