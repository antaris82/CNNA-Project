# CNNA Tool V1.08 - Context-filtered documentation slices

## Change scope

V1.08 implements a generated-secondary documentation-slice function. The function preserves the official documentation section topology but filters row-level content by a query/profile.

## Added function

- `Repository/scripts/generate_context_doc.py`

Example:

```bash
cd Repository
python3 scripts/generate_tables.py
python3 scripts/generate_context_doc.py "DtN Matrix" --profile dtn-matrix --slug dtn_matrix
```

Generated output:

- `Repository/context_docs/<slug>/context_filter_manifest.json`
- `Repository/context_docs/<slug>/context_section_summary.tsv`
- `Repository/context_docs/<slug>/matched_rows/*.matched.tsv`
- `Repository/context_docs/<slug>/<slug>_context_documentation.tex`
- `Repository/context_docs/<slug>/<slug>_context_documentation.pdf` if `pdflatex` succeeds

## Added planning records

- Phase `20.6`: Context-filtered documentation slices
- Object `DBR6`: Context-filtered documentation slice generator
- Proof dossier `proof:DBR6`
- Scratchpad record for `20.6`
- Workflow row: Context-filtered documentation slice generation
- Implementation-scaling row `1.1.1.5.10`
- Curated context profile `dtn-matrix`

## Sample output

The package includes a sample generated documentation slice:

- `Repository/context_docs/dtn_matrix/dtn_matrix_context_documentation.pdf`
- `Repository/context_docs/dtn_matrix/context_filter_manifest.json`
- `Repository/context_docs/dtn_matrix/context_section_summary.tsv`
- `Repository/context_docs/dtn_matrix/matched_rows/*.matched.tsv`

The human PDF uses the default cap of 80 rows per section; full matched row sets are exported as TSV.

## Validation performed

- `python3 -m py_compile scripts/generate_context_doc.py scripts/generate_tables.py`
- `python3 scripts/generate_tables.py`
- `python3 scripts/generate_context_doc.py "DtN Matrix" --profile dtn-matrix --slug dtn_matrix --pdf-max-rows-per-section 80`
- `pdflatex` compilation of the V1.08 full documentation PDF
- `pdflatex` compilation of the sample DtN context documentation PDF
- Spot rendering of the sample DtN PDF and the V1.08 full PDF first pages

## Non-claims

No Lean source was changed. No Lean build was run. The context-documentation output is a filtered generated-secondary view only; it is not a semantic certificate and does not replace discipline-specific expert review.
