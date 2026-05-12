# CNNA Tool V1.09 - Stats front section, tool-interface Leitmetapher, and license notices

## Change scope

V1.09 adds a compact front `Stats` section to the generated full PDF, records the tool-interface Leitmetapher as a bounded documentation principle, and adds explicit project license notices.

## Added planning records

- Phase `20.7`: Stats front section, tool-interface guiding metaphor, and project licensing notices
- Object `DBR7`: Stats front section and tool-interface documentation layer
- Proof dossier `proof:DBR7`
- Scratchpad record for `20.7`
- Guardrail `GNG25`: no tool-interface metaphor as formal CNNA theorem or ontic input
- Implementation-scaling row `1.1.1.5.11`

## Added/generated documentation artifacts

- `guiding_metaphors` YAML section
- `license_notice` YAML section
- `generated_exports/project_stats.generated.tsv`
- `generated_exports/guiding_metaphors.generated.tsv`
- `generated_exports/license_notice.generated.tsv`
- `tables/stats.tex`
- `tables/project_stats_table.tex`
- `tables/guiding_metaphors.tex`
- `tables/guiding_metaphors_table.tex`
- `tables/license_notice.tex`
- `tables/license_notice_table.tex`
- `CNNA_Planning_and_Documentation_Tool_V1_09_Data_2026-05-10T05-51-42_CEST_A3_English.tex/pdf`

## Stats integration

The full PDF now starts with `Stats`. The former top-level section `Repository module inventory and derivation graphs` is removed from the main section sequence and embedded under `Stats`. The repository inventory and graph content remains available, but the opening section now also includes project-scale facts and the review/licensing frame.

## Tool-interface Leitmetapher

The new guiding metaphor is stored as `GM-TOOL-INTERFACE`. It states that the CNNA tool locally exposes an active phase as a bright object against the complementary rest of the Lean codebase and still unaudited semantic surroundings. Master-YAML, registers, proof dossiers, module/import DAGs, context slices, and later database views are the interface layer.

The boundary is explicit: this is an architecture metaphor for documentation and review practice only. It is not a formal CNNA theorem, not an ontic input, and not a replacement for Lean-primary verification or discipline-specific expert review.

## License notice

The documentation now states:

- project-authored documentation, prose, generated reports, and PDFs: CC BY 4.0
- project-authored source code, Lean files, Python scripts, and tool code: MIT

Third-party dependencies, upstream libraries, and quoted/reference material retain their own licenses and rights.

## Validation performed

- `python3 -m py_compile scripts/generate_tables.py scripts/generate_context_doc.py`
- `python3 scripts/generate_tables.py`
- `python3 scripts/generate_context_doc.py "DtN Matrix" --profile dtn-matrix --slug dtn_matrix --pdf-max-rows-per-section 80`
- `pdflatex` twice on the V1.09 full documentation PDF
- render check for the opening V1.09 full-PDF pages
- render check for the DtN context-documentation PDF opening pages

## Non-claims

No Lean source was changed. No Lean build was run. The Stats section, graphs, context docs, license notices, and guiding metaphor are generated-secondary documentation/review surfaces only; they do not certify semantic truth and do not bypass expert review.
