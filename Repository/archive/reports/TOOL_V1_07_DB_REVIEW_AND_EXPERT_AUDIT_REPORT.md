# Tool V1.07 DB-REVIEW and expert-audit update

## Scope

This update adds DB-REVIEW as a first-class main side objective in the CNNA planning/documentation tool. It is a documentation, review, and future database-readiness objective only. No Lean source file was changed.

## Core semantic rule

The checked Lean code remains the primary truth system. Generated artifacts such as YAML-derived tables, PDFs, TSV exports, DOT graphs, future databases, and online/interactive views are secondary documentation and review surfaces.

A green Lean build proves formal consistency with respect to the chosen declarations and definitions. It does not by itself guarantee semantic correctness of modeling choices, interpretations, or established-theory links. Nothing is declared infallible or 100 percent secured. Every relevant claim remains subject to discipline-specific expert review.

## Added planning structure

- Added Phase `20` as `DB-REVIEW main side objective`.
- Added child phases:
  - `20.1` immediate epistemic expert-review rule and no-infallibility maxim
  - `20.2` Master-YAML database schema preparation and round-trip-safe identifiers
  - `20.3` discipline-separated expert-review matrix
  - `20.4` blue/reference-theory marking audit backlog
  - `20.5` interactive/online database-backed documentation views
- Added direct objects `DBR0` through `DBR5` and matching proof-dossier rows.
- Added scratchpad rows for all new phases.

## Added global guardrails

- `GNG23`: no 100-percent truth declaration and no bypass of discipline-specific expert review.
- `GNG24`: no ignored missing blue/reference-theory marking.

## Added workflow/tooling updates

- Added `DB-REVIEW database-ready documentation and expert-review workflow`.
- Added `SLTG-06` as a secondary long-term goal with immediate-principles semantics.
- Added implementation-scaling rows `1.1.1.5.8` and `1.1.1.5.9` for later database schema/export work.
- Added review/audit status legend rows: `review-required`, `blue-audit-needed`, `lean-primary`, `generated-secondary`.
- Updated `scripts/generate_tables.py` so phase status validation includes `O` consistently with the phase legend/check policy, and so the secondary-goals paragraph permits immediate-principles side objectives.

## Verification performed here

- Regenerated all generated tables and TSV exports from `masters/cnna_roadmap_master.yaml` using `scripts/generate_tables.py`.
- Regenerated the V1.07 PDF from the updated tables.
- Rendered representative PDF pages, including the latest-change section and new Phase 20/DB-REVIEW pages, for a basic PDF spot-verification pass. A full-page render was started but timed out after 92 pages in this environment; LaTeX compilation itself completed successfully.

## Lean status

No Lean source was edited and no Lean build success is claimed by this update.
