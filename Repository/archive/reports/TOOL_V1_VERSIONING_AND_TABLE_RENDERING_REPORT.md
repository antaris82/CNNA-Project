# Tool V1.0 versioning and table rendering report

This update addresses the five user-reported planning-tool issues before continuing with Phase 1.1.1.2.

## Closed static findings

- SCF27: uniform table legends were missing before every table; closed by generator-level table legend emission.
- SCF28: tool-version and data-snapshot version were conflated; closed by `tool_version: V1.0` plus timestamped `data_timestamp` / `data_version`.
- SCF29: the old front-matter `Essential findings` section duplicated issue tracking; closed by removing that section from the new main PDF and placing actionable items in Section 2.
- SCF30: the complete Lean module catalog could visually overflow from the Module column into Group; closed by adding dotted-name breakpoints and adjusting catalog widths.
- SCF31: Object table A IDs were anchors but not clickable links; closed by making the visible ID text link to the object's proof dossier while preserving row anchors.

## Scope

No Lean source file was edited. The change is restricted to the YAML master, the table generator, generated tables/exports, and the compiled PDF artifact.
