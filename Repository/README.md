# CNNA Planning and Documentation Tool

This package contains the current CNNA planning/documentation tool, a fixed Lean source snapshot, and the root Lean/Lake build-entry files needed for local work.

The tool makes a large formal project reviewable, queryable, documentable, and workflow-driven without turning documentation into a second truth system.

## Current snapshot

- Tool infrastructure version: **V1.34**
- Planning data version: **P1.40**
- Lean data timestamp: **2026-05-10T05:51:42+02:00**
- Lean source snapshot: `Repository/repo_snapshot/CNNA`
- Authoritative planning source: `Repository/masters/cnna_roadmap_master.yaml`
- Root build entry: `CNNA.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`
- Root policy: keep only source/control files in the root: `README.md`, `.gitignore`, and the Lean/Lake build-entry files. Generated PDFs/TeX/LaTeX build products and historical reports are not retained as active root sources.

Current generated project facts at this snapshot:

- Lean source files: **288**
- Lean source lines: **89,602**
- registered Lean modules: **287**
- internal import edges: **724**
- missing internal import edges in the inventory: **0**
- detected declarations: **8,860**
- registered phases: **272**
- registered objects/quantities: **275**
- proof dossiers: **275**
- implementation scratchpad records: **272**
- global no-go guardrails: **67**

These counts are generated-secondary inventory facts. They help navigation and review; they are not semantic proof of correctness.

## Truth status and review discipline

The primary truth system is the Lean code. The Master YAML, TSV exports, PDFs, graphs, context slices, reports, and README are secondary views that organize and expose the project.

A green Lean build proves formal consistency relative to the selected definitions. It does not by itself prove that the definitions, interpretations, theory attachments, or generated documentation are semantically infallible. Every relevant claim remains subject to discipline-specific expert review.

Blue/reference-theory material is comparison and review context, not CNNA input. Missing blue markings are audit debt.

P1.40 audits the workflow-policy surface for currency, consistency and coherence. It preserves the P1.39 GitHub/Webhosting/MySQL automation model, but clarifies the state machine: absent build evidence is not red or green; verified red builds are visible failure-history snapshots plus natural-origin repair phases without current production swap; verified green builds close phases only with complete evidence and advance exactly one active cursor. It also aligns closeout with timestamp-bounded delta-PDF output and threads CEX16 red-failure history through API/deployment dependencies. This is planning/tooling documentation only; no Lean source changed in this package.

## Repository layout

```text
./
  README.md
  CNNA.lean                         # top-level compatibility entry
  lakefile.lean                     # Lake package; srcDir := "Repository/repo_snapshot"
  lake-manifest.json                # dependency lock file
  lean-toolchain                    # Lean toolchain pin
  Repository/
    masters/
      cnna_roadmap_master.yaml      # single planning/documentation master
    scripts/
      generate_tables.py            # YAML -> TSV/TeX/generated views
      generate_full_document.py      # full documentation on demand
      generate_context_doc.py        # context-filtered documentation slices
      build_export_script_v1.8.py    # Lean module/import inventory scan
      clean_generated_root_artifacts.py
    generated_exports/              # generated TSV/JSON-style views
    tables/                         # generated TeX table fragments
    figures/                        # generated graph DOT/PDF fragments
    repo_inventory/raw_export/       # generated Lean module/import/declaration inventory
    repo_snapshot/CNNA/              # fixed Lean source snapshot
    context_docs/                    # generated context documentation slices
    archive/reports/                 # historical reports and tool-change evidence
```

The package is source-oriented. Full PDFs, TeX wrappers, and LaTeX build products are disposable outputs and can be regenerated.

## Manual Lean/Lake use

The root Lean/Lake files are retained so local builds can be run from the package root:

```bash
lake build
```

The `lakefile.lean` defines the `CNNA` library with:

```lean
srcDir := "Repository/repo_snapshot"
```

So the maintained Lean source tree remains:

```text
Repository/repo_snapshot/CNNA/
Repository/repo_snapshot/CNNA.lean
```

The root `CNNA.lean` is only a compatibility entry. It is intentionally not the Lake source root. Direct `lean CNNA.lean` from the package root may require an explicit `LEAN_PATH` including `Repository/repo_snapshot`.

The supplied toolchain pins Lean to:

```text
leanprover/lean4:v4.28.0
```

The manifest locks mathlib at input revision `v4.28.0`.

## Manual documentation use without ChatGPT

Run commands from the package root unless stated otherwise.

### Regenerate the planning tables and exports

```bash
cd Repository
python3 scripts/generate_tables.py
```

This reads `masters/cnna_roadmap_master.yaml` and regenerates `generated_exports/` and `tables/`.

### Generate the full PDF documentation

```bash
cd Repository
python3 scripts/generate_tables.py
python3 scripts/generate_full_document.py --compile
```

Output is written to:

```text
generated_docs/full/
```

If `pdflatex` is missing, the TeX/view artifacts can still be generated, but PDF compilation will fail.

### Generate context-filtered documentation

A context document preserves the large documentation section structure, but includes only rows relevant to the requested topic.

Example: DtN Matrix documentation.

```bash
cd Repository
python3 scripts/generate_tables.py
python3 scripts/generate_context_doc.py "DtN Matrix" --profile dtn-matrix --slug dtn_matrix
```

Output is written to:

```text
context_docs/dtn_matrix/
```

The output contains:

- `context_filter_manifest.json`
- `context_section_summary.tsv`
- `matched_rows/*.matched.tsv`
- `<slug>_context_documentation.tex`
- `<slug>_context_documentation.pdf` if LaTeX compilation succeeds

Another available profile is:

```bash
python3 scripts/generate_context_doc.py "Module Consolidation" --profile module-consolidation --slug module_consolidation
```

Use `--full-pdf` only when a very large context PDF is acceptable. By default, the PDF caps rows per section and exports the full matched row sets as TSV.

### Refresh the Lean module/import inventory

```bash
python3 Repository/scripts/build_export_script_v1.8.py
```

Default paths:

- Lean repo root: `Repository/repo_snapshot`
- Lean source root: `CNNA`
- inventory output: `Repository/repo_inventory/raw_export`

Equivalent explicit command:

```bash
python3 Repository/scripts/build_export_script_v1.8.py \
  Repository/repo_snapshot \
  --source-root CNNA \
  --output-dir Repository/repo_inventory/raw_export
```

After refreshing the inventory, regenerate tables:

```bash
cd Repository
python3 scripts/generate_tables.py
```

### Clean disposable root artifacts

```bash
cd Repository
python3 scripts/clean_generated_root_artifacts.py --apply
```

The cleanup policy preserves the root source/control files: `README.md`, `CNNA.lean`, `lakefile.lean`, `lake-manifest.json`, and `lean-toolchain`. It removes or archives only disposable generated documentation artifacts and historical root reports.

## Use together with ChatGPT

This package has been developed and tested with **ChatGPT** as the assistant-side workflow instantiator. It has not been developed or tested as an integrated Claude workflow. Claude or other systems may still be used externally for discussion or independent review, but this README does not claim them as validated toolchain components.

The intended ChatGPT workflow is:

1. Upload the current full tool zip.
2. Give a bounded task, for example:
   - `Prüfe die Implementierbarkeit der nächsten zusammenhängenden Schritte.`
   - `Erstelle die Kontextdoku zur DtN Matrix.`
   - `Schließe die grüne Phase im Plan und aktualisiere die Doku.`
   - `Prüfe semantisch zusammengehörige Module auf Merge-/No-Merge-Kandidaten.`
   - `Füge einen neuen Workflow für <task> hinzu.`
3. ChatGPT inspects the current package, modifies the appropriate source files, regenerates generated views when needed, and returns a full updated zip.
4. Lean builds are checked locally by the user. The assistant must not claim a Lean build unless it actually ran one in the working environment.
5. Build errors, semantic objections, or expert-review feedback can be fed back into ChatGPT as the next bounded task.

The value of the tool is not only the static documentation. The main value is the standardized workflow layer over the project state: the tool makes it possible to repeatedly instantiate the same review, planning, documentation, feasibility-check, and closeout operations without reinventing the method each time.

## Core workflows

### 1. Implementability dry run

Purpose: test the next connected implementation steps before writing substantial new Lean code.

The workflow performs a thought-experiment implementation along the dependency chain. If a required object, proof bridge, module seam, or consumer contract is missing, the tool should not patch it at the consumer. It should create or refine an upstream addressing phase at the natural emergence layer of the missing structure.

This is the current gate before new substantial content work.

### 2. Phase closeout after a green local build or verified green CI

Purpose: update the planning state after the user reports a successful local Lean build or after the CI controller receives verified green evidence for the active phase.

Typical actions:

- mark the completed phase green only if the required evidence is present
- update object/proof-dossier/scratchpad records
- advance the active cursor
- record remaining semantic or expert-review debt
- generate only the necessary context documentation unless a full document is explicitly needed

### 3. Red Lean build repair backjump

Purpose: make failed Lean builds structurally actionable instead of leaving the plan in an ambiguous state.

Typical actions:

- keep the failed branch unmerged and block deployment/import
- mark the attempted active phase red
- record failing modules/log references and the exact commit/run metadata
- create or activate a predecessor repair phase at the natural source layer
- add scratchpad and proof-dossier stubs for that repair phase
- make the repair phase the unique active follow-up when its dependencies are known

This is a provenance-preserving repair route, not a license to patch downstream consumers blindly.

### 4. Context documentation generation

Purpose: produce a focused review packet for one topic while preserving the document topology.

Example request:

```text
Erstelle die Doku zur DtN Matrix.
```

The generated context document should include all major sections, but only entries relevant to DtN. This is scalable because the same generator can instantiate review packets for objects, modules, phases, mathematical themes, or expert-review scopes.

### 5. Expert-review dossier preparation

Purpose: prepare an object or quantity so a specialist can compare it against established theory.

The generated packet should separate:

- CNNA object ID and provenance path
- Lean/module location
- definition and intended role
- proof target and proof sketch
- established-theory reference context
- blue/reference markings
- open review questions

This does not import the established theory as CNNA input. It makes comparison and expert review possible.

### 6. Semantic module consolidation audit

Purpose: identify module families that should be merged, wrapped, or kept separate before new substantial code is added.

Merge is allowed only if semantic content is preserved or clarified. Proof-stage chains, generated SM chains, and Cayley-Dickson phase chains must not be flattened merely because they look repetitive; their file boundaries may carry provenance and proof order.

### 7. Source/theory ingestion workflow

Purpose: process external mathematical or physical theory as reference material.

The workflow should extract definitions, comparison targets, standard theorems, and review obligations. It must keep them comparison-only unless a CNNA-derived construction later proves the corresponding object internally.

### 8. Root/documentation/build-entry hygiene workflow

Purpose: keep the package clean, reproducible, and locally buildable.

Generated PDFs, TeX wrappers, and LaTeX build products are not retained in the root. Reports belong in `Repository/archive/reports/`. Active planning state belongs in the Master YAML, scripts, generated exports, repo inventory, and Lean source snapshot.

The root Lean/Lake files are a special source/control exception: they are retained because they define the local build entry and toolchain lock.

## Workflow scalability

Workflows are not fixed forever. They are part of the tool surface and can be added, split, tightened, or retired as the project grows.

A new workflow should usually add or update:

- a `workflow_policy` row in the Master YAML
- a phase or side-objective entry if it changes governance or generated behavior
- object/proof-dossier/scratchpad records when it introduces a tracked tool object
- a script or context profile if the operation should be repeatable
- README text if users need to run or request it directly

This is where the tool’s real scaling value lies. It turns repeated CNNA work into reproducible operations over a single state model: feasibility checks, context documentation, object dossiers, module inventories, blue-object review, phase closeouts, and later database-backed exploration can all be instantiated from the same Master YAML and generated views.

## Database and interactive-map vision

The Master YAML is currently the maintained planning source. Long term, its information should be representable in a database or graph layer so phases, objects, modules, handoffs, status colors, theory links, proof dossiers, and review obligations can be queried, visualized, shared, and explored online.

The vision is an interactive, zoomable CNNA map: from pillars and phases down to individual objects, modules, declarations, proof dossiers, and expert-review packets. This would be a database-backed interface over the Lean-primary source space, not a replacement for it.

The database has no immediate priority over the active Lean/content path. The current YAML structure is being kept database-ready so this transition remains possible later.

## Tool-interface principle

The tool is an interface for making a local project slice visible. The active phase is the bright object. The remaining Lean code, open dependencies, unreviewed theory references, and unaudited semantics form the complementary space. The Master YAML, object register, proof dossiers, graphs, context slices, and future database views form the interface layer.

This is an operational metaphor for tool use. It is not a CNNA theorem and not an ontic input.

## Licenses

Project-authored documentation, prose, generated reports, and PDFs are under **Creative Commons Attribution 4.0 International (CC BY 4.0)**.

Project-authored Lean code, Python scripts, and other source/tool code are under the **MIT License**.

Third-party dependencies, upstream libraries, and quoted/reference material retain their own licenses and rights.

## Current active gate

The active mathematical/content cursor remains:

```text
1.1.1.1.5 — Semantic module consolidation audit and compatibility-preserving merge/no-merge gate
```

Phase `1.1.1.2` is implementable after this gate closes. New substantial Lean code should not start before the consolidation audit is addressed.

