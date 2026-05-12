# Phase 1.1.1.1.5.1 - Notation surface consumption audit report

## Result

Phase `1.1.1.1.5.1` is closed as an audit/ledger gate. It does not move, delete, or rewrite Lean code.

- Notation files inspected: **14**
- Notation files with extracted surfaces: **13**
- Import-only notation files: **1** (`repo_snapshot/CNNA/Notation.lean`)
- Extracted surfaces: **1156**
- Declaration/surface kinds: **{'abbrev': 849, 'def': 107, 'theorem': 176, 'scoped notation': 24}**
- Rows with direct consumers outside Notation.lean: **484**
- Rows without direct consumers outside Notation.lean: **672**
- Classification counts: **{'legacy_phase_alias_candidate': 196, 'consumed_internal_helper': 484, 'unconsumed_domain_alias_candidate': 399, 'unconsumed_symbol_surface_candidate': 17, 'unconsumed_umbrella_alias_candidate': 60}**

The row-level evidence is exported to:

- `Repository/generated_exports/notation_surface_consumption_cleanup_ledger.generated.tsv`
- `Repository/generated_exports/notation_surface_consumption_cleanup_evidence.generated.json`

## Interpretation

The audit is intentionally conservative. A row without direct consumer evidence is not automatically wrong, but it is not allowed to become neutral public API by inertia. It must be handled by the next phase as one of: explicit keep as intentional public facade, quarantine under legacy/phase alias surface, rename to a neutral surface, or remove after compatibility planning and local build evidence.

The largest risk surface is `CNNA/PillarA/Arithmetic/Notation.lean`, which contains many phase-semantic AR* aliases and proof-stage wrappers. These may be useful as transitional review handles, but they are not neutral API names by default.

## File-level summary

| File | consumed_internal_helper | legacy_phase_alias_candidate | unconsumed_domain_alias_candidate | unconsumed_symbol_surface_candidate | unconsumed_umbrella_alias_candidate | total |
|---|---:|---:|---:|---:|---:|---:|
| `repo_snapshot/CNNA/Notation.lean` | 0 | 0 | 0 | 0 | 0 | 0 |
| `repo_snapshot/CNNA/PillarA/Arithmetic/Notation.lean` | 409 | 196 | 298 | 0 | 0 | 903 |
| `repo_snapshot/CNNA/PillarA/Closure/Notation.lean` | 4 | 0 | 1 | 0 | 0 | 5 |
| `repo_snapshot/CNNA/PillarA/Coupling/Notation.lean` | 2 | 0 | 0 | 0 | 0 | 2 |
| `repo_snapshot/CNNA/PillarA/DtN/Notation.lean` | 3 | 0 | 9 | 0 | 0 | 12 |
| `repo_snapshot/CNNA/PillarA/Finite/ExecSpectral/Notation.lean` | 0 | 0 | 6 | 0 | 0 | 6 |
| `repo_snapshot/CNNA/PillarA/Finite/Notation.lean` | 0 | 0 | 34 | 0 | 0 | 34 |
| `repo_snapshot/CNNA/PillarA/Foundation/Notation.lean` | 4 | 0 | 25 | 12 | 0 | 41 |
| `repo_snapshot/CNNA/PillarA/Geometry/Notation.lean` | 2 | 0 | 10 | 0 | 0 | 12 |
| `repo_snapshot/CNNA/PillarA/Handoff/Notation.lean` | 2 | 0 | 8 | 0 | 0 | 10 |
| `repo_snapshot/CNNA/PillarA/Network/Notation.lean` | 5 | 0 | 0 | 0 | 0 | 5 |
| `repo_snapshot/CNNA/PillarA/Notation.lean` | 42 | 0 | 0 | 0 | 60 | 102 |
| `repo_snapshot/CNNA/PillarA/Sectors/Notation.lean` | 7 | 0 | 0 | 0 | 0 | 7 |
| `repo_snapshot/CNNA/PillarA/ToC/Notation.lean` | 4 | 0 | 8 | 5 | 0 | 17 |

## Closure decision

`LEG42` is closed as a generated governance/refactor ledger. The active cursor advances to `1.1.1.1.5.2`, where the ledger must be consumed to build the neutral module-name and facade migration map (`LEG38`).

No full module/declaration/object mirror is certified by this phase. No Explorer/API/UI readiness is implied.

## Method and limitations

- Extraction covered Lean lines beginning with `abbrev`, `def`, `theorem`, `lemma`, `scoped notation`, or `notation` inside `CNNA/**/Notation.lean`.
- Consumer evidence was collected by static identifier/token search over `repo_snapshot/CNNA/**/*.lean`, excluding the defining line and separating hits in other `Notation.lean` files from hits in ordinary Lean modules.
- This is a static governance audit, not an elaborator-level dependency proof. It can undercount semantic consumption through namespace exports or imported umbrella modules and can overcount textual hits in non-consumer proof scaffolding. Ambiguous rows require manual review in `1.1.1.1.5.2`.
- No Lean source changed; no Lean build was run or claimed.
