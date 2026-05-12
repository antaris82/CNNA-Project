# V1.12 semantic module consolidation audit report

## Scope

This V1.12 update creates a pre-substantive audit gate, not a Lean refactor. The goal is to decide where semantically related modules can be consolidated without reducing proof/provenance auditability.

Authoritative planning source: `masters/cnna_roadmap_master.yaml`.

Lean source status: no Lean source file was edited.

## Existing phase coverage

The earlier tool already had partial coverage:

- `1.1.1.1.1` module manifest and semantic placement gate
- `1.1.1.1.2` reuse/duplication audit and canonical generator policy
- `1.1.1.1.4` declaration consumption classification map
- `19.1` long-term existing-code documentation coverage

Missing piece: a dedicated gate for semantic module consolidation / no-merge classification before new substantive code. V1.12 adds it as active Phase `1.1.1.1.5` with object `LEG36`.

## Initial code findings

### High-confidence consolidation candidates

| Cluster | Files inspected | Reason | Required safeguard |
|---|---|---|---|
| BoundarySource substrate ledger clones | `BoundaryStateSubstrate.lean`, `BranchAddressSubstrate.lean`, `HistoryExpandedSubstrate.lean`, `InterfaceExposureSubstrate.lean` | Same import, same ledger projection pattern, same status/blocker/obligation theorem pattern, same AR2b1 wrapper structure with only candidate-kind/name variation. | Introduce one canonical candidate-ledger schema only if old modules remain as facades initially. |
| Handoff A-to-C/D/E output aliases | `A_to_C.lean`, `A_to_D.lean`, `A_to_E.lean` | Each is a `SectorExportStrong` alias with identical `ofSectorExport` and `exportData` pattern. | Preserve pillar-specific names and import paths; candidate canonical module would be an alias/facade layer. |
| Handoff B/C/D/E-to-A input wrappers | `B_to_A.lean`, `C_to_A.lean`, `D_to_A.lean`, `E_to_A.lean` | Same source/feedback structure, same ext proof, same handoff projection; only pillar direction name differs. | A generic feedback-input schema is plausible, but old direction-specific structures must remain visible until migration is build-proved. |

### Explicit no-merge-until-proven families

| Cluster | Reason |
|---|---|
| `Arithmetic/Smoke/GeneratedInterior*`, `Operational*`, `SM*` chains | These modules encode proof-stage and implementation-history provenance. Similar names or boilerplate do not prove semantic equivalence. |
| `Structural/CayleyDickson/S6*` chain | The many small modules likely represent staged proof duties and should not be flattened without a canonical proof module that preserves the duty structure. |
| `Arithmetic/Notation.lean` | Very large facade/notation surface. This is a compactness issue, but probably a split/facade-normalization question rather than a merge question. |

## New governance records

- Phase: `1.1.1.1.5`
- Object: `LEG36`
- Guardrail: `GNG26`
- Reuse/duplication row: `RD08`
- Static findings: `SCF43`, `SCF44`, `SCF45`
- Workflow: `Semantic module consolidation and compatibility-preserving refactor workflow`
- Context profile: `module-consolidation`

## Exit criterion for actual code consolidation

A later Lean refactor may close only if it records:

1. exact candidate cluster and natural source layer;
2. old-module facade or explicit migration plan;
3. import graph delta;
4. declaration/consumer delta;
5. local full-build evidence;
6. proof that semantic/provenance auditability is preserved or improved.

