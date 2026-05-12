# V1.35 REALOQS legacy AQFT scan and CNNA migration disposition report

Status: planning/reference integration only. No CNNA Lean code was changed and no Lean build was run.

## Source

- Archived source: `archive/source_materials/REALOQS_v0.0605_stable.zip`
- Scan data: `archive/reports/V1_35_REALOQS_LEGACY_AQFT_SCAN_DATA.json`
- Module TSV: `archive/reports/V1_35_REALOQS_LEGACY_AQFT_MODULE_SCAN.tsv`

## Static scan summary

| Scope | Files | Lines | Declarations | noncomputable files | files with @[simp] | sorry/admit/axiom hits |
|---|---:|---:|---:|---:|---:|---:|
| All REALOQS | 270 | 26177 | 1727 | 116 | 81 | 0 |
| PillarB | 88 | 12411 | 680 | 36 | 41 | 0 |
| PillarB/AQFT | 62 | 11285 | 596 | 35 | 40 | 0 |
| PillarB/Gates | 21 | 910 | 73 | 0 | 1 | 0 |
| Meta/PillarB | 18 | 903 | 51 | 16 | 6 | 0 |

## AQFT category map

- **AQFT Foundations**: 5 files, 509 lines, 45 declarations, 0 noncomputable files, 5 files with @[simp].
- **Local nets and HK support**: 4 files, 344 lines, 34 declarations, 0 noncomputable files, 1 files with @[simp].
- **HK gates**: 9 files, 447 lines, 39 declarations, 0 noncomputable files, 0 files with @[simp].
- **Quasi-local/GNS/KMS/Modular**: 8 files, 714 lines, 45 declarations, 0 noncomputable files, 5 files with @[simp].
- **Boundary-matrix derived layer**: 28 files, 7972 lines, 378 declarations, 28 noncomputable files, 24 files with @[simp].
- **TreeOfCliques/FromA examples**: 5 files, 1261 lines, 65 declarations, 5 noncomputable files, 4 files with @[simp].
- **PillarB meta/audit**: 18 files, 903 lines, 51 declarations, 16 noncomputable files, 6 files with @[simp].

## Disposition

The legacy AQFT code is advanced enough to be valuable, but it is not compatible with direct CNNA import. It is therefore integrated as reference/migration evidence only. Required follow-up ledgers are RLC0-RLC8 under phase block 23.

Main reasons direct copy is blocked:

1. The current CNNA PillarB must consume only explicit A->B handoff data, while legacy code often imports old A-side interfaces/config/TreeOfCliques harnesses.
2. The legacy BoundaryMatrix derived layer is noncomputable-heavy and often uses simplification attributes that are forbidden or highly restricted in CNNA operational paths.
3. Names such as HK gates, KMS, GNS, modular data, split property and quasi-local closure are useful target gates, but their appearance in legacy code is not a CNNA-derived closure proof.
4. Examples and Meta/PillarB files are quarantine/regression sources, not implementation sources.

## Planning integration

Added phases 23.0-23.8, objects RLC0-RLC8, guardrails GNG51-GNG54, crosscheck rows REALOQS-01..08 and static findings SCF64-SCF67.
