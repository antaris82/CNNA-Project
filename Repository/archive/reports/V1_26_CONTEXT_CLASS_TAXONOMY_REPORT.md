# V1.26 Context-class taxonomy report

## Scope
V1.26 adds an object-oriented context/class layer above the existing phase and object status logic. The correction is intentionally structural: **status** remains release/proof-state information, while **Context class** states what kind of row is being represented.

This prevents a green tool/database/generated/reference row from being read as a green Lean object, and it prevents Lean-facing contracts/refactors/governance rows from being mistaken for mathematical CNNA data.

## Core changes

- Added a required `Context class` field to every phase row and every object row in `masters/cnna_roadmap_master.yaml`.
- Added the top-level `context_class_taxonomy` section and rendered it before the object and phase registers.
- Added Phase `20.27` as the closed tooling/schema phase for the context-class taxonomy.
- Added Object `DBR27` as the generated-secondary planning/tool object for the taxonomy.
- Added proof dossier `proof:DBR27` and a scratchpad record for Phase `20.27`.
- Added guardrail `GNG38`: status/context orthogonality and Lean-facing subclass separation.
- Added code-audit record `SCF57`, format-decision record, workflow-policy record, and latest-change overview entry.
- Updated generated tables so phase, object, proof-dossier, scratchpad, and module-manifest views visibly carry `Context class`.

## Phase classes

Current phase classes:

- `LeanDerivationPhase`
- `LeanRefactorPhase`
- `LeanGovernancePhase`
- `ReferenceGatePhase`
- `ToolInfrastructurePhase`
- `DatabaseMirrorPhase`
- `GeneratedArtifactPhase`
- `DocumentationPhase`
- `BaselinePhase`

## Object classes

Current object classes:

- `LeanSourceObject`
- `LeanTargetObject`
- `LeanRefactorObject`
- `LeanHandoffContractObject`
- `LeanGovernanceObject`
- `GovernancePolicyObject`
- `ReferenceGateObject`
- `ToolInfrastructureObject`
- `DatabaseMirrorObject`
- `GeneratedArtifactObject`
- `DocumentationObject`

The second-pass audit was important: names such as `WeightPolicy.lean` must not automatically turn a mathematical Lean object into a governance object. `G02` and `S07` were therefore kept/returned to `LeanSourceObject`, while Handoff/Input rows such as `H00` and `B00` were classified as `LeanHandoffContractObject`.

## Validation

- `python3 scripts/generate_tables.py` succeeded.
- Generated table counts: 236 phases, 240 objects, 236 scratch-pad records, 240 proof-dossier records.
- Full A3 PDF compilation succeeded.
- Final PDF length: 661 pages.
- Spot-rendered pages checked: context-class taxonomy, object table area, phase/object areas, final module-implementation manifest area.
- No Lean source file was modified.
- No Lean build was run or claimed.

## Known uncertainty / follow-up

Existing long filenames and module/report paths still produce non-fatal LaTeX overfull-box warnings in some generated tables. They are layout warnings in generated documentation, not evidence of a Lean/provenance error. A later PDF table-layout phase could shorten report-name rendering or introduce path wrapping.
