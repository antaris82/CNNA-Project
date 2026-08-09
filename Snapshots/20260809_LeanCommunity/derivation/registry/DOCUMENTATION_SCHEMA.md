# CNNA node documentation schema

Schema id: `cnna-node-documentation-v2`.

## Authority and ordering

The canonical node record `derivation/registry/nodes/<ID>.json` stores the documentation tier, required sections, code anchors, countercheck obligation, and completion state. `NODES.tsv` mirrors the fields needed for global ordering and audit. `DOCUMENTATION_TIERS.tsv`, `CODE_ANCHORS.tsv`, and `DOCUMENTATION_COVERAGE.tsv` are generated projections, not parallel DAGs.

Every node is documented in `derivation_order`. The same sequence governs the DAG, main-paper section, supplement section, registry record, and code-anchor display.


## Stable node identity versus mutable section placement

Every node is displayed as `NNN · ID`. `NNN` is the canonical three-digit node number in derivation order; `ID` is the semantic ownership identifier. The hierarchical `section_path` is a separate, mutable placement coordinate and must not appear as part of the node identity. Main-paper and supplementary node headings are unnumbered and use `NNN · ID`; the current section path is displayed only as metadata.

The final node-directory component is `NNN_ID__slug`. Python and Lean `Sxx` prefixes are local module-order coordinates, not canonical node numbers. Exact cross-layer navigation is performed by semantic ID through `NODE_TRACEABILITY_INDEX.tsv` and `CODE_ANCHORS.tsv`.

## Common logical spine (all tiers)

Every node must make the following chain visible, with depth determined by its tier:

1. Position in the derivation.
2. Definition or formal statement.
3. Reason for introduction at this exact point.
4. Construction or proof method.
5. Countercheck, boundary case, or necessity test.
6. Result and exact scope.
7. Downstream handoff.
8. Python/Lean code anchors with file, symbol, line range, and SHA-256.

A node is not documentation-v2 complete merely because legacy prose exists. Existing v1 material is marked `V1_CONTENT_PRESENT_MIGRATION_REQUIRED` until it satisfies the tier-specific contract.

## Tier D0 - atomic input or definitional node

Compact but traceable. Required: exact definition; input/derived classification; admissible range or typing; why no hidden parameter is introduced; one definitional boundary/type-rejection check; result; downstream users; code anchors. No artificial proof narrative.

## Tier D1 - structural construction

Required in addition to the common spine: explicit construction; invariants; canonicity or uniqueness; boundary cases; Python/Lean semantic agreement; structural countercheck; result and handoff.

## Tier D2 - load-bearing theorem, proof owner, obstruction, or quarantine gate

Required: formal theorem/obstruction statement; hypotheses; proof strategy; explicit lemma chain; formal realization; counterexamples or necessity checks; axiom profile; code-line register; conclusion; remaining limits; downstream consequences. Internal lemma sequences remain dossiers inside the owning global DAG node and do not form a parallel DAG.

## Code-anchor stability

Every resolved anchor consists of path, symbol, declaration kind, start line, end line, and exact source SHA-256. Line numbers are presentation aids; symbol plus hash is the stable identity. Any source edit requires anchor regeneration.

## Completion states

- `NOT_STARTED`: no node prose under v2.
- `V1_CONTENT_PRESENT_MIGRATION_REQUIRED`: legacy content exists but has not passed v2.
- `DRAFT_V2`: all required headings exist but evidence remains open.
- `COMPLETE_V2`: all tier requirements, anchors, counterchecks, and status wording pass.
