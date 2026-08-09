# Traceability and reading convention

## Three coordinates, one scientific object

Every scientific node is identified by three distinct coordinates, which must not be conflated:

1. **Canonical node number** `NNN`, for example `001`. This is the stable global presentation label and follows the canonical derivation order.
2. **Semantic node ID**, for example `I001` or `C001`. This identifies the scientific owner of a definition, construction, theorem, control, or obstruction.
3. **Current section path**, for example `1.1.1`. This records only the node's present location in the document hierarchy. It may change when a section is inserted or reorganized.

The visible node label is therefore `NNN · ID`, for example `001 · I001`. The section path is deliberately excluded from that label. Consequently, inserting a new section can change `1.1.1` without changing either `001` or `I001`.

## One DAG and its document projections

`derivation/registry/dag/NODES.tsv` and `derivation/registry/dag/EDGES.tsv` are the canonical semantic graph. The yEd Live GraphML is the canonical visual layout of the same graph. Main-paper sections, supplementary sections, directory indices, and code-anchor tables are generated projections; none of them constitutes a second DAG.

For each node, `derivation/registry/nodes/<ID>.json` records its canonical number, semantic ID, current section path, documentation tier, incoming and outgoing ownership, document artifacts, and code anchors.

## Directory correspondence

The final directory component for a node has the stable form

```text
NNN_ID__descriptive_slug
```

For example:

```text
001_I001__branching_parameter_b
```

The parent directories encode the current section hierarchy. They may change if the paper is reorganized; the final node-directory component remains tied to `NNN · ID`.

The main-paper and supplementary paths are mirrored:

```text
derivation/paper/main/sections/<section parents>/NNN_ID__slug/SECTION.tex
derivation/supplement/sections/<section parents>/NNN_ID__slug/DOCUMENTATION.md
```

## Relation to Python and Lean

The semantic ID is the authoritative join key between the DAG, prose, Python, and Lean.

Python modules use a local module-order prefix and the lower-case semantic ID:

```text
sKK_id__descriptive_slug.py
```

Lean modules use the corresponding local module-order prefix and the upper-case semantic ID:

```text
SKK_ID_DescriptiveName.lean
```

Here `KK` is the order inside the current code section. It is not the canonical node number `NNN`. A reader must therefore not infer the scientific identity from `S01`, `S02`, and so forth alone.

The exact cross-layer lookup is provided by `derivation/registry/documentation/CODE_ANCHORS.tsv`. Each code anchor contains:

- node number and semantic ID;
- source layer and role;
- exact source path;
- declaration or function symbol;
- declaration kind;
- start and end lines;
- exact source SHA-256.

The symbol plus source hash is the stable code identity. Line numbers are a direct reading aid and must be regenerated after any source edit.

## Documentation tiers and completion state

The per-node tier `D0`, `D1`, or `D2` specifies the required depth: atomic definition, structural construction, or full proof dossier.

A node is marked `COMPLETE_V2` only when its main-paper text, supplementary dossier, countercheck, code anchors, artifact hashes, and validation gates agree. Nodes are read in canonical node order.

## Reproducible lookup procedure

From a DAG node to the scientific text and code:

1. Read `NNN · ID` from the node.
2. Locate `ID` in `NODES.tsv` or `NODE_TRACEABILITY_INDEX.tsv`.
3. Open the registered main-paper or supplementary artifact.
4. Filter `CODE_ANCHORS.tsv` by `ID` to obtain exact Python and Lean symbols, line intervals, and source hashes.
5. Verify the theorem or implementation status in `derivation/registry/nodes/<ID>.json` and the relevant build or axiom audit.

From a code declaration back to the DAG:

1. Use the semantic ID in the module name when present.
2. Confirm the source path and symbol in `CODE_ANCHORS.tsv`.
3. Follow the matching row to `NNN · ID`, the current section path, and the node record.

This correspondence separates scientific identity from mutable editorial placement and from local implementation ordering. It is the basis for all D0, D1, and D2 documentation.
