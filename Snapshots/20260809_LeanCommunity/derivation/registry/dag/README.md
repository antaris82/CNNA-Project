# Canonical CNNA DAG - G2 centred labels and separated edge routes

`NODES.tsv` and `EDGES.tsv` are the only normative graph tables. The graph contains 145 substantive nodes and 401 preserved edges. Current IDs are prefix-free (`I001`, `C001`, `P001`); yEd labels use `node_number · ID`.

G2 rendering rules:

- `derivation_rank` fixes the vertical level; the graph runs strictly from top to bottom;
- the visible origin is `I001`, `I002`, `C001`, ordered as branching parameter, finite depth, and empty carrier;
- nodes from one `section_group_title` form a contiguous horizontal block at each rank;
- same-rank proof gates form a contiguous cluster with their proof owner;
- all proof-certification links remain dashed, non-constraining links in this same graph;
- status uses fill colour only; node role uses shape and border only;
- every node label is horizontally and vertically centred with yEd's internal centre model;
- every edge receives a distinct source port, target port, and inter-rank horizontal lane;
- nonlocal dependencies are routed through deterministic outer gutters;
- exact collinear segment overlap is forbidden and audited;
- edge segments may cross at isolated points, but may not share a segment or traverse an unrelated node body;
- only current-node and current-edge relation labels are visible by default; every relation remains available as GraphML metadata.

Generated projections and evidence:

- `DAG_yEd.graphml`: the single yEd Live graph;
- `G2_AUDIT.json`: centring, overlap, grouping, routing, encoding, and owner-locality gates;
- `SECTION_HIERARCHY.tsv`, `SECTION_TRANSITIONS.tsv`, and `SECTION_DIRECTORY_INDEX.tsv`: G1 projections of the same `NODES.tsv`.

No visualization node or layout edge has been added to the semantic DAG.

## Canonical visual layout

`DAG_yEd.graphml` is the editor-owned yEd Live layout. Automated registry tools
must preserve its geometry, hierarchy, bend points, styles, and centred label
placement. `render_yed_dag.py` is a guard and no longer performs a relayout.
Semantic changes remain governed by `NODES.tsv` and `EDGES.tsv`; compatible
metadata may be inserted into the GraphML without moving the graph.
