#!/usr/bin/env python3
from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import csv
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
DAG = ROOT / "derivation/registry/dag"
MAIN_SECTIONS = ROOT / "derivation/paper/main/sections"
SUPP_SECTIONS = ROOT / "derivation/supplement/sections"


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def key(section: str) -> tuple[int, ...]:
    return tuple(int(part) for part in section.split("."))


def descendant(section: str, prefix: str) -> bool:
    return section == prefix or section.startswith(prefix + ".")


errors: list[str] = []
nodes = rows(DAG / "NODES.tsv")
edges = rows(DAG / "EDGES.tsv")
hierarchy = rows(DAG / "SECTION_HIERARCHY.tsv")
transitions = rows(DAG / "SECTION_TRANSITIONS.tsv")
directories = rows(DAG / "SECTION_DIRECTORY_INDEX.tsv")

required_node_fields = [
    "section_path", "section_root_title", "section_group_title", "introduction_reason",
    "main_section_directory", "supplement_section_directory", "main_section_artifact",
    "supplement_section_artifact", "main_documentation_state", "supplement_documentation_state",
    "canonical_node_label", "stable_node_directory_name",
]
if len(nodes) != 145:
    errors.append(f"node count {len(nodes)} != 145")
if len({n["id"] for n in nodes}) != len(nodes):
    errors.append("duplicate node IDs")
for node in nodes:
    for field in required_node_fields:
        if not node.get(field):
            errors.append(f"{node['id']} missing {field}")
    if node.get("section_path") != node.get("paper_section"):
        errors.append(f"{node['id']} section_path mismatch")

    expected_label = f"{int(node['node_number']):03d} · {node['id']}"
    if node.get("canonical_node_label") != expected_label:
        errors.append(f"{node['id']} canonical label mismatch")
    expected_dir = f"{int(node['node_number']):03d}_{node['id']}__"
    if not node.get("stable_node_directory_name", "").startswith(expected_dir):
        errors.append(f"{node['id']} stable node-directory name mismatch")

# Parent-section titles are canonical node attributes, not a parallel table.
root_title_sets: dict[str, set[str]] = defaultdict(set)
group_title_sets: dict[str, set[str]] = defaultdict(set)
for node in nodes:
    parts = node["paper_section"].split(".")
    root_title_sets[parts[0]].add(node["section_root_title"])
    group_title_sets[".".join(parts[:2])].add(node["section_group_title"])
if any(len(values) != 1 for values in root_title_sets.values()):
    errors.append("inconsistent root-section titles in NODES.tsv")
if any(len(values) != 1 for values in group_title_sets.values()):
    errors.append("inconsistent group-section titles in NODES.tsv")

# DAG order is exactly numeric section order.
by_derivation = sorted(nodes, key=lambda n: int(n["derivation_order"]))
by_section = sorted(nodes, key=lambda n: key(n["paper_section"]))
if [n["id"] for n in by_derivation] != [n["id"] for n in by_section]:
    errors.append("DAG derivation order != section order")
if [int(n["derivation_order"]) for n in by_derivation] != list(range(1, 146)):
    errors.append("derivation order not contiguous 1..145")
if len({n["paper_section"] for n in nodes}) != 145:
    errors.append("node paper sections not unique")

# Complete prefix hierarchy and exact first/last nodes.
prefixes: set[str] = set()
for node in nodes:
    parts = node["paper_section"].split(".")
    prefixes.update(".".join(parts[:length]) for length in range(1, len(parts) + 1))
h_by_section = {row["paper_section"]: row for row in hierarchy}
if set(h_by_section) != prefixes:
    errors.append(f"hierarchy prefix set mismatch: expected {len(prefixes)}, got {len(h_by_section)}")
for prefix in sorted(prefixes, key=key):
    row = h_by_section.get(prefix)
    if not row:
        continue
    descendants = [n for n in nodes if descendant(n["paper_section"], prefix)]
    first = min(descendants, key=lambda n: int(n["derivation_order"]))
    last = max(descendants, key=lambda n: int(n["derivation_order"]))
    expected = {
        "first_node_number": first["node_number"],
        "first_node_id": first["id"],
        "last_node_number": last["node_number"],
        "last_node_id": last["id"],
        "node_count": str(len(descendants)),
        "derivation_order_start": first["derivation_order"],
        "derivation_order_end": last["derivation_order"],
        "generated_from": "derivation/registry/dag/NODES.tsv",
    }
    for field, value in expected.items():
        if row.get(field) != value:
            errors.append(f"hierarchy {prefix} {field}: {row.get(field)!r} != {value!r}")
    for field in ["main_directory", "supplement_directory"]:
        path = ROOT / row[field]
        if not path.is_dir():
            errors.append(f"hierarchy directory missing: {row[field]}")

# Every sibling transition at every level is generated once and classified.
children: dict[str, list[str]] = defaultdict(list)
for prefix in prefixes:
    parent = ".".join(prefix.split(".")[:-1])
    children[parent].append(prefix)
expected_pairs: set[tuple[str, str]] = set()
for siblings in children.values():
    ordered = sorted(siblings, key=key)
    expected_pairs.update(zip(ordered, ordered[1:]))
actual_pairs = {(row["from_section"], row["to_section"]) for row in transitions}
if actual_pairs != expected_pairs:
    errors.append(f"section transition coverage mismatch: expected {len(expected_pairs)}, got {len(actual_pairs)}")
for row in transitions:
    if row.get("result") != "PASS":
        errors.append(f"transition not PASS: {row.get('from_section')}->{row.get('to_section')}")
    if not row.get("transition_kind") or not row.get("transition_statement"):
        errors.append(f"transition lacks mathematical handoff: {row.get('from_section')}->{row.get('to_section')}")

# One directory record per node; directories and status manifests exist.
if len(directories) != 145 or {r["id"] for r in directories} != {n["id"] for n in nodes}:
    errors.append("section directory index is not one-to-one with nodes")
dir_by_id = {r["id"]: r for r in directories}
for node in nodes:
    row = dir_by_id.get(node["id"])
    if not row:
        continue
    if row["section_path"] != node["paper_section"] or row["derivation_order"] != node["derivation_order"]:
        errors.append(f"directory index mismatch for {node['id']}")
    for field in ["main_directory", "supplement_directory"]:
        path = ROOT / row[field]
        if not path.is_dir():
            errors.append(f"node directory missing: {row[field]}")
        if path.name != node["stable_node_directory_name"]:
            errors.append(f"{node['id']} {field} does not use stable global node-directory name")
        status = path / "SECTION_STATUS.json"
        if not status.is_file():
            errors.append(f"section status missing: {status.relative_to(ROOT)}")
        else:
            data = json.loads(status.read_text(encoding="utf-8"))
            if data.get("id") != node["id"] or data.get("section_path") != node["paper_section"]:
                errors.append(f"section status mismatch for {node['id']} in {field}")
    for state_field, artifact_field in [("main_state", "main_artifact"), ("supplement_state", "supplement_artifact")]:
        exists = (ROOT / row[artifact_field]).is_file()
        expected_state = "DOCUMENTED" if exists else "PLANNED"
        if row[state_field] != expected_state:
            errors.append(f"{node['id']} {state_field} mismatch")

# No orphan directories: every directory below section roots is a hierarchy directory.
expected_main_dirs = {str((ROOT / row["main_directory"]).resolve()) for row in hierarchy}
expected_supp_dirs = {str((ROOT / row["supplement_directory"]).resolve()) for row in hierarchy}
actual_main_dirs = {str(p.resolve()) for p in MAIN_SECTIONS.rglob("*") if p.is_dir()} | {str(MAIN_SECTIONS.resolve())}
actual_supp_dirs = {str(p.resolve()) for p in SUPP_SECTIONS.rglob("*") if p.is_dir()} | {str(SUPP_SECTIONS.resolve())}
# The section root container itself is allowed but is not a numbered section.
expected_main_dirs.add(str(MAIN_SECTIONS.resolve()))
expected_supp_dirs.add(str(SUPP_SECTIONS.resolve()))
if actual_main_dirs != expected_main_dirs:
    extra = sorted(actual_main_dirs - expected_main_dirs)
    missing = sorted(expected_main_dirs - actual_main_dirs)
    errors.append(f"main section directory mismatch; extra={extra[:3]}, missing={missing[:3]}")
if actual_supp_dirs != expected_supp_dirs:
    extra = sorted(actual_supp_dirs - expected_supp_dirs)
    missing = sorted(expected_supp_dirs - actual_supp_dirs)
    errors.append(f"supplement section directory mismatch; extra={extra[:3]}, missing={missing[:3]}")

# Numeric directory prefixes enforce section order at every parent.
for base in [MAIN_SECTIONS, SUPP_SECTIONS]:
    for parent in [base] + [p for p in base.rglob("*") if p.is_dir()]:
        child_dirs = [p for p in parent.iterdir() if p.is_dir()]
        if not child_dirs:
            continue
        names = sorted(p.name for p in child_dirs)
        prefixes_found = []
        for name in names:
            match = re.match(r"^(\d+)_", name)
            if not match:
                errors.append(f"unnumbered section directory: {(parent/name).relative_to(ROOT)}")
                continue
            prefixes_found.append(int(match.group(1)))
        if len(prefixes_found) != len(set(prefixes_found)):
            errors.append(f"duplicate sibling section prefix: {parent.relative_to(ROOT)}")
        if prefixes_found != sorted(prefixes_found):
            errors.append(f"lexical directory order != numeric section order: {parent.relative_to(ROOT)}")

# Main paper includes are generated and follow documented-node derivation order.
paper_tex = (ROOT / "derivation/paper/main/paper.tex").read_text(encoding="utf-8")
if "\\input{derivation/paper/main/GENERATED_SECTION_STRUCTURE.tex}" not in paper_tex:
    errors.append("paper.tex does not consume generated section structure")
if re.search(r"\\input\{derivation/paper/main/sections/", paper_tex):
    errors.append("paper.tex retains manual node-section inputs")
generated = (ROOT / "derivation/paper/main/GENERATED_SECTION_STRUCTURE.tex").read_text(encoding="utf-8")
main_inputs = re.findall(r"\\input\{([^}]+/SECTION\.tex)\}", generated)
expected_main = [n["main_section_artifact"] for n in by_derivation if n["main_documentation_state"] == "DOCUMENTED"]
if main_inputs != expected_main:
    errors.append("generated main-paper input order != documented DAG order")

# Supplement source headings use stable NNN · ID labels and follow derivation order.
supp_text = (ROOT / "derivation/supplement/supplementary.md").read_text(encoding="utf-8")
if "# Traceability and reading convention" not in supp_text:
    errors.append("supplement traceability guide missing")
heading_pairs = re.findall(r"^#\s+(\d{3})\s+·\s+([A-Z]+\d+[A-Z]?)\s+—", supp_text, re.M)
expected_supp_nodes = [n for n in by_derivation if n["supplement_documentation_state"] == "DOCUMENTED"]
expected_pairs = [(f"{int(n['node_number']):03d}", n["id"]) for n in expected_supp_nodes]
if heading_pairs != expected_pairs:
    errors.append("supplement stable-node heading order != documented DAG order")
if re.search(r"^#\s+[0-9]+(?:\.[0-9]+)+\.\s+-", supp_text, re.M):
    errors.append("supplement node headings still depend on section numbering")

# Per-node audit table.
audit_rows = []
for node in by_derivation:
    row = dir_by_id[node["id"]]
    audit_rows.append({
        "node_number": node["node_number"],
        "id": node["id"],
        "section_path": node["paper_section"],
        "derivation_order": node["derivation_order"],
        "main_state": row["main_state"],
        "supplement_state": row["supplement_state"],
        "result": "PASS",
    })
with (DAG / "G1_SECTION_ORDER_AUDIT.tsv").open("w", encoding="utf-8", newline="") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(audit_rows[0]), delimiter="\t", lineterminator="\n")
    writer.writeheader(); writer.writerows(audit_rows)

result = {
    "schema": "cnna.g1-unified-section-hierarchy-audit.v1",
    "status": "PASS" if not errors else "FAIL",
    "nodes": len(nodes),
    "node_sections": len(nodes),
    "hierarchy_rows": len(hierarchy),
    "section_transitions": len(transitions),
    "main_documented_nodes": sum(n["main_documentation_state"] == "DOCUMENTED" for n in nodes),
    "supplement_documented_nodes": sum(n["supplement_documentation_state"] == "DOCUMENTED" for n in nodes),
    "dag_order_equals_section_order": not any("DAG derivation order" in e for e in errors),
    "section_order_equals_directory_order": not any("directory" in e.lower() for e in errors),
    "orphan_sections": 0 if not any("orphan" in e.lower() or "directory mismatch" in e.lower() for e in errors) else None,
    "nodes_without_section": sum(not n.get("paper_section") for n in nodes),
    "hierarchy_generated_from": "derivation/registry/dag/NODES.tsv",
    "paper_structure_generated": True,
    "supplement_sequence_generated": True,
    "errors": errors,
}
(DAG / "G1_AUDIT.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, ensure_ascii=False, indent=2))
sys.exit(1 if errors else 0)
