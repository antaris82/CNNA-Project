#!/usr/bin/env python3
from __future__ import annotations

from collections import defaultdict, deque
from pathlib import Path
import csv
import json
import re
import shutil

ROOT = Path(__file__).resolve().parents[3]
DAG = ROOT / "derivation/registry/dag"
NODES_PATH = DAG / "NODES.tsv"
EDGES_PATH = DAG / "EDGES.tsv"
HIERARCHY_PATH = DAG / "SECTION_HIERARCHY.tsv"
TRANSITIONS_PATH = DAG / "SECTION_TRANSITIONS.tsv"
DIRECTORY_INDEX_PATH = DAG / "SECTION_DIRECTORY_INDEX.tsv"
MAIN_SECTIONS = ROOT / "derivation/paper/main/sections"
SUPP_SECTIONS = ROOT / "derivation/supplement/sections"
GENERATED_MAIN = ROOT / "derivation/paper/main/GENERATED_SECTION_STRUCTURE.tex"
SUPP_MD = ROOT / "derivation/supplement/supplementary.md"
TRACEABILITY_GUIDE_MD = ROOT / "derivation/registry/documentation/TRACEABILITY_AND_READING_GUIDE.md"
OPEN_PROVENANCE_FRAMEWORK_MD = ROOT / "derivation/registry/documentation/OPEN_PROVENANCE_FRAMEWORK.md"
ROOT_CLASSIFICATION = DAG / "G0_ROOT_CLASSIFICATION.md"


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def write_tsv(path: Path, rows: list[dict[str, object]], fields: list[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fields})


def key(section: str) -> tuple[int, ...]:
    return tuple(int(part) for part in section.split("."))


def slug(text: str) -> str:
    value = text.lower()
    value = value.replace("/", "_").replace("+", "plus")
    value = re.sub(r"[^a-z0-9]+", "_", value)
    return value.strip("_") or "section"


def parse_parent_titles() -> tuple[dict[str, str], dict[str, str]]:
    roots: dict[str, str] = {}
    groups: dict[str, str] = {}
    if HIERARCHY_PATH.is_file():
        for row in read_tsv(HIERARCHY_PATH):
            section = row.get("paper_section", "")
            level = row.get("level", "")
            if level == "0":
                roots[section] = row["title"]
            elif level == "1":
                groups[section] = row["title"]
    return roots, groups


def parse_root_reasons() -> dict[str, str]:
    reasons: dict[str, str] = {}
    if not ROOT_CLASSIFICATION.is_file():
        return reasons
    for line in ROOT_CLASSIFICATION.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|") or "---" in line or "No." in line:
            continue
        parts = [part.strip() for part in line.strip("|").split("|")]
        if len(parts) >= 6 and re.fullmatch(r"[A-Z]+\d+[A-Z]?", parts[1]):
            reasons[parts[1]] = parts[5]
    return reasons


def find_existing_main(node_id: str) -> Path | None:
    matches = [p for p in MAIN_SECTIONS.rglob("SECTION.tex") if re.search(rf"(?:^|_){re.escape(node_id)}__", p.parent.name)]
    if len(matches) > 1:
        raise RuntimeError(f"multiple main-paper artifacts for {node_id}: {matches}")
    return matches[0] if matches else None


def find_existing_supp(node_id: str) -> Path | None:
    matches = [p for p in SUPP_SECTIONS.rglob("DOCUMENTATION.md") if re.search(rf"(?:^|_){re.escape(node_id)}__", p.parent.name)]
    if len(matches) > 1:
        raise RuntimeError(f"multiple supplement artifacts for {node_id}: {matches}")
    return matches[0] if matches else None


def prefix_dir(component: int, identifier: str | None, title: str) -> str:
    if identifier:
        return f"{component:02d}_{identifier}__{slug(title)}"
    return f"{component:02d}_{slug(title)}"


def node_dir_name(node: dict[str, str]) -> str:
    """Stable node-directory identity independent of the current section path."""
    return f"{int(node['node_number']):03d}_{node['id']}__{slug(node['label'])}"


def make_paths(node: dict[str, str], by_section: dict[str, dict[str, str]]) -> tuple[Path, Path]:
    parts = key(node["paper_section"])
    root_title = node["section_root_title"]
    group_title = node["section_group_title"]
    components = [prefix_dir(parts[0], None, root_title), prefix_dir(parts[1], None, group_title)]
    for length in range(3, len(parts) + 1):
        prefix = ".".join(str(x) for x in parts[:length])
        owner = by_section[prefix]
        components.append(node_dir_name(owner))
    rel = Path(*components)
    return MAIN_SECTIONS / rel, SUPP_SECTIONS / rel


def descendant(section: str, prefix: str) -> bool:
    return section == prefix or section.startswith(prefix + ".")


def cross_edges(from_prefix: str, to_prefix: str, nodes: list[dict[str, str]], edges: list[dict[str, str]]) -> list[str]:
    from_ids = {n["id"] for n in nodes if descendant(n["paper_section"], from_prefix)}
    to_ids = {n["id"] for n in nodes if descendant(n["paper_section"], to_prefix)}
    return [e["id"] for e in edges if e["hard_dependency"] == "true" and e["source"] in from_ids and e["target"] in to_ids]


def transition_record(
    from_section: str,
    to_section: str,
    level: int,
    nodes: list[dict[str, str]],
    edges: list[dict[str, str]],
    by_id: dict[str, dict[str, str]],
) -> dict[str, object]:
    from_nodes = [n for n in nodes if descendant(n["paper_section"], from_section)]
    to_nodes = [n for n in nodes if descendant(n["paper_section"], to_section)]
    left = max(from_nodes, key=lambda n: int(n["derivation_order"]))
    right = min(to_nodes, key=lambda n: int(n["derivation_order"]))
    direct = [e for e in edges if e["hard_dependency"] == "true" and e["source"] == left["id"] and e["target"] == right["id"]]
    crossing = cross_edges(from_section, to_section, nodes, edges)
    if direct:
        kind = "DIRECT_HARD_HANDOFF"
        statement = f"{left['id']} hands its result directly to {right['id']} through {direct[0]['relation']}."
        support = ",".join(e["id"] for e in direct)
    elif right.get("proof_owner") and right["proof_owner"] in {n["id"] for n in from_nodes}:
        kind = "PROOF_OWNER_EXPANSION"
        statement = f"{right['id']} expands the proof obligation owned by {right['proof_owner']} without creating a parallel derivation branch."
        support = ""
    elif crossing:
        kind = "CROSS_SECTION_HARD_HANDOFF"
        statement = f"The next section receives hard mathematical inputs through {len(crossing)} registered DAG edge(s)."
        support = ",".join(crossing)
    elif right["introduction_reason"]:
        kind = "EXPLICIT_INTRODUCTION_POINT"
        statement = right["introduction_reason"]
        support = ""
    else:
        kind = "ACCUMULATED_DERIVATION_ORDER"
        incoming = [e for e in edges if e["hard_dependency"] == "true" and e["target"] == right["id"]]
        support = ",".join(e["id"] for e in incoming)
        statement = f"{right['id']} is introduced after all of its registered predecessors have appeared in derivation order."
    return {
        "hierarchy_level": level,
        "from_section": from_section,
        "to_section": to_section,
        "from_last_node": left["id"],
        "to_first_node": right["id"],
        "transition_kind": kind,
        "supporting_edge_ids": support,
        "transition_statement": statement,
        "result": "PASS",
    }


def main() -> None:
    old_nodes = read_tsv(NODES_PATH)
    edges = read_tsv(EDGES_PATH)
    if not old_nodes:
        raise RuntimeError("empty NODES.tsv")
    if all(row.get("section_root_title") and row.get("section_group_title") for row in old_nodes):
        root_titles = {row["paper_section"].split(".")[0]: row["section_root_title"] for row in old_nodes}
        group_titles = {".".join(row["paper_section"].split(".")[:2]): row["section_group_title"] for row in old_nodes}
    else:
        # One-time migration fallback only; after G1, NODES.tsv is authoritative.
        root_titles, group_titles = parse_parent_titles()
    root_reasons = parse_root_reasons()

    # Populate section metadata directly on every canonical node row.
    nodes: list[dict[str, str]] = []
    incoming = defaultdict(list)
    for edge in edges:
        if edge["hard_dependency"] == "true":
            incoming[edge["target"]].append(edge)
    for row in old_nodes:
        section = row["paper_section"]
        parts = section.split(".")
        root_prefix = parts[0]
        group_prefix = ".".join(parts[:2])
        row = dict(row)
        row["section_path"] = section
        row["section_root_title"] = root_titles[root_prefix]
        row["section_group_title"] = group_titles[group_prefix]
        if row.get("introduction_reason"):
            reason = row["introduction_reason"]
        elif row["id"] in root_reasons:
            reason = root_reasons[row["id"]]
        elif incoming[row["id"]]:
            sources = ", ".join(edge["source"] for edge in incoming[row["id"]])
            relations = ", ".join(edge["relation"] for edge in incoming[row["id"]])
            reason = f"Introduced after {sources}; registered hard handoff(s): {relations}."
        elif row["proof_owner"]:
            reason = f"Introduced as the proof-certification expansion owned by {row['proof_owner']}."
        else:
            reason = "Introduced at this derivation point as an explicitly classified convention, operator, control, or obstruction gate."
        row["introduction_reason"] = reason
        nodes.append(row)

    by_section = {n["paper_section"]: n for n in nodes}
    by_id = {n["id"]: n for n in nodes}

    # First discover current artifacts before moving anything.
    old_main = {n["id"]: find_existing_main(n["id"]) for n in nodes}
    old_supp = {n["id"]: find_existing_supp(n["id"]) for n in nodes}

    directory_rows: list[dict[str, object]] = []
    for node in nodes:
        main_dir, supp_dir = make_paths(node, by_section)
        main_dir.mkdir(parents=True, exist_ok=True)
        supp_dir.mkdir(parents=True, exist_ok=True)
        main_artifact = main_dir / "SECTION.tex"
        supp_artifact = supp_dir / "DOCUMENTATION.md"
        if old_main[node["id"]] and old_main[node["id"]] != main_artifact:
            if main_artifact.exists():
                main_artifact.unlink()
            shutil.move(str(old_main[node["id"]]), str(main_artifact))
        if old_supp[node["id"]] and old_supp[node["id"]] != supp_artifact:
            if supp_artifact.exists():
                supp_artifact.unlink()
            shutil.move(str(old_supp[node["id"]]), str(supp_artifact))
        main_state = "DOCUMENTED" if main_artifact.is_file() else "PLANNED"
        supp_state = "DOCUMENTED" if supp_artifact.is_file() else "PLANNED"
        status = {
            "schema": "cnna.section-directory-status.v2",
            "node_number": node["node_number"],
            "canonical_node_label": f"{int(node['node_number']):03d} · {node['id']}",
            "stable_node_directory_name": node_dir_name(node),
            "id": node["id"],
            "section_path": node["paper_section"],
            "derivation_order": int(node["derivation_order"]),
            "main_documentation": main_state,
            "supplement_documentation": supp_state,
            "generated_from": "derivation/registry/dag/NODES.tsv",
        }
        (main_dir / "SECTION_STATUS.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        (supp_dir / "SECTION_STATUS.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        node["canonical_node_label"] = f"{int(node['node_number']):03d} · {node['id']}"
        node["stable_node_directory_name"] = node_dir_name(node)
        node["main_section_directory"] = str(main_dir.relative_to(ROOT))
        node["supplement_section_directory"] = str(supp_dir.relative_to(ROOT))
        node["main_section_artifact"] = str(main_artifact.relative_to(ROOT))
        node["supplement_section_artifact"] = str(supp_artifact.relative_to(ROOT))
        node["main_documentation_state"] = main_state
        node["supplement_documentation_state"] = supp_state
        directory_rows.append({
            "node_number": node["node_number"],
            "id": node["id"],
            "section_path": node["paper_section"],
            "derivation_order": node["derivation_order"],
            "main_directory": node["main_section_directory"],
            "main_artifact": node["main_section_artifact"],
            "main_state": main_state,
            "supplement_directory": node["supplement_section_directory"],
            "supplement_artifact": node["supplement_section_artifact"],
            "supplement_state": supp_state,
            "result": "PASS",
        })

    # Remove stale node directories left by an earlier section-local naming scheme.
    expected_node_dirs = {str((ROOT / n["main_section_directory"]).resolve()) for n in nodes}
    expected_node_dirs |= {str((ROOT / n["supplement_section_directory"]).resolve()) for n in nodes}
    for base in [MAIN_SECTIONS, SUPP_SECTIONS]:
        for status_path in list(base.rglob("SECTION_STATUS.json")):
            parent = status_path.parent
            if str(parent.resolve()) in expected_node_dirs:
                continue
            other_files = [x for x in parent.iterdir() if x.is_file() and x.name != "SECTION_STATUS.json"]
            child_dirs = [x for x in parent.iterdir() if x.is_dir()]
            if other_files:
                raise RuntimeError(f"stale section directory contains non-status artifacts: {parent}")
            status_path.unlink()
            if not child_dirs:
                parent.rmdir()

    # Remove now-empty legacy folders, bottom-up.
    for base in [MAIN_SECTIONS, SUPP_SECTIONS]:
        for path in sorted((p for p in base.rglob("*") if p.is_dir()), key=lambda p: len(p.parts), reverse=True):
            try:
                path.rmdir()
            except OSError:
                pass

    fields = list(old_nodes[0].keys())
    extra = [
        "section_path", "section_root_title", "section_group_title", "introduction_reason",
        "canonical_node_label", "stable_node_directory_name",
        "main_section_directory", "supplement_section_directory", "main_section_artifact",
        "supplement_section_artifact", "main_documentation_state", "supplement_documentation_state",
    ]
    fields = [f for f in fields if f not in extra] + extra
    write_tsv(NODES_PATH, nodes, fields)

    # Mirror the same canonical section metadata into each node JSON.
    for node in nodes:
        path = ROOT / f"derivation/registry/nodes/{node['id']}.json"
        if not path.is_file():
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        data["canonical_identity"] = {
            "node_number": node["node_number"],
            "semantic_id": node["id"],
            "canonical_node_label": node["canonical_node_label"],
            "stable_node_directory_name": node["stable_node_directory_name"],
            "identity_rule": "node number and semantic ID are independent of the mutable section path",
        }
        data["section_hierarchy"] = {
            "section_path": node["paper_section"],
            "root_title": node["section_root_title"],
            "group_title": node["section_group_title"],
            "main_directory": node["main_section_directory"],
            "supplement_directory": node["supplement_section_directory"],
            "main_artifact": node["main_section_artifact"],
            "supplement_artifact": node["supplement_section_artifact"],
            "introduction_reason": node["introduction_reason"],
        }
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    # Generate the complete hierarchy from node attributes only.
    prefixes: set[str] = set()
    for node in nodes:
        parts = node["paper_section"].split(".")
        prefixes.update(".".join(parts[:length]) for length in range(1, len(parts) + 1))
    hierarchy_rows: list[dict[str, object]] = []
    for prefix in sorted(prefixes, key=key):
        parts = prefix.split(".")
        descendants = [n for n in nodes if descendant(n["paper_section"], prefix)]
        first = min(descendants, key=lambda n: int(n["derivation_order"]))
        last = max(descendants, key=lambda n: int(n["derivation_order"]))
        if len(parts) == 1:
            title = first["section_root_title"]
            kind = "ROOT_SECTION"
            main_dir = MAIN_SECTIONS / prefix_dir(int(parts[0]), None, title)
            supp_dir = SUPP_SECTIONS / prefix_dir(int(parts[0]), None, title)
        elif len(parts) == 2:
            title = first["section_group_title"]
            kind = "SECTION_GROUP"
            root_component = prefix_dir(int(parts[0]), None, first["section_root_title"])
            group_component = prefix_dir(int(parts[1]), None, title)
            main_dir = MAIN_SECTIONS / root_component / group_component
            supp_dir = SUPP_SECTIONS / root_component / group_component
        else:
            owner = by_section[prefix]
            title = owner["label"]
            kind = "NODE_SECTION" if len(parts) == 3 else "PROOF_NODE_SECTION"
            main_dir = ROOT / owner["main_section_directory"]
            supp_dir = ROOT / owner["supplement_section_directory"]
        main_dir.mkdir(parents=True, exist_ok=True)
        supp_dir.mkdir(parents=True, exist_ok=True)
        hierarchy_rows.append({
            "paper_section": prefix,
            "level": len(parts) - 1,
            "section_kind": kind,
            "title": title,
            "first_node_number": first["node_number"],
            "first_node_id": first["id"],
            "last_node_number": last["node_number"],
            "last_node_id": last["id"],
            "node_count": len(descendants),
            "derivation_order_start": first["derivation_order"],
            "derivation_order_end": last["derivation_order"],
            "main_directory": str(main_dir.relative_to(ROOT)),
            "supplement_directory": str(supp_dir.relative_to(ROOT)),
            "generated_from": "derivation/registry/dag/NODES.tsv",
        })
    write_tsv(HIERARCHY_PATH, hierarchy_rows, [
        "paper_section", "level", "section_kind", "title", "first_node_number", "first_node_id",
        "last_node_number", "last_node_id", "node_count", "derivation_order_start", "derivation_order_end",
        "main_directory", "supplement_directory", "generated_from",
    ])

    # Generate transitions between every pair of sibling sections at every hierarchy level.
    children: dict[str, list[str]] = defaultdict(list)
    for prefix in prefixes:
        parts = prefix.split(".")
        parent = ".".join(parts[:-1])
        children[parent].append(prefix)
    transition_rows: list[dict[str, object]] = []
    for parent, siblings in children.items():
        ordered = sorted(siblings, key=key)
        for left, right in zip(ordered, ordered[1:]):
            transition_rows.append(transition_record(left, right, len(left.split(".")) - 1, nodes, edges, by_id))
    write_tsv(TRANSITIONS_PATH, transition_rows, [
        "hierarchy_level", "from_section", "to_section", "from_last_node", "to_first_node",
        "transition_kind", "supporting_edge_ids", "transition_statement", "result",
    ])
    write_tsv(DIRECTORY_INDEX_PATH, directory_rows, [
        "node_number", "id", "section_path", "derivation_order", "main_directory", "main_artifact", "main_state",
        "supplement_directory", "supplement_artifact", "supplement_state", "result",
    ])

    # Main-paper include order is generated from documented node artifacts.
    documented = [n for n in nodes if n["main_documentation_state"] == "DOCUMENTED"]
    lines = ["% Generated from derivation/registry/dag/NODES.tsv. Do not edit manually."]
    current_root = current_group = None
    for node in sorted(documented, key=lambda n: int(n["derivation_order"])):
        root = node["paper_section"].split(".")[0]
        group = ".".join(node["paper_section"].split(".")[:2])
        if root != current_root:
            lines.append(f"\\section{{{node['section_root_title']}}}")
            current_root = root
            current_group = None
        if group != current_group:
            lines.append(f"\\subsection{{{node['section_group_title']}}}")
            current_group = group
        lines.append(f"\\input{{{node['main_section_artifact']}}}")
    GENERATED_MAIN.write_text("\n".join(lines) + "\n", encoding="utf-8")

    # Supplement body source is likewise concatenated in canonical derivation order.
    old = SUPP_MD.read_text(encoding="utf-8") if SUPP_MD.is_file() else "# From Primitive Provenance to Mathematical Structure — Supplementary Material\n\n"
    metadata_match = re.search(
        r"\A# From Primitive Provenance to Mathematical Structure — Supplementary Material\s*\n\n(<!-- CNNA-DOCUMENT-METADATA-BEGIN -->.*?<!-- CNNA-DOCUMENT-METADATA-END -->\s*\n\n)?",
        old,
        flags=re.S,
    )
    header = metadata_match.group(0) if metadata_match else "# From Primitive Provenance to Mathematical Structure — Supplementary Material\n\n"
    body_parts = []
    if OPEN_PROVENANCE_FRAMEWORK_MD.is_file():
        body_parts.append(OPEN_PROVENANCE_FRAMEWORK_MD.read_text(encoding="utf-8").rstrip())
    if TRACEABILITY_GUIDE_MD.is_file():
        body_parts.append(TRACEABILITY_GUIDE_MD.read_text(encoding="utf-8").rstrip())
    for node in sorted(nodes, key=lambda n: int(n["derivation_order"])):
        artifact = ROOT / node["supplement_section_artifact"]
        if artifact.is_file():
            body_parts.append(artifact.read_text(encoding="utf-8").rstrip())
    SUPP_MD.write_text(header + "\n\n---\n\n".join(body_parts) + "\n", encoding="utf-8")

    print(json.dumps({
        "nodes": len(nodes),
        "hierarchy_rows": len(hierarchy_rows),
        "transition_rows": len(transition_rows),
        "documented_main_nodes": len(documented),
        "documented_supplement_nodes": sum(n["supplement_documentation_state"] == "DOCUMENTED" for n in nodes),
    }, indent=2))


if __name__ == "__main__":
    main()
