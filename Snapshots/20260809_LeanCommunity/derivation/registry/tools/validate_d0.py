#!/usr/bin/env python3
from pathlib import Path
import csv, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[3]
REG = ROOT / "derivation/registry"
DAG = REG / "dag"
DOC = REG / "documentation"
ALLOWED_STATES = {"NOT_STARTED", "V1_CONTENT_PRESENT_MIGRATION_REQUIRED", "DRAFT_V2", "COMPLETE_V2"}


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


errors: list[str] = []
nodes = rows(DAG / "NODES.tsv")
tiers = rows(DOC / "DOCUMENTATION_TIERS.tsv")
anchors = rows(DOC / "CODE_ANCHORS.tsv")

if len(nodes) != 145:
    errors.append("node count")
if len(tiers) != 145:
    errors.append("tier rows")

for node in nodes:
    sid = node["id"]
    if node.get("documentation_tier") not in {"D0", "D1", "D2"}:
        errors.append("tier " + sid)
    if node.get("documentation_v2_state") not in ALLOWED_STATES:
        errors.append("state " + sid)
    node_path = REG / "nodes" / f"{sid}.json"
    if not node_path.is_file():
        errors.append("node json " + sid)
        continue
    data = json.loads(node_path.read_text(encoding="utf-8"))
    profile = data.get("documentation_profile", {})
    if profile.get("tier") != node.get("documentation_tier"):
        errors.append("profile tier " + sid)
    if profile.get("v2_state") != node.get("documentation_v2_state"):
        errors.append("profile state " + sid)
    if len(profile.get("required_sections", [])) < 8:
        errors.append("sections " + sid)
    if profile.get("v2_state") == "COMPLETE_V2":
        if profile.get("countercheck_status") != "PASS":
            errors.append("complete countercheck " + sid)
        evidence = profile.get("completion_evidence", {})
        if not evidence.get("required_sections_present") or not evidence.get("code_anchors_resolved"):
            errors.append("complete evidence " + sid)
        main_rel = data.get("section_hierarchy", {}).get("main_artifact")
        supp_rel = data.get("section_hierarchy", {}).get("supplement_artifact")
        if not main_rel or not supp_rel:
            errors.append("complete artifacts " + sid)
        else:
            main = ROOT / main_rel
            supp = ROOT / supp_rel
            if not main.is_file() or not supp.is_file():
                errors.append("complete artifact missing " + sid)
            else:
                if data.get("artifacts", {}).get("math_prose") != sha(main):
                    errors.append("main documentation hash " + sid)
                if data.get("artifacts", {}).get("supplement_documentation") != sha(supp):
                    errors.append("supplement documentation hash " + sid)

for anchor in anchors:
    path = ROOT / anchor["path"]
    if not path.is_file():
        errors.append("anchor path " + anchor["path"])
        continue
    if sha(path) != anchor["source_sha256"]:
        errors.append("anchor hash " + anchor["id"] + ":" + anchor["symbol"])
    lines = path.read_text(encoding="utf-8").splitlines()
    start, end = int(anchor["start_line"]), int(anchor["end_line"])
    if not (1 <= start <= end <= len(lines)):
        errors.append("anchor range " + anchor["id"] + ":" + anchor["symbol"])
    elif anchor["symbol"] != "<module>" and anchor["symbol"] not in "\n".join(lines[start - 1 : min(end, start + 3)]):
        errors.append("anchor symbol " + anchor["id"] + ":" + anchor["symbol"])

counts = {tier: sum(node["documentation_tier"] == tier for node in nodes) for tier in ["D0", "D1", "D2"]}
states = {state: sum(node["documentation_v2_state"] == state for node in nodes) for state in ALLOWED_STATES}
result = {
    "schema": "cnna.d0-documentation-schema-audit.v2",
    "status": "PASS" if not errors else "FAIL",
    "nodes": len(nodes),
    "tier_counts": counts,
    "documentation_states": states,
    "node_records": len(list((REG / "nodes").glob("*.json"))),
    "code_anchors": len(anchors),
    "resolved_python_nodes": sum(node["python_anchor_status"] == "RESOLVED" for node in nodes),
    "resolved_lean_nodes": sum(node["lean_anchor_status"] == "RESOLVED" for node in nodes),
    "errors": errors,
}
(DOC / "D0_AUDIT.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
sys.exit(1 if errors else 0)
