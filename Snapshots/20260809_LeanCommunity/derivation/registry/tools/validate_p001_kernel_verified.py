#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import csv
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "derivation/code/lean"
REG = ROOT / "derivation/registry"
DOC = REG / "documentation"
EVIDENCE = LEAN / "audit/evidence/USER_LOCAL_P001_FULL_BUILD_20260806.json"
TRANSCRIPT = LEAN / "audit/evidence/USER_LOCAL_P001_FULL_BUILD_20260806.txt"
STATIC = LEAN / "audit/P001_STATIC_AUDIT.json"
OUTPUT = DOC / "P001_CURRENT_AUDIT.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


errors: list[str] = []

if not EVIDENCE.is_file() or not TRANSCRIPT.is_file():
    errors.append("authoritative build evidence missing")
    evidence: dict = {}
else:
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))

expected_profiles = {
    "choice_propext_quot": 117,
    "propext_quot_only": 23,
    "axiom_free": 2,
}
required_artifacts = {
    "core_olean",
    "proofs_olean",
    "proof_manifest",
    "p001_semantic_olean",
    "p001_maximum_principle_olean",
    "p001_finite_linear_olean",
    "p001_response_well_definedness_olean",
    "p001_directed_laplacian_olean",
    "p001_distinguished_positivity_olean",
    "p001_canonical_instantiation_olean",
    "p001_canonical_matrix_structure_olean",
    "p001_canonical_backbone_reachability_olean",
    "p001_m003_m004_facades_olean",
    "p001_second_cut_reuse_olean",
}
if evidence:
    expected_scalar = {
        "schema": "cnna.p001-kernel-build-evidence.v1",
        "status": "PASS",
        "toolchain": "leanprover/lean4:v4.31.0",
        "mathlib": "v4.31.0",
        "proof_modules": 13,
        "proof_declarations": 142,
        "source_warnings": 0,
        "p001_current_proof_axiom_audit": "PASS",
        "full_package_boundary_audit": "PASS",
    }
    for key, value in expected_scalar.items():
        if evidence.get(key) != value:
            errors.append(f"build evidence field {key}")
    if evidence.get("axiom_profile_counts") != expected_profiles:
        errors.append("axiom-profile partition")
    if evidence.get("transcript_sha256") != sha(TRANSCRIPT):
        errors.append("build transcript hash")
    artifacts = evidence.get("verified_artifacts", {})
    if not required_artifacts.issubset(artifacts) or not all(artifacts.get(k) is True for k in required_artifacts):
        errors.append("verified build artifacts")
    built_hashes = evidence.get("verified_source_sha256", {})
    if len(built_hashes) != 12:
        errors.append("verified source set")
    for relative, expected in built_hashes.items():
        source = LEAN / relative
        if not source.is_file() or sha(source) != expected:
            errors.append("verified source hash " + relative)

transcript = TRANSCRIPT.read_text(encoding="utf-8") if TRANSCRIPT.is_file() else ""
for required in [
    "Build completed successfully (8595 jobs).",
    "P001_CURRENT_PROOF_AXIOM_AUDIT PASS",
    '"p001": "R8_INDEPENDENT_BIDIRECTED_CHAIN_REUSE_KERNEL_VERIFIED"',
    '"p001_second_cut_reuse_olean": true',
    "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
]:
    if required not in transcript:
        errors.append("build transcript marker " + required)

run = subprocess.run(
    [sys.executable, str(LEAN / "audit/check_package_boundary.py"), "--output", str(STATIC)],
    cwd=LEAN,
    capture_output=True,
    text=True,
)
if run.returncode:
    errors.append("static package-boundary audit")
static = json.loads(STATIC.read_text(encoding="utf-8")) if STATIC.is_file() else {}
if static.get("status") != "PASS":
    errors.append("static audit status")
if static.get("proofs", {}).get("p001") not in {
    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE",
    "KERNEL_VERIFIED_CURRENT_BUILD",
}:
    errors.append("static P001 status")
if static.get("build_evidence", {}).get("retained_verified_p001_source_hash_match") is not True:
    errors.append("current-source evidence binding")

node_path = REG / "nodes/P001.json"
node = json.loads(node_path.read_text(encoding="utf-8"))
lean_evidence = node.get("evidence", {}).get("lean", {})
if lean_evidence.get("kernel_verified_declarations") != 142:
    errors.append("P001 node declaration count")
if lean_evidence.get("axiom_profile_counts") != expected_profiles:
    errors.append("P001 node axiom profiles")
if lean_evidence.get("build_evidence_sha256") != sha(EVIDENCE):
    errors.append("P001 node build-evidence hash")
if lean_evidence.get("build_transcript_sha256") != sha(TRANSCRIPT):
    errors.append("P001 node transcript hash")
if node.get("implementation_status", {}).get("status") != "KERNEL_VERIFIED":
    errors.append("P001 implementation status")
if node.get("documentation_profile", {}).get("lean_anchor_status") != "RESOLVED_142_KERNEL_AXIOM_VERIFIED":
    errors.append("P001 code-anchor status")

anchors = [r for r in rows(DOC / "CODE_ANCHORS.tsv") if r["id"] == "P001"]
if len(anchors) != 179:
    errors.append("P001 code-anchor count")
for anchor in anchors:
    source = ROOT / anchor["path"]
    if not source.is_file() or sha(source) != anchor["source_sha256"]:
        errors.append("P001 code-anchor integrity " + anchor["symbol"])

usage_rows = [r for r in rows(REG / "references/EXTERNAL_REFERENCE_USAGE.tsv") if r["id"] == "P001"]
if len(usage_rows) != 26:
    errors.append("P001 reference-usage count")
for usage in usage_rows:
    target = ROOT / usage["target_file"]
    if not target.is_file():
        errors.append("P001 reference target " + usage["usage_id"])
        continue
    text = target.read_text(encoding="utf-8")
    if usage["scope"] == "MAIN_TEX":
        begin = f"% CNNA-EXTREF-BEGIN {usage['usage_id']}"
        end = f"% CNNA-EXTREF-END {usage['usage_id']}"
    else:
        begin = f"<!-- CNNA-EXTREF-BEGIN {usage['usage_id']} -->"
        end = f"<!-- CNNA-EXTREF-END {usage['usage_id']} -->"
    if text.count(begin) != 1 or text.count(end) != 1:
        errors.append("P001 reference marker " + usage["usage_id"])
    status = usage["formalization_status"]
    if any(token in status for token in ["PENDING", "OPEN", "REPAIR", "R6", "R7", "R8"]):
        errors.append("P001 reference status " + usage["usage_id"])

main = ROOT / node["section_hierarchy"]["main_artifact"]
supp = ROOT / node["section_hierarchy"]["supplement_artifact"]
profile = node["documentation_profile"]
completion = profile["completion_evidence"]
if node.get("artifacts", {}).get("math_prose") != sha(main):
    errors.append("P001 main documentation hash")
if node.get("artifacts", {}).get("supplement_documentation") != sha(supp):
    errors.append("P001 supplementary documentation hash")
if completion.get("main_sha256") != sha(main) or completion.get("supplement_sha256") != sha(supp):
    errors.append("P001 completion documentation hashes")

active_docs = [
    main,
    supp,
    ROOT / "derivation/registry/documentation/TRACEABILITY_AND_READING_GUIDE.md",
    ROOT / "derivation/paper/main/TRACEABILITY_AND_READING_GUIDE.tex",
]
for path in active_docs:
    text = path.read_text(encoding="utf-8")
    for pattern in [
        r"SOURCE[_ -]?BUILD[_ -]?PENDING",
        r"BUILD[_ -]?PENDING",
        r"ANALYTICAL[_ -]?PROOF[_ -]?OPEN",
        r"documentation phase",
        r"intermediate status",
        r"promotion report",
        r"repair report",
    ]:
        if re.search(pattern, text, flags=re.I):
            errors.append(f"noncurrent documentation wording {path.relative_to(ROOT)}")

s11 = LEAN / "proofs/src/CNNAProofs/P001/S11_IndependentBidirectedChainCutReuse.lean"
s11_text = s11.read_text(encoding="utf-8")
for declaration in [
    "independentChainBoundaryWeight",
    "independentBidirectedChainBlocks",
    "independentBidirectedChainOffDiagonalNonpositive",
    "independentBidirectedChainRowConservative",
    "independentBidirectedChainInteriorReachesBoundary",
    "independentBidirectedChainDistinguishedReachesOtherBoundary",
    "independentBidirectedChainHypotheses",
    "independentBidirectedChainClosure",
    "SecondCutReuseContract",
    "secondCutReuseContract",
]:
    if declaration not in s11_text:
        errors.append("S11 declaration " + declaration)
if s11_text.count("exact directedSchurDtnClosure") != 1:
    errors.append("S11 generic-closure reuse count")

result = {
    "schema": "cnna.p001-current-audit.v1",
    "status": "PASS" if not errors else "FAIL",
    "date": "2026-08-06",
    "toolchain": "leanprover/lean4:v4.31.0",
    "proof_modules": 13,
    "kernel_verified_declarations": 142,
    "axiom_profile_counts": expected_profiles,
    "code_anchors": len(anchors),
    "reference_usage_rows": len(usage_rows),
    "independent_cut_reuse": "KERNEL_VERIFIED",
    "exact_source_evidence": "MATCH",
    "errors": errors,
}
OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
sys.exit(1 if errors else 0)
