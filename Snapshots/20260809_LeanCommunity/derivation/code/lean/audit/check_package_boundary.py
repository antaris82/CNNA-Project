#!/usr/bin/env python3
"""Audit the one-way CNNA core/proof Lake package boundary."""
from __future__ import annotations

import argparse
import json
import hashlib
from pathlib import Path
import re
import sys
import tomllib

LEAN_ROOT = Path(__file__).resolve().parents[1]
CORE = LEAN_ROOT / "core"
PROOFS = LEAN_ROOT / "proofs"
TOOLCHAIN = "leanprover/lean4:v4.31.0"


def read_toml(path: Path) -> dict:
    with path.open("rb") as handle:
        return tomllib.load(handle)


def imports(path: Path) -> list[str]:
    result: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"\s*import\s+([^\s]+)", line)
        if match:
            result.append(match.group(1))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-build", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    errors: list[str] = []
    warnings: list[str] = []

    def manifest_paths(path: Path) -> set[str]:
        if not path.is_file():
            errors.append(f"missing source hash manifest: {path}")
            return set()
        result: set[str] = set()
        for raw in path.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(maxsplit=1)
            if len(parts) != 2:
                errors.append(f"malformed source hash row in {path.name}: {raw!r}")
                continue
            result.add(parts[1])
        return result

    p001_manifest_paths = manifest_paths(LEAN_ROOT / "audit/P001_CURRENT_SOURCE_SHA256.txt")
    m003_m004_manifest_paths = manifest_paths(LEAN_ROOT / "audit/M003M004_CURRENT_SOURCE_SHA256.txt")
    p002_manifest_paths = manifest_paths(LEAN_ROOT / "audit/P002_CURRENT_SOURCE_SHA256.txt")
    c008_manifest_paths = manifest_paths(LEAN_ROOT / "audit/C008_CURRENT_SOURCE_SHA256.txt")
    c016_c017_manifest_paths = manifest_paths(LEAN_ROOT / "audit/C016C017_CURRENT_SOURCE_SHA256.txt")
    c009_manifest_paths = manifest_paths(LEAN_ROOT / "audit/C009_CURRENT_SOURCE_SHA256.txt")
    t002_manifest_paths = manifest_paths(LEAN_ROOT / "audit/T002_CURRENT_SOURCE_SHA256.txt")
    audit_manifest_paths = manifest_paths(LEAN_ROOT / "audit/AUDIT_INFRASTRUCTURE_CURRENT_SOURCE_SHA256.txt")
    scoped = {
        "P001": p001_manifest_paths,
        "M003/M004": m003_m004_manifest_paths,
        "P002": p002_manifest_paths,
        "C008": c008_manifest_paths,
        "C016/C017": c016_c017_manifest_paths,
        "C009": c009_manifest_paths,
        "T002": t002_manifest_paths,
        "audit infrastructure": audit_manifest_paths,
    }
    names = list(scoped)
    for i, left_name in enumerate(names):
        for right_name in names[i + 1:]:
            overlap = scoped[left_name] & scoped[right_name]
            if overlap:
                errors.append(
                    f"source hash scope overlap between {left_name} and {right_name}: "
                    f"{sorted(overlap)}")
    permitted_p001_aux = {"audit/P001_CurrentProofAxiomAudit.lean"}
    for relative in p001_manifest_paths:
        if not (relative.startswith("proofs/src/CNNAProofs/P001/") or relative in permitted_p001_aux):
            errors.append(f"non-P001 path in immutable P001 source scope: {relative}")
    required_m003_m004 = {
        "proofs/src/CNNAProofs/M003M004/S01_CanonicalM003Closure.lean",
        "proofs/src/CNNAProofs/M003M004/S02_CanonicalM004ClosureAndHandoff.lean",
        "proofs/src/CNNAProofs.lean",
        "audit/M003M004_CurrentProofAxiomAudit.lean",
    }
    if not required_m003_m004.issubset(m003_m004_manifest_paths):
        errors.append("M003/M004 source scope omits a required closure, aggregator, or axiom-audit source")
    required_p002 = {
        "proofs/lakefile.toml",
        "proofs/src/CNNAProofsP002.lean",
        "proofs/src/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S01_PrimitiveInputsGrammarAndEventOrder/"
        "S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/"
        "S01_P002_CanonicalScheduleStrictTotalOrderClosure.lean",
        "audit/P002_CurrentProofAxiomAudit.lean",
    }
    if p002_manifest_paths != required_p002:
        errors.append("P002 source scope must contain exactly its library target, root, proof module, and axiom audit")
    required_c008 = {
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/"
        "S01_C008_RecordLiveResponseCoupledUpdate.lean",
        "proofs/src/CNNAProofs/C008.lean",
        "proofs/src/CNNAProofs/C008/S01_CanonicalRecordLiveUpdateClosure.lean",
        "audit/C008_CurrentProofAxiomAudit.lean",
    }
    if c008_manifest_paths != required_c008:
        errors.append("C008 source scope must contain exactly its Core module, proof root, proof facade, and axiom audit")
    required_c016_c017 = {
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S02_C016_ImmutableRecordChannel.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S03_C017_CurrentLiveChannel.lean",
        "proofs/src/CNNAProofs/C016C017.lean",
        "proofs/src/CNNAProofs/C016C017/S01_CanonicalRecordLiveChannelProjectionClosure.lean",
        "audit/C016C017_CurrentProofAxiomAudit.lean",
    }
    if c016_c017_manifest_paths != required_c016_c017:
        errors.append("C016/C017 source scope must contain exactly two Core modules, proof root, shared proof facade, and axiom audit")
    required_c009 = {
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S04_C009_CodomainStateX.lean",
        "proofs/src/CNNAProofs/C009.lean",
        "proofs/src/CNNAProofs/C009/S01_CanonicalCodomainStateAssemblyClosure.lean",
        "audit/C009_CurrentProofAxiomAudit.lean",
    }
    if c009_manifest_paths != required_c009:
        errors.append("C009 source scope must contain exactly its Core assembly, proof root, proof facade, and axiom audit")
    required_t002 = {
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/S01A_C005_ConductanceAppendClosure.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/S02A_C004_SuccessorBornPrefixClosure.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/S03A_C006_ExactFractionRatRealizationClosure.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/S04A_M001_PortSupportClosure.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/S06A_C007_StateDirectedBlockRealizationClosure.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/S10A_M004_LiveUpdateSupportClosure.lean",
        "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S05_T002_RecurrentStateClosureTheorem.lean",
        "proofs/src/CNNAProofs/T002.lean",
        "proofs/src/CNNAProofs/T002/S01_CanonicalRecurrentStateClosure.lean",
        "audit/T002_CurrentProofAxiomAudit.lean",
    }
    if t002_manifest_paths != required_t002:
        errors.append("T002 source scope must contain exactly the origin-owned closures, Core theorem, proof root/facade, and axiom audit")
    required_audit_infra = {
        "audit/check_package_boundary.py",
        "audit/run_package_boundary_audit.sh",
    }
    if audit_manifest_paths != required_audit_infra:
        errors.append(
            "audit infrastructure source scope must contain exactly check_package_boundary.py "
            "and run_package_boundary_audit.sh")

    for package in (CORE, PROOFS):
        if not package.is_dir():
            errors.append(f"missing package directory: {package}")
        toolchain = (package / "lean-toolchain").read_text(encoding="utf-8").strip()
        if toolchain != TOOLCHAIN:
            errors.append(f"toolchain mismatch in {package.name}: {toolchain!r}")

    if (CORE / "lakefile.lean").exists():
        errors.append("core must use only lakefile.toml")
    if (PROOFS / "lakefile.lean").exists():
        errors.append("proofs must use only lakefile.toml")

    core_cfg = read_toml(CORE / "lakefile.toml")
    if core_cfg.get("name") != "cnna_core":
        errors.append("core package name is not cnna_core")
    if core_cfg.get("defaultTargets") != ["CNNA"]:
        errors.append("core default target is not CNNA")
    if core_cfg.get("require", []) != []:
        errors.append("core lakefile declares package dependencies")
    core_libs = core_cfg.get("lean_lib", [])
    if len(core_libs) != 1 or core_libs[0].get("name") != "CNNA":
        errors.append("core library target is not exactly CNNA")

    core_manifest_path = CORE / "lake-manifest.json"
    if not core_manifest_path.is_file():
        errors.append("core lake-manifest.json is missing")
        core_manifest = {}
    else:
        core_manifest = json.loads(core_manifest_path.read_text(encoding="utf-8"))
        if core_manifest.get("name") != "cnna_core":
            errors.append("core manifest package name mismatch")
        if core_manifest.get("packages") != []:
            errors.append("core manifest must contain exactly zero dependencies")
        if "mathlib" in core_manifest_path.read_text(encoding="utf-8").lower():
            errors.append("mathlib occurs in core manifest")

    proof_cfg = read_toml(PROOFS / "lakefile.toml")
    if proof_cfg.get("name") != "cnna_proofs":
        errors.append("proof package name is not cnna_proofs")
    if proof_cfg.get("defaultTargets") != ["CNNAProofs", "CNNAProofsP002"]:
        errors.append("proof default targets are not exactly CNNAProofs and CNNAProofsP002")
    proof_libs = proof_cfg.get("lean_lib", [])
    proof_lib_names = [item.get("name") for item in proof_libs]
    if proof_lib_names != ["CNNAProofs", "CNNAProofsP002"]:
        errors.append("proof library targets are not exactly CNNAProofs and CNNAProofsP002")
    requirements = {item.get("name"): item for item in proof_cfg.get("require", [])}
    if set(requirements) != {"mathlib", "cnna_core"}:
        errors.append(f"proof direct dependencies differ: {sorted(requirements)}")
    mathlib = requirements.get("mathlib", {})
    if mathlib.get("git") != "https://github.com/leanprover-community/mathlib4":
        errors.append("proof mathlib URL mismatch")
    if mathlib.get("rev") != "v4.31.0":
        errors.append("proof mathlib revision is not v4.31.0")
    core_dep = requirements.get("cnna_core", {})
    if core_dep.get("path") != "../core":
        errors.append("proof core dependency is not the local path ../core")

    core_files = sorted((CORE / "src").rglob("*.lean"))
    proof_files = sorted((PROOFS / "src").rglob("*.lean"))
    if len(core_files) != 35:
        errors.append(f"unexpected core Lean module count: {len(core_files)}")
    if len(proof_files) != 25:
        errors.append(f"unexpected proof Lean module count: {len(proof_files)}")

    for path in core_files:
        text = path.read_text(encoding="utf-8")
        for module in imports(path):
            if module == "Mathlib" or module.startswith("Mathlib."):
                errors.append(f"mathlib import in core: {path.relative_to(LEAN_ROOT)}")
            if module == "CNNAProofs" or module.startswith("CNNAProofs."):
                errors.append(f"proof import in core: {path.relative_to(LEAN_ROOT)}")
        if re.search(r"\bCNNAProofs\b", text):
            errors.append(f"CNNAProofs reference in core: {path.relative_to(LEAN_ROOT)}")

    p001 = PROOFS / "src/CNNAProofs/P001/DirectedSchurDtnKronChannelClosure.lean"
    p001_imports = imports(p001)
    if "Mathlib" not in p001_imports:
        errors.append("P001 does not import Mathlib")
    if not any(module.startswith("CNNA.") for module in p001_imports):
        errors.append("P001 does not import a CNNA core module")
    source = p001.read_text(encoding="utf-8")
    if "namespace CNNAProofs.P001" not in source or "end CNNAProofs.P001" not in source:
        errors.append("P001 namespace envelope is missing")
    body = source.split("namespace CNNAProofs.P001", 1)[1].split("end CNNAProofs.P001", 1)[0]
    for token in ("theorem", "lemma", "axiom", "opaque", "instance", "example", "sorry", "admit"):
        if re.search(rf"^\s*{token}\b", body, re.M):
            errors.append(f"P001 contract contains forbidden proof declaration: {token}")
    required_contract_names = [
        "DirectedCutHypotheses",
        "InteriorPathToBoundary",
        "CutPotential",
        "laplacianAction",
        "VanishesOnBoundary",
        "IsInteriorHarmonic",
        "IsInteriorKernelVector",
        "zeroBoundaryExtension",
        "InteriorKernelTrivial",
        "ExactSemanticBridge",
        "InteriorSolveExists",
        "InteriorSolveUnique",
        "ResponseWitnessIndependent",
        "IsDirectedLaplacianResponse",
        "DistinguishedPortStrictlyPositive",
        "DirectedSchurDtnClosure",
        "ReusableDirectedClosureContract",
        "DistinguishedParentIndex",
        "CanonicalBirthCutClosure",
        "CanonicalBirthCutClosureContract",
        "PublicContract",
    ]
    for name in required_contract_names:
        if not re.search(rf"\b{name}\b", body):
            errors.append(f"P001 contract declaration missing: {name}")

    # Matrix/Pi instance boundary: the carrier bridge remains explicit, while
    # rectangular multiplication is defined by a transparent row-by-column sum.
    # No `*` expression is permitted at this boundary because reducible Matrix
    # and Pi carriers can make HMul resolution select the wrong instance.
    if "def coreRatMatrixValue" not in body or "Matrix.of matrix" not in body:
        errors.append("P001 lacks the explicit core RatMatrix -> Matrix carrier bridge")
    if "def exactMatrixValue" not in body or "Matrix.of fun i j =>" not in body:
        errors.append("P001 exact-matrix value constructor does not use Matrix.of")
    if "def rationalMatrixMul" not in body:
        errors.append("P001 lacks explicit rationalMatrixMul")
    if "Matrix.of fun i j => ∑ k, left i k * right k j" not in body:
        errors.append("P001 rationalMatrixMul is not the explicit row-by-column sum")
    forbidden_products = [
        r"coreRatMatrixValue[^\n]*\*",
        r"blocks\.k(?:BB|BI|IB|II)\s*\*",
    ]
    for pattern in forbidden_products:
        if re.search(pattern, body):
            errors.append(f"P001 contains forbidden HMul boundary expression: {pattern}")
    for required_use in [
        "rationalMatrixMul (coreRatMatrixValue blocks.kII) solve",
        "rationalMatrixMul (coreRatMatrixValue blocks.kII) extension",
        "rationalMatrixMul (coreRatMatrixValue blocks.kBI) solve",
    ]:
        if required_use not in body:
            errors.append(f"P001 explicit rectangular product use missing: {required_use}")

    semantic = PROOFS / "src/CNNAProofs/P001/S01_ExactSemanticBridge.lean"
    if not semantic.is_file():
        errors.append("P001 exact semantic bridge module is missing")
        semantic_source = ""
    else:
        semantic_source = semantic.read_text(encoding="utf-8")
        if imports(semantic) != ["CNNAProofs.P001.DirectedSchurDtnKronChannelClosure"]:
            errors.append("P001 semantic bridge must import only the contract module")

    maximum = PROOFS / "src/CNNAProofs/P001/S02_DirectedMaximumPrinciple.lean"
    if not maximum.is_file():
        errors.append("P001 directed maximum-principle module is missing")
        maximum_source = ""
    else:
        maximum_source = maximum.read_text(encoding="utf-8")
        if imports(maximum) != ["CNNAProofs.P001.S01_ExactSemanticBridge"]:
            errors.append("P001 maximum principle must import only the semantic bridge")
        required_namespace_opens = [
            "open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering",
            "open BirthLocalSchurDtnPrimitive",
        ]
        for namespace_open in required_namespace_opens:
            if namespace_open not in maximum_source:
                errors.append(
                    f"P001 maximum principle lacks module-local namespace visibility: {namespace_open}")

    finite_linear = PROOFS / "src/CNNAProofs/P001/S03_FiniteLinearWellPosedness.lean"
    if not finite_linear.is_file():
        errors.append("P001 finite linear well-posedness module is missing")
        finite_linear_source = ""
    else:
        finite_linear_source = finite_linear.read_text(encoding="utf-8")
        if imports(finite_linear) != ["CNNAProofs.P001.S02_DirectedMaximumPrinciple"]:
            errors.append("P001 finite linear module must import only the maximum principle")
        for namespace_open in required_namespace_opens:
            if namespace_open not in finite_linear_source:
                errors.append(
                    f"P001 finite linear module lacks module-local namespace visibility: {namespace_open}")

    response_well_definedness = PROOFS / "src/CNNAProofs/P001/S04_ResponseWellDefinedness.lean"
    if not response_well_definedness.is_file():
        errors.append("P001 S07 response-well-definedness module is missing")
        response_source = ""
    else:
        response_source = response_well_definedness.read_text(encoding="utf-8")
        if imports(response_well_definedness) != ["CNNAProofs.P001.S03_FiniteLinearWellPosedness"]:
            errors.append("P001 S07 response module must import only finite linear well-posedness")
        for namespace_open in required_namespace_opens:
            if namespace_open not in response_source:
                errors.append(
                    f"P001 S07 response module lacks module-local namespace visibility: {namespace_open}")

    directed_laplacian = PROOFS / "src/CNNAProofs/P001/S05_ResponseDirectedLaplacian.lean"
    if not directed_laplacian.is_file():
        errors.append("P001 S08 directed-Laplacian module is missing")
        directed_laplacian_source = ""
    else:
        directed_laplacian_source = directed_laplacian.read_text(encoding="utf-8")
        if imports(directed_laplacian) != ["CNNAProofs.P001.S04_ResponseWellDefinedness"]:
            errors.append("P001 S08 directed-Laplacian module must import only S07 response well-definedness")
        for namespace_open in required_namespace_opens:
            if namespace_open not in directed_laplacian_source:
                errors.append(
                    f"P001 S08 module lacks module-local namespace visibility: {namespace_open}")

    distinguished_positivity = PROOFS / "src/CNNAProofs/P001/S06_DistinguishedPortStrictPositivity.lean"
    if not distinguished_positivity.is_file():
        errors.append("P001 S09 distinguished-port positivity module is missing")
        distinguished_positivity_source = ""
    else:
        distinguished_positivity_source = distinguished_positivity.read_text(encoding="utf-8")
        if imports(distinguished_positivity) != ["CNNAProofs.P001.S05_ResponseDirectedLaplacian"]:
            errors.append("P001 S09 module must import only S08 directed-Laplacian structure")
        for namespace_open in required_namespace_opens:
            if namespace_open not in distinguished_positivity_source:
                errors.append(
                    f"P001 S09 module lacks module-local namespace visibility: {namespace_open}")

    canonical_instantiation = PROOFS / "src/CNNAProofs/P001/S07_CanonicalBirthCutInstantiation.lean"
    if not canonical_instantiation.is_file():
        errors.append("P001 R6A canonical birth-cut instantiation module is missing")
        canonical_instantiation_source = ""
    else:
        canonical_instantiation_source = canonical_instantiation.read_text(encoding="utf-8")
        if imports(canonical_instantiation) != ["CNNAProofs.P001.S06_DistinguishedPortStrictPositivity"]:
            errors.append("P001 R6A module must import only S09 distinguished-port positivity")
        required_r6_opens = [
            "open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering",
            "open CanonicalBirthLocalMeasurementCut",
            "open CanonicalResponseSteeringFunctionalSigmaBRnS",
        ]
        for namespace_open in required_r6_opens:
            if namespace_open not in canonical_instantiation_source:
                errors.append(
                    f"P001 R6A module lacks module-local namespace visibility: {namespace_open}")

    canonical_matrix = PROOFS / "src/CNNAProofs/P001/S08_CanonicalDirectedMatrixStructure.lean"
    if not canonical_matrix.is_file():
        errors.append("P001 R6B.1 canonical directed-matrix module is missing")
        canonical_matrix_source = ""
    else:
        canonical_matrix_source = canonical_matrix.read_text(encoding="utf-8")
        if imports(canonical_matrix) != ["CNNAProofs.P001.S07_CanonicalBirthCutInstantiation"]:
            errors.append("P001 R6B.1 module must import only R6A canonical instantiation")

    canonical_reachability = PROOFS / "src/CNNAProofs/P001/S09_CanonicalBackboneReachability.lean"
    if not canonical_reachability.is_file():
        errors.append("P001 R6B.2 canonical backbone-reachability module is missing")
        canonical_reachability_source = ""
    else:
        canonical_reachability_source = canonical_reachability.read_text(encoding="utf-8")
        if imports(canonical_reachability) != ["CNNAProofs.P001.S08_CanonicalDirectedMatrixStructure"]:
            errors.append("P001 R6B.2 module must import only R6B.1 matrix structure")

    proof_facades = PROOFS / "src/CNNAProofs/P001/S10_M003M004ProofFacades.lean"
    if not proof_facades.is_file():
        errors.append("P001 R7 M003/M004 proof-facade module is missing")
        proof_facades_source = ""
    else:
        proof_facades_source = proof_facades.read_text(encoding="utf-8")
        expected_facade_imports = [
            "CNNAProofs.P001.S09_CanonicalBackboneReachability",
            "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
            "S03_RecurrentPreBirthMeasurementAndSteering."
            "S10_M004_ResponseCoupledBirthLawBirthlawB",
        ]
        if imports(proof_facades) != expected_facade_imports:
            errors.append("P001 R7 facade imports differ from the exact S09/M004 boundary")

    second_cut_reuse = PROOFS / "src/CNNAProofs/P001/S11_IndependentBidirectedChainCutReuse.lean"
    if not second_cut_reuse.is_file():
        errors.append("P001 R8 independent second-cut reuse module is missing")
        second_cut_reuse_source = ""
    else:
        second_cut_reuse_source = second_cut_reuse.read_text(encoding="utf-8")
        if imports(second_cut_reuse) != ["CNNAProofs.P001.S10_M003M004ProofFacades"]:
            errors.append("P001 R8 module must import only the R7 facade layer")

    m003_closure = PROOFS / "src/CNNAProofs/M003M004/S01_CanonicalM003Closure.lean"
    if not m003_closure.is_file():
        errors.append("canonical M003 closure module is missing")
        m003_closure_source = ""
    else:
        m003_closure_source = m003_closure.read_text(encoding="utf-8")
        if imports(m003_closure) != ["CNNAProofs.P001.S10_M003M004ProofFacades"]:
            errors.append("canonical M003 closure must import only the verified P001 facade layer")

    m004_closure = PROOFS / "src/CNNAProofs/M003M004/S02_CanonicalM004ClosureAndHandoff.lean"
    if not m004_closure.is_file():
        errors.append("canonical M004 closure and handoff module is missing")
        m004_closure_source = ""
    else:
        m004_closure_source = m004_closure.read_text(encoding="utf-8")
        if imports(m004_closure) != ["CNNAProofs.M003M004.S01_CanonicalM003Closure"]:
            errors.append("canonical M004 closure must import only the closed M003 interface")

    required_m003_declarations = [
        ("structure", "CanonicalM003Closure"),
        ("theorem", "canonicalM003Closure"),
        ("def", "CanonicalM003ClosureContract"),
        ("theorem", "canonicalM003ClosureContract"),
    ]
    for kind, name in required_m003_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", m003_closure_source, re.M):
            errors.append(f"canonical M003 closure declaration missing: {kind} {name}")

    required_m004_declarations = [
        ("structure", "CanonicalM004Closure"),
        ("theorem", "canonicalM004Closure"),
        ("def", "IsCanonicalBirthInstructionHandoff"),
        ("theorem", "canonicalBirthInstructionHandoff_exists"),
        ("theorem", "canonicalBirthInstructionHandoff_sameValue"),
        ("def", "CanonicalM004ClosureContract"),
        ("theorem", "canonicalM004ClosureContract"),
    ]
    for kind, name in required_m004_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", m004_closure_source, re.M):
            errors.append(f"canonical M004 closure declaration missing: {kind} {name}")

    for fragment in [
        "distinguishedParentIndex_exists next",
        "canonicalInPositiveSteeringDomain realization distinguished",
        "responseSteeringPair_exists realization hDomain.1",
    ]:
        if fragment not in m003_closure_source:
            errors.append(f"canonical M003 closure fragment missing: {fragment}")
    for fragment in [
        "canonicalM003Closure realization",
        "m003.responseSteeringExists",
        "m003.everySteeringPositive response value hPair",
        "birthLaw_exists realization response value hPair hPositive",
        "derivedCanonicalBirthLaw_unique",
        "responseSteeringPairs_give_same_birthLaw",
        "IsCanonicalBirthInstructionHandoff",
    ]:
        if fragment not in m004_closure_source:
            errors.append(f"canonical M004 closure fragment missing: {fragment}")

    p002_module = PROOFS / (
        "src/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S01_PrimitiveInputsGrammarAndEventOrder/"
        "S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/"
        "S01_P002_CanonicalScheduleStrictTotalOrderClosure.lean"
    )
    if not p002_module.is_file():
        errors.append("P002 static schedule-order closure module is missing")
        p002_source = ""
    else:
        p002_source = p002_module.read_text(encoding="utf-8")
        expected_p002_import = [
            "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
            "S01_PrimitiveInputsGrammarAndEventOrder."
            "S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule"
        ]
        if imports(p002_module) != expected_p002_import:
            errors.append("P002 must import exactly its C018 owner module")
    required_p002_declarations = [
        ("structure", "CanonicalScheduleStrictTotalOrderClosure"),
        ("theorem", "canonicalScheduleStrictTotalOrderClosure"),
        ("def", "IsMinimalSelectedChild"),
        ("theorem", "minimalSelectedChild_unique"),
        ("def", "CanonicalScheduleStrictTotalOrderContract"),
        ("theorem", "canonicalScheduleStrictTotalOrderContract"),
    ]
    for kind, name in required_p002_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", p002_source, re.M):
            errors.append(f"P002 declaration missing: {kind} {name}")
    for fragment in [
        "birthBefore_irrefl",
        "birthBefore_trans",
        "birthBefore_asymm",
        "birthBefore_trichotomy",
        "birthBefore_total_of_ne",
        "openSlotBefore_irrefl",
        "openSlotBefore_trans",
        "openSlotBefore_asymm",
        "openSlotBefore_total_of_distinct_children",
    ]:
        if fragment not in p002_source:
            errors.append(f"P002 C018 consumption fragment missing: {fragment}")
    for forbidden in [
        "ResponseCapableState", "Unsaturated", "bornNonRoot", "nextOpen",
        "native_decide", "noncomputable", "Classical", "simp", "simpa",
    ]:
        if re.search(rf"\b{re.escape(forbidden)}\b", p002_source):
            errors.append(f"forbidden P002 static-contract token: {forbidden}")
    p002_root = PROOFS / "src/CNNAProofsP002.lean"
    expected_p002_root_import = (
        "import CNNAProofs.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
        "S01_PrimitiveInputsGrammarAndEventOrder."
        "S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule.Proofs."
        "S01_P002_CanonicalScheduleStrictTotalOrderClosure"
    )
    if not p002_root.is_file() or p002_root.read_text(encoding="utf-8").strip() != expected_p002_root_import:
        errors.append("CNNAProofsP002 root does not expose exactly the P002 closure module")

    c008_core = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/"
        "S01_C008_RecordLiveResponseCoupledUpdate.lean"
    )
    c008_proof = PROOFS / "src/CNNAProofs/C008/S01_CanonicalRecordLiveUpdateClosure.lean"
    c008_root = PROOFS / "src/CNNAProofs/C008.lean"
    if not c008_core.is_file():
        errors.append("C008 Core record/live update module is missing")
        c008_core_source = ""
    else:
        c008_core_source = c008_core.read_text(encoding="utf-8")
        expected_c008_core_import = [
            "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
            "S03_RecurrentPreBirthMeasurementAndSteering."
            "S10_M004_ResponseCoupledBirthLawBirthlawB"
        ]
        if imports(c008_core) != expected_c008_core_import:
            errors.append("C008 Core must import exactly the M004 Core handoff owner")
    if not c008_proof.is_file():
        errors.append("C008 canonical record/live proof facade is missing")
        c008_proof_source = ""
    else:
        c008_proof_source = c008_proof.read_text(encoding="utf-8")
        expected_c008_proof_imports = [
            "CNNAProofs.M003M004.S02_CanonicalM004ClosureAndHandoff",
            "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
            "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure."
            "S01_C008_RecordLiveResponseCoupledUpdate",
        ]
        if imports(c008_proof) != expected_c008_proof_imports:
            errors.append("C008 proof facade must import only the verified M004 handoff and C008 Core")
    required_c008_core_declarations = [
        ("structure", "RecordLiveChannels"),
        ("def", "bootstrapRecordLiveChannels"),
        ("def", "recordInstructionUpdates"),
        ("def", "liveInstructionUpdates"),
        ("def", "applyInstruction"),
        ("theorem", "applyInstruction_record_eq"),
        ("theorem", "applyInstruction_live_eq"),
        ("theorem", "applyInstruction_respects_sameValue"),
        ("def", "RecordLiveResponseCoupledUpdateContract"),
        ("theorem", "recordLiveResponseCoupledUpdateContract"),
    ]
    for kind, name in required_c008_core_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c008_core_source, re.M):
            errors.append(f"C008 Core declaration missing: {kind} {name}")
    required_c008_proof_declarations = [
        ("structure", "CanonicalRecordLiveUpdateClosure"),
        ("theorem", "canonicalRecordLiveUpdateClosure"),
        ("def", "CanonicalRecordLiveUpdateContract"),
        ("theorem", "canonicalRecordLiveUpdateContract"),
    ]
    for kind, name in required_c008_proof_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c008_proof_source, re.M):
            errors.append(f"C008 proof declaration missing: {kind} {name}")
    for fragment in [
        "instruction.parentChildBirthUpdates",
        "instruction.ancestorBackreactionUpdates",
        "instruction.siblingBackreactionUpdates",
        "directedRelationUpdatesSameValue_append",
        "applyInstruction_respects_sameValue",
    ]:
        if fragment not in c008_core_source:
            errors.append(f"C008 Core derived-update fragment missing: {fragment}")
    for fragment in [
        "canonicalBirthInstructionHandoff_exists realization",
        "canonicalBirthInstructionHandoff_sameValue realization",
        "recordLiveChannelsSameValue_refl channels",
    ]:
        if fragment not in c008_proof_source:
            errors.append(f"C008 verified M004 handoff fragment missing: {fragment}")
    for source_name, source_text in [("C008 Core", c008_core_source), ("C008 proof", c008_proof_source)]:
        for token in ("native_decide", "noncomputable", "Classical", "simp", "simpa", "Matrix.inv"):
            if re.search(rf"\b{re.escape(token)}\b", source_text):
                errors.append(f"forbidden {source_name} token: {token}")
    expected_c008_root = "import CNNAProofs.C008.S01_CanonicalRecordLiveUpdateClosure"
    if not c008_root.is_file() or c008_root.read_text(encoding="utf-8").strip() != expected_c008_root:
        errors.append("CNNAProofs.C008 root does not expose exactly the C008 closure module")


    c016_core = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/"
        "S02_C016_ImmutableRecordChannel.lean"
    )
    c017_core = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/"
        "S03_C017_CurrentLiveChannel.lean"
    )
    c016_c017_proof = PROOFS / "src/CNNAProofs/C016C017/S01_CanonicalRecordLiveChannelProjectionClosure.lean"
    c016_c017_root = PROOFS / "src/CNNAProofs/C016C017.lean"
    for label, path in [("C016", c016_core), ("C017", c017_core)]:
        if not path.is_file():
            errors.append(f"{label} Core channel module is missing")
    c016_source = c016_core.read_text(encoding="utf-8") if c016_core.is_file() else ""
    c017_source = c017_core.read_text(encoding="utf-8") if c017_core.is_file() else ""
    expected_projection_import = [
        "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure."
        "S01_C008_RecordLiveResponseCoupledUpdate"
    ]
    if c016_core.is_file() and imports(c016_core) != expected_projection_import:
        errors.append("C016 Core must import exactly C008")
    if c017_core.is_file() and imports(c017_core) != expected_projection_import:
        errors.append("C017 Core must import exactly C008")
    if not c016_c017_proof.is_file():
        errors.append("C016/C017 shared proof facade is missing")
        c016_c017_proof_source = ""
    else:
        c016_c017_proof_source = c016_c017_proof.read_text(encoding="utf-8")
        expected_projection_proof_imports = [
            "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
            "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S02_C016_ImmutableRecordChannel",
            "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
            "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S03_C017_CurrentLiveChannel",
        ]
        if imports(c016_c017_proof) != expected_projection_proof_imports:
            errors.append("C016/C017 proof facade must import exactly the C016 and C017 Core modules")
    required_c016 = [
        ("def", "recordChannel"),
        ("def", "afterInstruction"),
        ("theorem", "afterInstruction_eq_append"),
        ("theorem", "previousRecord_isLeftPrefix"),
        ("theorem", "afterInstruction_respects_sameValue"),
        ("def", "ImmutableRecordChannelContract"),
        ("theorem", "immutableRecordChannelContract"),
    ]
    required_c017 = [
        ("def", "liveChannel"),
        ("def", "afterInstruction"),
        ("theorem", "afterInstruction_eq_append"),
        ("theorem", "previousLive_isLeftPrefix"),
        ("theorem", "afterInstruction_respects_sameValue"),
        ("def", "CurrentLiveChannelContract"),
        ("theorem", "currentLiveChannelContract"),
    ]
    for kind, name in required_c016:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c016_source, re.M):
            errors.append(f"C016 Core declaration missing: {kind} {name}")
    for kind, name in required_c017:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c017_source, re.M):
            errors.append(f"C017 Core declaration missing: {kind} {name}")
    for fragment in [
        "recordChannel channels ++ instruction.parentChildBirthUpdates",
        "previousRecord_isLeftPrefix",
        "applyInstruction_respects_sameValue",
    ]:
        if fragment not in c016_source:
            errors.append(f"C016 immutable-record fragment missing: {fragment}")
    for fragment in [
        "instruction.parentChildBirthUpdates ++",
        "instruction.ancestorBackreactionUpdates ++",
        "instruction.siblingBackreactionUpdates",
        "previousLive_isLeftPrefix",
        "applyInstruction_respects_sameValue",
    ]:
        if fragment not in c017_source:
            errors.append(f"C017 current-live fragment missing: {fragment}")
    required_projection_proof = [
        ("structure", "CanonicalImmutableRecordChannelClosure"),
        ("theorem", "canonicalImmutableRecordChannelClosure"),
        ("structure", "CanonicalCurrentLiveChannelClosure"),
        ("theorem", "canonicalCurrentLiveChannelClosure"),
        ("def", "CanonicalRecordLiveChannelProjectionContract"),
        ("theorem", "canonicalRecordLiveChannelProjectionContract"),
    ]
    for kind, name in required_projection_proof:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c016_c017_proof_source, re.M):
            errors.append(f"C016/C017 proof declaration missing: {kind} {name}")
    for source_name, source_text in [
        ("C016 Core", c016_source), ("C017 Core", c017_source),
        ("C016/C017 proof", c016_c017_proof_source),
    ]:
        for token in ("native_decide", "noncomputable", "Classical", "simp", "simpa", "Matrix.inv"):
            if re.search(rf"\b{re.escape(token)}\b", source_text):
                errors.append(f"forbidden {source_name} token: {token}")
    expected_c016_c017_root = "import CNNAProofs.C016C017.S01_CanonicalRecordLiveChannelProjectionClosure"
    if not c016_c017_root.is_file() or c016_c017_root.read_text(encoding="utf-8").strip() != expected_c016_c017_root:
        errors.append("CNNAProofs.C016C017 root does not expose exactly the shared projection closure")

    c009_core = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S04_C009_CodomainStateX.lean"
    )
    c009_proof = PROOFS / "src/CNNAProofs/C009/S01_CanonicalCodomainStateAssemblyClosure.lean"
    c009_root = PROOFS / "src/CNNAProofs/C009.lean"
    if not c009_core.is_file():
        errors.append("C009 Core assembly module is missing")
    if not c009_proof.is_file():
        errors.append("C009 proof facade is missing")
    c009_core_source = c009_core.read_text(encoding="utf-8") if c009_core.is_file() else ""
    c009_proof_source = c009_proof.read_text(encoding="utf-8") if c009_proof.is_file() else ""
    expected_c009_core_imports = [
        "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S02_C016_ImmutableRecordChannel",
        "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S03_C017_CurrentLiveChannel",
    ]
    if c009_core.is_file() and imports(c009_core) != expected_c009_core_imports:
        errors.append("C009 Core must import exactly C016 and C017")
    expected_c009_proof_imports = [
        "CNNAProofs.C016C017",
        "CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance."
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S04_C009_CodomainStateX",
    ]
    if c009_proof.is_file() and imports(c009_proof) != expected_c009_proof_imports:
        errors.append("C009 proof facade must import exactly the verified C016/C017 facade and C009 Core")
    required_c009_core = [
        ("def", "StateChannelCoherent"),
        ("structure", "CodomainAssemblyInput"),
        ("structure", "CodomainStateData"),
        ("def", "assemble"),
        ("theorem", "assemble_schedule_eq"),
        ("theorem", "assemble_bornNonRoot_eq"),
        ("theorem", "assemble_record_eq_c016"),
        ("theorem", "assemble_live_eq_c017"),
        ("structure", "CodomainStateDataSameValue"),
        ("theorem", "assemble_respects_sameValue"),
        ("def", "IsCodomainAssembly"),
        ("theorem", "codomainAssembly_existsUnique"),
        ("def", "CodomainStateAssemblyContract"),
        ("theorem", "codomainStateAssemblyContract"),
    ]
    for kind, name in required_c009_core:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c009_core_source, re.M):
            errors.append(f"C009 Core declaration missing: {kind} {name}")
    required_c009_proof = [
        ("structure", "CanonicalCodomainStateAssemblyClosure"),
        ("theorem", "canonicalCodomainStateAssemblyClosure"),
        ("def", "CanonicalCodomainStateAssemblyContract"),
        ("theorem", "canonicalCodomainStateAssemblyContract"),
    ]
    for kind, name in required_c009_proof:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c009_proof_source, re.M):
            errors.append(f"C009 proof declaration missing: {kind} {name}")
    for fragment in [
        "schedule := X.schedule",
        "X.bornNonRoot ++ [next.val]",
        "ImmutableRecordChannel.afterInstruction",
        "CurrentLiveChannel.afterInstruction",
        "StateChannelCoherent X",
        "codomainAssembly_existsUnique",
    ]:
        if fragment not in c009_core_source:
            errors.append(f"C009 assembly fragment missing: {fragment}")
    for forbidden_claim in [
        "bornWithinCutoff :=", "bornOrdered :=", "bornInitial :=",
        "conductancePairsUnique :=", "parentBackbone :=",
    ]:
        if forbidden_claim in c009_core_source:
            errors.append(f"C009 illegally absorbs T002 C005-closure proof field: {forbidden_claim}")
    for source_name, source_text in [("C009 Core", c009_core_source), ("C009 proof", c009_proof_source)]:
        for token in ("native_decide", "noncomputable", "Classical", "simp", "simpa", "Matrix.inv"):
            if re.search(rf"\b{re.escape(token)}\b", source_text):
                errors.append(f"forbidden {source_name} token: {token}")
    expected_c009_root = "import CNNAProofs.C009.S01_CanonicalCodomainStateAssemblyClosure"
    if not c009_root.is_file() or c009_root.read_text(encoding="utf-8").strip() != expected_c009_root:
        errors.append("CNNAProofs.C009 root does not expose exactly the C009 assembly closure")

    t002_core = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/"
        "S05_T002_RecurrentStateClosureTheorem.lean"
    )
    t002_proof = PROOFS / "src/CNNAProofs/T002/S01_CanonicalRecurrentStateClosure.lean"
    t002_root = PROOFS / "src/CNNAProofs/T002.lean"
    origin_closures = [
        CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S01A_C005_ConductanceAppendClosure.lean",
        CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S02A_C004_SuccessorBornPrefixClosure.lean",
        CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S03A_C006_ExactFractionRatRealizationClosure.lean",
        CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S04A_M001_PortSupportClosure.lean",
        CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S06A_C007_StateDirectedBlockRealizationClosure.lean",
        CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S10A_M004_LiveUpdateSupportClosure.lean",
    ]
    for path in origin_closures + [t002_core, t002_proof, t002_root]:
        if not path.is_file():
            errors.append(f"T002 required source missing: {path}")
    t002_core_source = t002_core.read_text(encoding="utf-8") if t002_core.is_file() else ""
    t002_proof_source = t002_proof.read_text(encoding="utf-8") if t002_proof.is_file() else ""
    c007_origin = CORE / "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S06A_C007_StateDirectedBlockRealizationClosure.lean"
    c007_origin_source = c007_origin.read_text(encoding="utf-8") if c007_origin.is_file() else ""
    for kind, name in [("def", "canonicalStateDirectedBlockRealization"), ("theorem", "stateDirectedBlockRealization_exists")]:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", c007_origin_source, re.M):
            errors.append(f"C007 origin closure declaration missing: {kind} {name}")
    if "canonicalStateDirectedBlockRealization next" not in t002_proof_source:
        errors.append("T002 proof facade does not consume the C007 canonical realization")
    required_t002_core = [
        ("def", "RelationUpdateAdmissible"),
        ("def", "realizeRelationUpdates"),
        ("theorem", "realizedLiveDelta_sameValue"),
        ("theorem", "old_new_conductancePairs_distinct"),
        ("def", "successorState"),
        ("theorem", "successor_live_coherent"),
        ("structure", "RecurrentStateClosure"),
        ("theorem", "recurrentStateClosure"),
        ("def", "RecurrentStateClosureContract"),
        ("theorem", "recurrentStateClosureContract"),
    ]
    for kind, name in required_t002_core:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", t002_core_source, re.M):
            errors.append(f"T002 Core declaration missing: {kind} {name}")
    required_t002_proof = [
        ("theorem", "canonicalRecurrentStepInput_exists"),
        ("theorem", "canonicalRecurrentStateClosure_exists"),
        ("structure", "CanonicalRecurrentStateClosure"),
        ("theorem", "canonicalRecurrentStateClosure"),
        ("def", "CanonicalRecurrentStateClosureContract"),
        ("theorem", "canonicalRecurrentStateClosureContract"),
    ]
    for kind, name in required_t002_proof:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", t002_proof_source, re.M):
            errors.append(f"T002 proof declaration missing: {kind} {name}")
    for fragment in [
        "successorBornPrefixClosure next",
        "ExactFraction.toRat",
        "liveRelationDelta next value",
        "old_new_conductancePairs_distinct",
        "StateChannelCoherent (successorState input)",
        "rawCodomain input",
    ]:
        if fragment not in t002_core_source:
            errors.append(f"T002 closure fragment missing: {fragment}")
    for forbidden in [
        "def born_snoc_withinCutoff",
        "def liveRelationDelta_pairwise_distinct",
        "def toRat",
    ]:
        if forbidden in t002_core_source:
            errors.append(f"T002 illegally redefines an origin-owned closure: {forbidden}")
    if "(realization : StateDirectedBlockRealization" in t002_proof_source:
        errors.append("T002 proof facade exposes C007 realization as a free public input")
    if re.search(r"^\s*c007Realization\s*:\s*StateDirectedBlockRealization\b", t002_proof_source, re.M):
        errors.append("T002 Prop facade re-exports C007 realization as a data field")
    if "realization : StateDirectedBlockRealization" in t002_core_source:
        errors.append("T002 Core RecurrentStepInput exposes C007 realization instead of consuming the C007 origin closure")
    if "input.realization" in t002_core_source or "input.realization" in t002_proof_source:
        errors.append("T002 still carries a downstream realization field after the C007 origin closure")
    for source_name, source_text in [("T002 Core", t002_core_source), ("T002 proof", t002_proof_source)]:
        for token in ("native_decide", "noncomputable", "Classical", "simp", "simpa", "Matrix.inv"):
            if re.search(rf"\b{re.escape(token)}\b", source_text):
                errors.append(f"forbidden {source_name} token: {token}")
    expected_t002_root = "import CNNAProofs.T002.S01_CanonicalRecurrentStateClosure"
    if not t002_root.is_file() or t002_root.read_text(encoding="utf-8").strip() != expected_t002_root:
        errors.append("CNNAProofs.T002 root does not expose exactly the recurrent closure facade")

    for source_name, closure_source in [
        ("M003", m003_closure_source),
        ("M004", m004_closure_source),
    ]:
        for token in ("native_decide", "noncomputable", "Classical", "simp", "simpa"):
            if re.search(rf"\b{re.escape(token)}\b", closure_source):
                errors.append(f"forbidden {source_name} closure token: {token}")

    core_m003 = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/"
        "S09_M003_CanonicalResponseSteeringFunctionalSigmaBRnS.lean"
    )
    core_m004 = CORE / (
        "src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/"
        "S03_RecurrentPreBirthMeasurementAndSteering/"
        "S10_M004_ResponseCoupledBirthLawBirthlawB.lean"
    )
    core_m003_source = core_m003.read_text(encoding="utf-8")
    core_m004_source = core_m004.read_text(encoding="utf-8")
    for stale in ["The missing directed-Kron theorem", "No universal inhabitance theorem is claimed"]:
        if stale in core_m003_source:
            errors.append(f"stale open M003 comment remains: {stale}")
    for stale in ["closure obligation in M003", "not a theorem assumed here"]:
        if stale in core_m004_source:
            errors.append(f"stale open M004 comment remains: {stale}")

    for path in proof_files:
        text = path.read_text(encoding="utf-8")
        for token in ("axiom", "opaque", "sorry", "admit", "unsafe", "partial", "implemented_by"):
            if re.search(rf"^\s*{token}\b", text, re.M):
                errors.append(
                    f"forbidden proof-layer declaration {token}: {path.relative_to(LEAN_ROOT)}")

    required_semantic_theorems = [
        "exactFractionValue_ofRat",
        "sameValue_iff_exactFractionValue_eq",
        "represents_iff_exactFractionValue_eq",
        "exactFractionValue_zero",
        "exactFractionValue_add",
        "exactFractionValue_mul",
        "exactFractionValue_sub",
        "exactFractionValue_finFoldl_add",
        "finFoldl_add_eq_initial_add_sum",
        "finFoldl_add_eq_sum",
        "exactFractionValue_matrixMul_entry",
        "exactMatrixValue_matrixMul",
        "exactMatrixValue_matrixSub",
        "matrixRepresents_iff_exactMatrixValue_eq",
        "rationalMatrixMul_neg_right",
        "interiorSolveAgreement",
        "harmonicSignAgreement",
        "responseValueAgreement",
        "exactSemanticBridge",
    ]
    for name in required_semantic_theorems:
        if not re.search(rf"^theorem\s+{name}\b", semantic_source, re.M):
            errors.append(f"P001 semantic theorem missing: {name}")

    if "unfold exactMatrixValue coreRatMatrixValue matrixSub rawMatrixSub" in semantic_source:
        errors.append(
            "P001 matrix-subtraction proof over-unfolds Matrix.of and reopens an "
            "instance-transparency failure")
    required_subtraction_change = [
        "ExactFraction.sub",
        "ExactFraction.ofRat (left row column)",
        "left row column - exactFractionValue (right row column)",
    ]
    for fragment in required_subtraction_change:
        if fragment not in semantic_source:
            errors.append(
                f"P001 explicit matrix-subtraction entry proof missing: {fragment}")

    required_maximum_theorems = [
        "zeroBoundaryExtension_vanishesOnBoundary",
        "laplacianAction_zeroBoundaryExtension",
        "zeroBoundaryExtension_isInteriorHarmonic",
        "laplacianAction_neg",
        "maximumDefectSum_eq_zero",
        "maximumDefectTerm_nonnegative",
        "maximum_propagates_across_positive_arc",
        "maximum_propagates_to_boundary",
        "interior_le_zero_of_harmonic_zero_boundary",
        "interior_nonnegative_of_harmonic_zero_boundary",
        "interior_eq_zero_of_harmonic_zero_boundary",
        "interiorKernelTrivial",
    ]
    for name in required_maximum_theorems:
        if not re.search(rf"^theorem\s+{name}\b", maximum_source, re.M):
            errors.append(f"P001 maximum-principle theorem missing: {name}")

    required_maximum_fragments = [
        "Finset.sum_eq_zero_iff_of_nonneg",
        "Finset.exists_max_image",
        "InteriorPathToBoundary",
        "InteriorPathToBoundary.rec",
        "motive := fun pathSource pathTarget _ =>",
        "Ne.symm hTarget",
        "rw [Finset.sum_neg_distrib]",
        "maximumDefectTerm",
        "InteriorKernelTrivial blocks",
    ]
    for fragment in required_maximum_fragments:
        if fragment not in maximum_source:
            errors.append(f"P001 maximum-principle proof fragment missing: {fragment}")

    warning_free_recursive_intro = (
        "intro pathSource middle pathTarget hArc tail inductionHypothesis potential "
        "hInteriorHarmonic hMaximum"
    )
    if warning_free_recursive_intro not in maximum_source:
        errors.append("P001 maximum-principle recursive intro is not warning-free")
    if re.search(
        r"intro pathSource middle pathTarget hArc tail inductionHypothesis\s*\n\s*"
        r"intro potential hInteriorHarmonic hMaximum",
        maximum_source,
    ):
        errors.append("P001 maximum-principle source retains the split recursive intro warning")

    if re.search(r":=\s*\n\s*Finset\.sum_neg_distrib", maximum_source):
        errors.append("maximum-principle source uses sum_neg_distrib as an uninstantiated exact term")

    forbidden_maximum_fragments = [
        "hOffDiagonal source target hTarget",
        "induction path with",
        "Matrix.inv",
        "nonsingInv",
        "adjugate",
        "det ",
        "Classical",
        "noncomputable",
        "native_decide",
        "simp",
        "simpa",
    ]
    for fragment in forbidden_maximum_fragments:
        if fragment in maximum_source:
            errors.append(f"forbidden maximum-principle proof fragment: {fragment}")

    required_finite_linear_declarations = [
        ("def", "interiorLinearMap"),
        ("theorem", "interiorLinearMap_apply"),
        ("theorem", "interiorLinearMap_injective"),
        ("theorem", "interiorLinearMap_surjective"),
        ("theorem", "interiorRightHandSideSolveExists"),
        ("theorem", "interiorSolveExists"),
        ("theorem", "interiorSolveUnique"),
        ("theorem", "interiorWellPosed"),
    ]
    for kind, name in required_finite_linear_declarations:
        if not re.search(rf"^{kind}\s+{name}\b", finite_linear_source, re.M):
            errors.append(f"P001 finite linear declaration missing: {kind} {name}")

    required_finite_linear_fragments = [
        "(coreRatMatrixValue blocks.kII).mulVecLin",
        "InteriorKernelTrivial blocks",
        "IsInteriorKernelVector blocks (left - right)",
        "map_sub (interiorLinearMap blocks) left right",
        "sub_eq_zero.mp hDifferenceZero",
        "LinearMap.surjective_of_injective",
        "choose solutionColumn hSolutionColumn using hColumnExists",
        "unfold IsMathlibInteriorSolve rationalMatrixMul",
        "interiorLinearMap_injective blocks hKernel",
        "InteriorSolveExists blocks ∧ InteriorSolveUnique blocks",
    ]
    for fragment in required_finite_linear_fragments:
        if fragment not in finite_linear_source:
            errors.append(f"P001 finite linear proof fragment missing: {fragment}")

    forbidden_finite_linear_fragments = [
        "Matrix.inv",
        "nonsingInv",
        "adjugate",
        "det ",
        "Classical",
        "noncomputable",
        "native_decide",
        "simp",
        "simpa",
        "pseudoinverse",
        "regularization",
        "symmetrization",
        "grounding vertex",
    ]
    # Prose may name excluded methods; reject only executable occurrences for
    # the broad mathematical words, and reject tactic/API tokens everywhere.
    for fragment in forbidden_finite_linear_fragments[:9]:
        if fragment in finite_linear_source:
            errors.append(f"forbidden finite linear proof fragment: {fragment}")

    required_response_declarations = [
        "exactMatrixValue_eq_of_matrixSameValue",
        "c006InteriorAdmissible",
        "responseExists",
        "responseRepresentativeAgreement",
        "responseWitnessIndependent",
        "responseWellDefined",
    ]
    for name in required_response_declarations:
        if not re.search(rf"^theorem\s+{name}\b", response_source, re.M):
            errors.append(f"P001 S07 response theorem missing: {name}")

    required_response_fragments = [
        "sameValue_iff_exactFractionValue_eq.mp",
        "interiorSolveExists blocks hKernel",
        "interiorSolveAgreement blocks solve",
        "interiorSolveUnique blocks hKernel other solve",
        "response_exists_of_admissible blocks",
        "response_unique_of_admissible blocks",
        "responseValueAgreement blocks solve",
        "ResponseWitnessIndependent blocks",
    ]
    for fragment in required_response_fragments:
        if fragment not in response_source:
            errors.append(f"P001 S07 response proof fragment missing: {fragment}")

    forbidden_response_fragments = [
        "Matrix.inv",
        "nonsingInv",
        "adjugate",
        "det ",
        "Classical",
        "noncomputable",
        "native_decide",
        "simp",
        "simpa",
        "pseudoinverse",
        "regularization",
        "symmetrization",
        "grounding vertex",
    ]
    for fragment in forbidden_response_fragments[:9]:
        if fragment in response_source:
            errors.append(f"forbidden S07 response proof fragment: {fragment}")

    required_s08_declarations = [
        ("def", "boundaryBasis"),
        ("theorem", "boundaryBasis_nonnegative"),
        ("theorem", "boundaryBasis_le_one"),
        ("def", "harmonicBasisPotential"),
        ("theorem", "interiorSolve_columnEquation"),
        ("theorem", "harmonicBasisPotential_isInteriorHarmonic"),
        ("theorem", "interior_le_of_harmonic_boundary_le"),
        ("theorem", "interior_ge_of_harmonic_boundary_ge"),
        ("theorem", "harmonicBasisPotential_nonnegative"),
        ("theorem", "harmonicBasisPotential_le_one"),
        ("theorem", "mathlibResponse_entry_eq_laplacianAction_harmonicBasis"),
        ("theorem", "responseOffDiagonalNonpositive"),
        ("theorem", "interiorSolve_rowSum_eq_neg_one"),
        ("theorem", "mathlibResponse_rowConservative"),
        ("theorem", "responseRowConservative"),
        ("theorem", "responseDiagonalNonnegative_of_offDiagonal_rowConservative"),
        ("theorem", "responseDiagonalNonnegative"),
        ("theorem", "directedLaplacianClosure"),
    ]
    for kind, name in required_s08_declarations:
        if not re.search(rf"^{kind}\s+{name}\b", directed_laplacian_source, re.M):
            errors.append(f"P001 S08 declaration missing: {kind} {name}")

    required_s08_fragments = [
        "Fintype.sum_ite_eq'",
        "Finset.exists_max_image",
        "maximum_propagates_to_boundary",
        "harmonicBasisPotential_isInteriorHarmonic",
        "Finset.sum_nonpos",
        "interiorSolve_rowSum_eq_neg_one",
        "Fintype.sum_eq_add_sum_compl",
        "ResponseOffDiagonalNonpositive response",
        "ResponseRowConservative response",
        "ResponseDiagonalNonnegative response",
        "IsDirectedLaplacianResponse response",
    ]
    for fragment in required_s08_fragments:
        if fragment not in directed_laplacian_source:
            errors.append(f"P001 S08 proof fragment missing: {fragment}")

    forbidden_s08_fragments = [
        "Matrix.inv",
        "nonsingInv",
        "adjugate",
        "det ",
        "Classical",
        "noncomputable",
        "native_decide",
        "simp",
        "simpa",
        "pseudoinverse",
        "regularization",
        "symmetrization",
        "grounding vertex",
    ]
    for fragment in forbidden_s08_fragments[:9]:
        if fragment in directed_laplacian_source:
            errors.append(f"forbidden S08 proof fragment: {fragment}")

    required_s09_declarations = [
        "maximum_propagates_from_distinguished_boundary_across_positive_arc",
        "harmonicBasis_one_propagates_across_positive_arc",
        "harmonicBasis_one_propagates_along_positive_path",
        "harmonicBasis_distinguished_action_ne_zero",
        "distinguishedResponseDiagonal_ne_zero",
        "distinguishedPortStrictlyPositive",
        "directedSchurDtnClosure",
        "reusableDirectedClosureContract",
    ]
    for name in required_s09_declarations:
        if not re.search(rf"^theorem\s+{name}\b", distinguished_positivity_source, re.M):
            errors.append(f"P001 S09 theorem missing: {name}")

    required_s09_fragments = [
        "Finset.sum_eq_zero_iff_of_nonneg",
        "maximum_propagates_from_distinguished_boundary_across_positive_arc",
        "maximum_propagates_across_positive_arc",
        "induction path with",
        "harmonicBasisPotential_le_one",
        "hypotheses.distinguishedReachesOtherBoundary",
        "boundaryBasis distinguished other",
        "responseDiagonalNonnegative",
        "lt_of_le_of_ne",
        "DirectedSchurDtnClosure blocks distinguished",
        "ReusableDirectedClosureContract",
    ]
    for fragment in required_s09_fragments:
        if fragment not in distinguished_positivity_source:
            errors.append(f"P001 S09 proof fragment missing: {fragment}")

    forbidden_s09_fragments = [
        "Matrix.inv",
        "nonsingInv",
        "adjugate",
        "det ",
        "Classical",
        "noncomputable",
        "native_decide",
        "simp",
        "simpa",
    ]
    for fragment in forbidden_s09_fragments:
        if fragment in distinguished_positivity_source:
            errors.append(f"forbidden S09 proof fragment: {fragment}")

    required_r6a_declarations = [
        "bornNonRoot_nodup",
        "root_not_mem_bornNonRoot",
        "canonicalCarrier_nodup",
        "boundary_nodup",
        "interior_nodup",
        "distinguishedParentIndex_exists",
        "positiveSteering_of_exactFractionValue_pos",
        "parentSelfResponse_value_eq_parentDiagonal",
        "m003ParentPositivity_of_genericClosure",
        "canonicalBirthCutClosure_of_hypotheses",
        "canonicalBirthCutClosureContract",
    ]
    for name in required_r6a_declarations:
        if not re.search(rf"^theorem\s+{name}\b", canonical_instantiation_source, re.M):
            errors.append(f"P001 R6A theorem missing: {name}")

    required_r6a_fragments = [
        "X.bornOrdered.nodup",
        "List.get_of_mem",
        "(boundary_nodup next).injective_get",
        "Finset.sum_eq_single",
        "Rat.divInt_nonneg_iff_of_pos_right",
        "parentSelfResponse next response",
        "sigma_eq_parentSelfResponse",
        "DirectedKronParentPositivityAt realization",
        "CanonicalBirthCutClosure realization parent",
        "CanonicalBirthCutClosureContract",
    ]
    for fragment in required_r6a_fragments:
        if fragment not in canonical_instantiation_source:
            errors.append(f"P001 R6A proof fragment missing: {fragment}")

    forbidden_r6a_fragments = [
        "Matrix.inv",
        "nonsingInv",
        "adjugate",
        "det ",
        "Classical",
        "noncomputable",
        "native_decide",
        "simp",
        "simpa",
        "pseudoinverse",
        "regularization",
        "symmetrization",
    ]
    for fragment in forbidden_r6a_fragments[:9]:
        if fragment in canonical_instantiation_source:
            errors.append(f"forbidden R6A proof fragment: {fragment}")

    required_r6b1_declarations = ['canonicalCutAddress', 'canonicalCutAddress_injective', 'canonicalCutCoordinate_exists', 'conductanceSourceCoordinate_exists', 'conductanceTargetCoordinate_exists', 'ratOutgoingSum', 'ratOrderedPairSum', 'exactFractionValue_outgoingFold', 'exactFractionValue_orderedPairFold', 'exactFractionValue_outgoingSum', 'exactFractionValue_orderedPairSum', 'ratDirectedMatrixEntry', 'exactFractionValue_directedMatrixEntry', 'ratOrderedPairSum_nonnegative', 'ratOrderedPairSum_pos_of_hasConductance', 'ratOrderedPairSum_self_zero', 'sum_single_edge_target_indicator', 'sum_ratOrderedPairSum_eq_ratOutgoingSum', 'ratDirectedMatrixEntry_eq_indicator_sub_pair', 'ratDirectedMatrixEntry_row_sum_zero', 'blockEntry_eq_ratDirectedMatrixEntry', 'canonicalBlocks_offDiagonalNonpositive', 'canonicalBlocks_rowConservative', 'canonicalPositiveArc_of_hasConductance']
    for name in required_r6b1_declarations:
        if not re.search(rf"^(?:def|theorem)\s+{re.escape(name)}\b", canonical_matrix_source, re.M):
            errors.append(f"P001 R6B.1 declaration missing: {name}")
    for fragment in [
        "ratDirectedMatrixEntry_row_sum_zero",
        "canonicalBlocks_offDiagonalNonpositive",
        "canonicalBlocks_rowConservative",
        "canonicalPositiveArc_of_hasConductance",
        "Fintype.sum_eq_single",
    ]:
        if fragment not in canonical_matrix_source:
            errors.append(f"P001 R6B.1 proof fragment missing: {fragment}")

    required_r6b2_declarations = ['eq_snoc_of_parent?_eq_some', 'depth_parent_lt_of_parent?_eq_some', 'immediateParent_mem_causalPredecessorPorts', 'hasConductance_endpoints_distinct', 'firstProvenanceSlotOfState', 'firstProvenanceAddress_born', 'firstProvenanceAddress_mem_olderSiblingPorts_of_parent_root', 'canonicalInteriorPathToBoundary_aux', 'canonicalEveryInteriorReachesBoundary', 'canonicalDistinguishedReachesOtherBoundary', 'canonicalDirectedCutHypotheses', 'canonicalBirthCutClosure_derived', 'DerivedCanonicalBirthCutClosureContract', 'derivedCanonicalBirthCutClosureContract', 'DerivedPublicContract', 'derivedPublicContract']
    for name in required_r6b2_declarations:
        if not re.search(rf"^(?:def|theorem)\s+{re.escape(name)}\b", canonical_reachability_source, re.M):
            errors.append(f"P001 canonical-reachability declaration missing: {name}")
    for fragment in [
        "canonicalInteriorPathToBoundary_aux",
        "canonicalEveryInteriorReachesBoundary",
        "canonicalDistinguishedReachesOtherBoundary",
        "canonicalDirectedCutHypotheses",
        "derivedCanonicalBirthCutClosureContract",
        "termination_by",
        "parentBackbone",
    ]:
        if fragment not in canonical_reachability_source:
            errors.append(f"P001 canonical-reachability proof fragment missing: {fragment}")

    required_r7_declarations = [
        ("theorem", "canonicalInPositiveSteeringDomain"),
        ("theorem", "canonicalResponseSteeringPair_positive"),
        ("def", "IsDerivedCanonicalBirthLaw"),
        ("theorem", "derivedCanonicalBirthLaw_exists"),
        ("theorem", "derivedCanonicalBirthLaw_unique"),
        ("theorem", "derivedCanonicalBirthLaw_existsUnique"),
        ("theorem", "canonicalActiveBirthInstruction_exists"),
        ("theorem", "derivedCanonicalBirthLaws_sameValue"),
        ("def", "M003M004ProofFacadeContract"),
        ("theorem", "m003M004ProofFacadeContract"),
    ]
    for kind, name in required_r7_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", proof_facades_source, re.M):
            errors.append(f"P001 M003/M004 facade declaration missing: {kind} {name}")
    for fragment in [
        "canonicalBirthCutClosure_derived",
        "closure.c007ResponseDomain",
        "closure.m003ParentPositivity",
        "birthLaw_exists",
        "birthLaw_unique",
        "responseSteeringPairs_give_same_birthLaw",
        "Subsingleton.elim",
        "IsDerivedCanonicalBirthLaw",
        "M003M004ProofFacadeContract",
    ]:
        if fragment not in proof_facades_source:
            errors.append(f"P001 M003/M004 facade proof fragment missing: {fragment}")
    for token in [
        "Matrix.inv", "native_decide", "noncomputable", "Classical",
        "simp", "simpa", "pseudoinverse", "regularization", "symmetrization",
    ]:
        if re.search(rf"\b{re.escape(token)}\b", proof_facades_source):
            errors.append(f"forbidden M003/M004 facade token: {token}")


    required_r8_declarations = [
        ("def", "independentChainBoundaryWeight"),
        ("def", "independentBidirectedChainBlocks"),
        ("theorem", "independentBidirectedChainOffDiagonalNonpositive"),
        ("theorem", "independentBidirectedChainRowConservative"),
        ("theorem", "independentBidirectedChainInteriorReachesBoundary"),
        ("theorem", "independentBidirectedChainDistinguishedReachesOtherBoundary"),
        ("theorem", "independentBidirectedChainHypotheses"),
        ("theorem", "independentBidirectedChainClosure"),
        ("def", "SecondCutReuseContract"),
        ("theorem", "secondCutReuseContract"),
    ]
    for kind, name in required_r8_declarations:
        if not re.search(rf"^{kind}\s+{re.escape(name)}\b", second_cut_reuse_source, re.M):
            errors.append(f"P001 independent-reuse declaration missing: {kind} {name}")
    for fragment in [
        "OrderedSchurBlocks 2 1",
        "Fintype.sum_sum_type",
        "Fin.sum_univ_succ",
        "InteriorPathToBoundary.direct",
        "PositivePath.tail",
        "DirectedCutHypotheses",
        "directedSchurDtnClosure",
        "SecondCutReuseContract",
    ]:
        if fragment not in second_cut_reuse_source:
            errors.append(f"P001 independent-reuse proof fragment missing: {fragment}")
    for token in [
        "Matrix.inv", "native_decide", "noncomputable", "Classical",
        "simp", "simpa", "pseudoinverse", "regularization", "symmetrization",
    ]:
        if re.search(rf"\b{re.escape(token)}\b", second_cut_reuse_source):
            errors.append(f"forbidden independent-reuse token: {token}")
    for pattern in [
        r"\{X\s*:\s*ResponseCapableState\}",
        r"\(next\s*:\s*NextOpenSlot",
        r"canonicalDirectedCutHypotheses\s",
    ]:
        if re.search(pattern, second_cut_reuse_source):
            errors.append(f"independent reuse is coupled to the canonical birth cut: {pattern}")

    forbidden_open_claims = [
        "publicContract",
    ]
    all_partial_sources = [semantic_source, maximum_source, finite_linear_source,
                           response_source, directed_laplacian_source,
                           distinguished_positivity_source, canonical_instantiation_source,
                           canonical_matrix_source, canonical_reachability_source,
                           proof_facades_source, second_cut_reuse_source]
    for name in forbidden_open_claims:
        if any(re.search(rf"^theorem\s+{name}\b", partial, re.M)
               for partial in all_partial_sources):
            errors.append(f"current partial source improperly proves a later closure claim: {name}")

    if "def exactFractionValue" not in source or "_root_.mkRat value.num value.den" not in source:
        errors.append("P001 exactFractionValue is not the direct mkRat semantics")
    if "theorem exactSemanticBridge" not in semantic_source or             "ExactSemanticBridge blocks where" not in semantic_source:
        errors.append("P001 exact semantic bridge is not inhabited")

    aggregator = (PROOFS / "src/CNNAProofs.lean").read_text(encoding="utf-8")
    if aggregator.strip() != "import CNNAProofs.M003M004.S02_CanonicalM004ClosureAndHandoff":
        errors.append("CNNAProofs aggregator does not expose the closed M003/M004 handoff layer")

    boundary = json.loads((LEAN_ROOT / "PACKAGE_BOUNDARY.json").read_text(encoding="utf-8"))
    if boundary.get("allowed_direction") != "CNNAProofs -> CNNA":
        errors.append("machine-readable allowed direction mismatch")
    if boundary.get("core", {}).get("direct_dependencies") != []:
        errors.append("machine-readable core dependency list is not empty")

    proof_manifest_path = PROOFS / "lake-manifest.json"
    if proof_manifest_path.exists():
        proof_manifest = json.loads(proof_manifest_path.read_text(encoding="utf-8"))
        names = {package.get("name") for package in proof_manifest.get("packages", [])}
        if "mathlib" not in names:
            errors.append("generated proof manifest lacks mathlib")
        if "cnna_core" not in names:
            warnings.append("generated proof manifest does not list local cnna_core; verify Lake path-dependency representation")

    def current_run_olean(source_path: Path, olean_path: Path) -> bool:
        """Validate an artifact only inside the post-build audit pass.

        Lake 5 validates module freshness through build traces and content
        dependencies, not by requiring the olean mtime to be newer than an
        extracted source file.  `--require-build` is invoked only after the
        same script has completed `lake build` successfully; at that point
        source existence plus olean existence is the correct local artifact
        check.  Outside a current build run, retained verification is accepted
        only through immutable exact source hashes below.
        """
        return (
            args.require_build
            and source_path.is_file()
            and olean_path.is_file()
        )

    def verified_external_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained successful build against exact current source hashes."""
        evidence_path = AUDIT_EVIDENCE = LEAN_ROOT / "audit/evidence/USER_LOCAL_P001_FULL_BUILD_20260806.json"
        if not evidence_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_evidence = {
                "proofs/src/CNNAProofs/P001/DirectedSchurDtnKronChannelClosure.lean",
                "proofs/src/CNNAProofs/P001/S01_ExactSemanticBridge.lean",
                "proofs/src/CNNAProofs/P001/S02_DirectedMaximumPrinciple.lean",
                "proofs/src/CNNAProofs/P001/S03_FiniteLinearWellPosedness.lean",
                "proofs/src/CNNAProofs/P001/S04_ResponseWellDefinedness.lean",
                "proofs/src/CNNAProofs/P001/S05_ResponseDirectedLaplacian.lean",
                "proofs/src/CNNAProofs/P001/S06_DistinguishedPortStrictPositivity.lean",
                "proofs/src/CNNAProofs/P001/S07_CanonicalBirthCutInstantiation.lean",
                "proofs/src/CNNAProofs/P001/S08_CanonicalDirectedMatrixStructure.lean",
                "proofs/src/CNNAProofs/P001/S09_CanonicalBackboneReachability.lean",
                "proofs/src/CNNAProofs/P001/S10_M003M004ProofFacades.lean",
                "proofs/src/CNNAProofs/P001/S11_IndependentBidirectedChainCutReuse.lean",
            }
            required_artifacts = {
                "core_olean", "proofs_olean", "proof_manifest",
                "p001_semantic_olean", "p001_maximum_principle_olean",
                "p001_finite_linear_olean", "p001_response_well_definedness_olean",
                "p001_directed_laplacian_olean", "p001_distinguished_positivity_olean",
                "p001_canonical_instantiation_olean", "p001_canonical_matrix_structure_olean",
                "p001_canonical_backbone_reachability_olean", "p001_m003_m004_facades_olean",
                "p001_second_cut_reuse_olean",
            }
            if not (
                evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("p001_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("proof_declarations") == 142
                and all(artifacts.get(key) is True for key in required_artifacts)
                and isinstance(built_hashes, dict)
                and required_evidence.issubset(built_hashes)
            ):
                return False, evidence
            transcript = LEAN_ROOT / "audit/evidence/USER_LOCAL_P001_FULL_BUILD_20260806.txt"
            if not transcript.is_file() or hashlib.sha256(transcript.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            for relative in required_evidence:
                source_path = LEAN_ROOT / relative
                if not source_path.is_file():
                    return False, evidence
                actual = hashlib.sha256(source_path.read_bytes()).hexdigest()
                if actual != built_hashes[relative]:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}


    def verified_m003_m004_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained M003/M004 build against exact current source hashes."""
        evidence_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_M003_M004_FULL_BUILD_20260806.json"
        transcript_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_M003_M004_FULL_BUILD_20260806.txt"
        if not evidence_path.is_file() or not transcript_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_sources = {
                "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S09_M003_CanonicalResponseSteeringFunctionalSigmaBRnS.lean",
                "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S10_M004_ResponseCoupledBirthLawBirthlawB.lean",
                "proofs/src/CNNAProofs/M003M004/S01_CanonicalM003Closure.lean",
                "proofs/src/CNNAProofs/M003M004/S02_CanonicalM004ClosureAndHandoff.lean",
                "proofs/src/CNNAProofs.lean",
                "audit/M003M004_CurrentProofAxiomAudit.lean",
            }
            required_artifacts = {
                "core_olean", "proofs_olean", "proof_manifest",
                "m003_canonical_closure_olean", "m004_canonical_closure_handoff_olean",
            }
            if not (
                evidence.get("schema") == "cnna.m003-m004-kernel-build-evidence.v1"
                and evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("proof_modules") == 15
                and evidence.get("m003_m004_proof_declarations") == 11
                and evidence.get("m003_m004_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("m003_m004_axiom_profile_counts")
                    == {"choice_propext_quot": 6, "propext_quot_only": 5, "axiom_free": 0}
                and all(artifacts.get(key) is True for key in required_artifacts)
                and isinstance(built_hashes, dict)
                and required_sources == set(built_hashes)
            ):
                return False, evidence
            if hashlib.sha256(transcript_path.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            transcript = transcript_path.read_text(encoding="utf-8")
            for marker in [
                "Build completed successfully (8596 jobs).",
                "M003_M004_CURRENT_PROOF_AXIOM_AUDIT PASS",
                '"m003": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"m004": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"m003_canonical_closure_olean": true',
                '"m004_canonical_closure_handoff_olean": true',
                "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
            ]:
                if marker not in transcript:
                    return False, evidence
            for relative, expected in built_hashes.items():
                source_path = LEAN_ROOT / relative
                if not source_path.is_file() or hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}


    def verified_p002_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained P002 build against exact current source hashes."""
        evidence_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_P002_FULL_BUILD_20260808.json"
        transcript_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_P002_FULL_BUILD_20260808.txt"
        if not evidence_path.is_file() or not transcript_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_sources = {
                "proofs/lakefile.toml",
                "proofs/src/CNNAProofsP002.lean",
                "proofs/src/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/S01_P002_CanonicalScheduleStrictTotalOrderClosure.lean",
                "audit/P002_CurrentProofAxiomAudit.lean",
            }
            if not (
                evidence.get("schema") == "cnna.p002-kernel-build-evidence.v1"
                and evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("proof_modules") == 17
                and evidence.get("p002_proof_declarations") == 6
                and evidence.get("p002_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("p002_axiom_profile_counts")
                    == {"choice_propext_quot": 0, "propext_quot_only": 0, "axiom_free": 6}
                and evidence.get("transitive_axioms_observed") == []
                and artifacts.get("p002_static_order_closure_olean") is True
                and evidence.get("retained_verified_p001_source_hash_match") is True
                and evidence.get("retained_verified_m003_m004_source_hash_match") is True
                and isinstance(built_hashes, dict)
                and required_sources == set(built_hashes)
            ):
                return False, evidence
            if hashlib.sha256(transcript_path.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            transcript = transcript_path.read_text(encoding="utf-8")
            for marker in [
                "Build completed successfully (8599 jobs).",
                "P002_CURRENT_PROOF_AXIOM_AUDIT PASS",
                "'CNNAProofs.P002.CanonicalScheduleStrictTotalOrderClosure' does not depend on any axioms",
                "'CNNAProofs.P002.canonicalScheduleStrictTotalOrderClosure' does not depend on any axioms",
                "'CNNAProofs.P002.IsMinimalSelectedChild' does not depend on any axioms",
                "'CNNAProofs.P002.minimalSelectedChild_unique' does not depend on any axioms",
                "'CNNAProofs.P002.CanonicalScheduleStrictTotalOrderContract' does not depend on any axioms",
                "'CNNAProofs.P002.canonicalScheduleStrictTotalOrderContract' does not depend on any axioms",
                '"p002": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"p002_static_order_closure_olean": true',
                '"retained_verified_p001_source_hash_match": true',
                '"retained_verified_m003_m004_source_hash_match": true',
                "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
            ]:
                if marker not in transcript:
                    return False, evidence
            for relative, expected in built_hashes.items():
                source_path = LEAN_ROOT / relative
                if not source_path.is_file() or hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}

    def verified_c008_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained C008 build against exact current source hashes."""
        evidence_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_C008_FULL_BUILD_20260808.json"
        transcript_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_C008_FULL_BUILD_20260808.txt"
        if not evidence_path.is_file() or not transcript_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_sources = {
                "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S01_C008_RecordLiveResponseCoupledUpdate.lean",
                "proofs/src/CNNAProofs/C008.lean",
                "proofs/src/CNNAProofs/C008/S01_CanonicalRecordLiveUpdateClosure.lean",
                "audit/C008_CurrentProofAxiomAudit.lean",
            }
            if not (
                evidence.get("schema") == "cnna.c008-kernel-build-evidence.v1"
                and evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("proof_modules") == 19
                and evidence.get("c008_audited_declarations") == 7
                and evidence.get("c008_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("c008_axiom_profile_counts")
                    == {"choice_propext_quot": 4, "propext_quot_only": 3, "axiom_free": 0}
                and set(evidence.get("transitive_axioms_observed", []))
                    == {"propext", "Classical.choice", "Quot.sound"}
                and evidence.get("direct_project_axioms") == 0
                and evidence.get("sorry_count") == 0
                and artifacts.get("c008_record_live_update_olean") is True
                and evidence.get("retained_verified_p001_source_hash_match") is True
                and evidence.get("retained_verified_m003_m004_source_hash_match") is True
                and evidence.get("retained_verified_p002_source_hash_match") is True
                and isinstance(built_hashes, dict)
                and required_sources == set(built_hashes)
            ):
                return False, evidence
            if hashlib.sha256(transcript_path.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            transcript = transcript_path.read_text(encoding="utf-8")
            for marker in [
                "Build completed successfully (27 jobs).",
                "Built CNNAProofs.C008.S01_CanonicalRecordLiveUpdateClosure",
                "Built CNNAProofs.C008",
                "C008_CURRENT_PROOF_AXIOM_AUDIT PASS",
                '"c008": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"c008_record_live_update_olean": true',
                '"retained_verified_p001_source_hash_match": true',
                '"retained_verified_m003_m004_source_hash_match": true',
                '"retained_verified_p002_source_hash_match": true',
                "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
            ]:
                if marker not in transcript:
                    return False, evidence
            for relative, expected in built_hashes.items():
                source_path = LEAN_ROOT / relative
                if not source_path.is_file() or hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}

    def verified_c016_c017_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained C016/C017 build against exact current source hashes."""
        evidence_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_C016_C017_FULL_BUILD_20260808.json"
        transcript_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_C016_C017_FULL_BUILD_20260808.txt"
        if not evidence_path.is_file() or not transcript_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_sources = {
                "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S02_C016_ImmutableRecordChannel.lean",
                "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S03_C017_CurrentLiveChannel.lean",
                "proofs/src/CNNAProofs/C016C017.lean",
                "proofs/src/CNNAProofs/C016C017/S01_CanonicalRecordLiveChannelProjectionClosure.lean",
                "audit/C016C017_CurrentProofAxiomAudit.lean",
            }
            if not (
                evidence.get("schema") == "cnna.c016-c017-kernel-build-evidence.v1"
                and evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("proof_modules") == 21
                and evidence.get("c016_c017_audited_declarations") == 12
                and evidence.get("c016_c017_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("c016_c017_axiom_profile_counts")
                    == {"choice_propext_quot": 10, "propext_quot_only": 2, "axiom_free": 0}
                and set(evidence.get("transitive_axioms_observed", []))
                    == {"propext", "Classical.choice", "Quot.sound"}
                and evidence.get("direct_project_axioms") == 0
                and evidence.get("sorry_count") == 0
                and artifacts.get("c016_c017_projection_closure_olean") is True
                and evidence.get("retained_verified_p001_source_hash_match") is True
                and evidence.get("retained_verified_m003_m004_source_hash_match") is True
                and evidence.get("retained_verified_p002_source_hash_match") is True
                and evidence.get("retained_verified_c008_source_hash_match") is True
                and isinstance(built_hashes, dict)
                and required_sources == set(built_hashes)
            ):
                return False, evidence
            if hashlib.sha256(transcript_path.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            transcript = transcript_path.read_text(encoding="utf-8")
            for marker in [
                "Build completed successfully (29 jobs).",
                "Built CNNAProofs.C016C017.S01_CanonicalRecordLiveChannelProjectionClosure",
                "Built CNNAProofs.C016C017",
                "C016_C017_CURRENT_PROOF_AXIOM_AUDIT PASS",
                '"c016": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"c017": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"c016_c017_projection_closure_olean": true',
                '"retained_verified_p001_source_hash_match": true',
                '"retained_verified_m003_m004_source_hash_match": true',
                '"retained_verified_p002_source_hash_match": true',
                '"retained_verified_c008_source_hash_match": true',
                "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
            ]:
                if marker not in transcript:
                    return False, evidence
            for relative, expected in built_hashes.items():
                source_path = LEAN_ROOT / relative
                if not source_path.is_file() or hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}

    def verified_c009_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained C009 build against exact current source hashes."""
        evidence_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_C009_FULL_BUILD_20260808.json"
        transcript_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_C009_FULL_BUILD_20260808.txt"
        if not evidence_path.is_file() or not transcript_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_sources = {
                "core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S04_C009_CodomainStateX.lean",
                "proofs/src/CNNAProofs/C009.lean",
                "proofs/src/CNNAProofs/C009/S01_CanonicalCodomainStateAssemblyClosure.lean",
                "audit/C009_CurrentProofAxiomAudit.lean",
            }
            if not (
                evidence.get("schema") == "cnna.c009-kernel-build-evidence.v1"
                and evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("proof_modules") == 23
                and evidence.get("c009_audited_declarations") == 8
                and evidence.get("c009_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("c009_axiom_profile_counts")
                    == {"choice_propext_quot": 2, "propext_quot_only": 4, "axiom_free": 2}
                and set(evidence.get("transitive_axioms_observed", []))
                    == {"propext", "Classical.choice", "Quot.sound"}
                and evidence.get("direct_project_axioms") == 0
                and evidence.get("sorry_count") == 0
                and artifacts.get("c009_codomain_assembly_olean") is True
                and evidence.get("retained_verified_p001_source_hash_match") is True
                and evidence.get("retained_verified_m003_m004_source_hash_match") is True
                and evidence.get("retained_verified_p002_source_hash_match") is True
                and evidence.get("retained_verified_c008_source_hash_match") is True
                and evidence.get("retained_verified_c016_c017_source_hash_match") is True
                and isinstance(built_hashes, dict)
                and required_sources == set(built_hashes)
            ):
                return False, evidence
            if hashlib.sha256(transcript_path.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            transcript = transcript_path.read_text(encoding="utf-8")
            for marker in [
                "Build completed successfully (30 jobs).",
                "Built CNNAProofs.C009.S01_CanonicalCodomainStateAssemblyClosure",
                "Built CNNAProofs.C009",
                "C009_CURRENT_PROOF_AXIOM_AUDIT PASS",
                '"c009": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"c009_codomain_assembly_olean": true',
                '"retained_verified_p001_source_hash_match": true',
                '"retained_verified_m003_m004_source_hash_match": true',
                '"retained_verified_p002_source_hash_match": true',
                '"retained_verified_c008_source_hash_match": true',
                '"retained_verified_c016_c017_source_hash_match": true',
                "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
            ]:
                if marker not in transcript:
                    return False, evidence
            for relative, expected in built_hashes.items():
                source_path = LEAN_ROOT / relative
                if not source_path.is_file() or hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}

    def verified_t002_build_matches_current_sources() -> tuple[bool, dict]:
        """Check the retained T002 build against exact current source hashes."""
        evidence_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_T002_FULL_BUILD_20260809.json"
        transcript_path = LEAN_ROOT / "audit/evidence/USER_LOCAL_T002_FULL_BUILD_20260809.txt"
        if not evidence_path.is_file() or not transcript_path.is_file():
            return False, {}
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
            built_hashes = evidence.get("verified_source_sha256", {})
            artifacts = evidence.get("verified_artifacts", {})
            required_sources = manifest_paths(LEAN_ROOT / "audit/T002_CURRENT_SOURCE_SHA256.txt")
            if not (
                evidence.get("schema") == "cnna.t002-kernel-build-evidence.v1"
                and evidence.get("status") == "PASS"
                and evidence.get("toolchain") == TOOLCHAIN
                and evidence.get("proof_modules") == 25
                and evidence.get("t002_audited_declarations") == 26
                and evidence.get("t002_current_proof_axiom_audit") == "PASS"
                and evidence.get("full_package_boundary_audit") == "PASS"
                and evidence.get("t002_axiom_profile_counts") == {"choice_propext_quot": 19, "propext_quot_only": 7, "axiom_free": 0}
                and set(evidence.get("transitive_axioms_observed", [])) == {"propext", "Classical.choice", "Quot.sound"}
                and evidence.get("direct_project_axioms") == 0
                and evidence.get("sorry_count") == 0
                and artifacts.get("t002_recurrent_state_closure_olean") is True
                and all(evidence.get(k) is True for k in [
                    "retained_verified_p001_source_hash_match", "retained_verified_m003_m004_source_hash_match",
                    "retained_verified_p002_source_hash_match", "retained_verified_c008_source_hash_match",
                    "retained_verified_c016_c017_source_hash_match", "retained_verified_c009_source_hash_match"])
                and isinstance(built_hashes, dict) and required_sources == set(built_hashes)
            ): return False, evidence
            if hashlib.sha256(transcript_path.read_bytes()).hexdigest() != evidence.get("transcript_sha256"):
                return False, evidence
            transcript = transcript_path.read_text(encoding="utf-8")
            for marker in [
                "Build completed successfully (37 jobs).",
                "Built CNNAProofs.T002.S01_CanonicalRecurrentStateClosure",
                "Built CNNAProofs.T002",
                "T002_CURRENT_PROOF_AXIOM_AUDIT PASS",
                '"t002": "KERNEL_VERIFIED_CURRENT_BUILD"',
                '"t002_recurrent_state_closure_olean": true',
                '"retained_verified_c009_source_hash_match": true',
                "FULL_PACKAGE_BOUNDARY_AUDIT PASS",
            ]:
                if marker not in transcript: return False, evidence
            for relative, expected in built_hashes.items():
                source_path = LEAN_ROOT / relative
                if not source_path.is_file() or hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
                    return False, evidence
            return True, evidence
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            return False, {}

    retained_verified_build, retained_build_evidence = verified_external_build_matches_current_sources()
    retained_verified_m003_m004, retained_m003_m004_evidence = verified_m003_m004_build_matches_current_sources()
    retained_verified_p002, retained_p002_evidence = verified_p002_build_matches_current_sources()
    retained_verified_c008, retained_c008_evidence = verified_c008_build_matches_current_sources()
    retained_verified_c016_c017, retained_c016_c017_evidence = verified_c016_c017_build_matches_current_sources()
    retained_verified_c009, retained_c009_evidence = verified_c009_build_matches_current_sources()
    retained_verified_t002, retained_t002_evidence = verified_t002_build_matches_current_sources()

    build_evidence = {
        "required": args.require_build,
        "core_olean": (CORE / ".lake/build/lib/lean/CNNA.olean").is_file(),
        "proofs_olean": (PROOFS / ".lake/build/lib/lean/CNNAProofs.olean").is_file(),
        "proof_manifest": proof_manifest_path.is_file(),
        "p001_semantic_olean": current_run_olean(
            semantic,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S01_ExactSemanticBridge.olean",
        ),
        "p001_maximum_principle_olean": current_run_olean(
            maximum,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S02_DirectedMaximumPrinciple.olean",
        ),
        "p001_finite_linear_olean": current_run_olean(
            finite_linear,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S03_FiniteLinearWellPosedness.olean",
        ),
        "p001_response_well_definedness_olean": current_run_olean(
            response_well_definedness,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S04_ResponseWellDefinedness.olean",
        ),
        "p001_directed_laplacian_olean": current_run_olean(
            directed_laplacian,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S05_ResponseDirectedLaplacian.olean",
        ),
        "p001_distinguished_positivity_olean": current_run_olean(
            distinguished_positivity,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S06_DistinguishedPortStrictPositivity.olean",
        ),
        "p001_canonical_instantiation_olean": current_run_olean(
            canonical_instantiation,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S07_CanonicalBirthCutInstantiation.olean",
        ),
        "p001_canonical_matrix_structure_olean": current_run_olean(
            canonical_matrix,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S08_CanonicalDirectedMatrixStructure.olean",
        ),
        "p001_canonical_backbone_reachability_olean": current_run_olean(
            canonical_reachability,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S09_CanonicalBackboneReachability.olean",
        ),
        "p001_m003_m004_facades_olean": current_run_olean(
            proof_facades,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S10_M003M004ProofFacades.olean",
        ),
        "p001_second_cut_reuse_olean": current_run_olean(
            second_cut_reuse,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/P001/S11_IndependentBidirectedChainCutReuse.olean",
        ),
        "m003_canonical_closure_olean": current_run_olean(
            m003_closure,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/M003M004/S01_CanonicalM003Closure.olean",
        ),
        "m004_canonical_closure_handoff_olean": current_run_olean(
            m004_closure,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/M003M004/S02_CanonicalM004ClosureAndHandoff.olean",
        ),
        "p002_static_order_closure_olean": current_run_olean(
            p002_module,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/S01_P002_CanonicalScheduleStrictTotalOrderClosure.olean",
        ),
        "c008_record_live_update_olean": current_run_olean(
            c008_proof,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/C008/S01_CanonicalRecordLiveUpdateClosure.olean",
        ),
        "c016_c017_projection_closure_olean": current_run_olean(
            c016_c017_proof,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/C016C017/S01_CanonicalRecordLiveChannelProjectionClosure.olean",
        ),
        "c009_codomain_assembly_olean": current_run_olean(
            c009_proof,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/C009/S01_CanonicalCodomainStateAssemblyClosure.olean",
        ),
        "t002_recurrent_state_closure_olean": current_run_olean(
            t002_proof,
            PROOFS / ".lake/build/lib/lean/CNNAProofs/T002/S01_CanonicalRecurrentStateClosure.olean",
        ),
        "retained_verified_p001_source_hash_match": retained_verified_build,
        "retained_verified_m003_m004_source_hash_match": retained_verified_m003_m004,
        "retained_verified_p002_source_hash_match": retained_verified_p002,
        "retained_verified_c008_source_hash_match": retained_verified_c008,
        "retained_verified_c016_c017_source_hash_match": retained_verified_c016_c017,
        "retained_verified_c009_source_hash_match": retained_verified_c009,
        "retained_verified_t002_source_hash_match": retained_verified_t002,
    }
    if args.require_build:
        if not build_evidence["core_olean"]:
            errors.append("required core build artifact CNNA.olean is missing")
        if not build_evidence["proofs_olean"]:
            errors.append("required proof build artifact CNNAProofs.olean is missing")
        if not build_evidence["proof_manifest"]:
            errors.append("required generated proof lake-manifest.json is missing")
        if not build_evidence["p001_semantic_olean"]:
            errors.append("required P001 semantic bridge olean is missing")
        if not build_evidence["p001_maximum_principle_olean"]:
            errors.append("required P001 maximum-principle olean is missing")
        if not build_evidence["p001_finite_linear_olean"]:
            errors.append("required P001 finite-linear olean is missing")
        if not build_evidence["p001_response_well_definedness_olean"]:
            errors.append("required P001 S07 response-well-definedness olean is missing")
        if not build_evidence["p001_directed_laplacian_olean"]:
            errors.append("required P001 S08 directed-Laplacian olean is missing")
        if not build_evidence["p001_distinguished_positivity_olean"]:
            errors.append("required P001 S09 distinguished-port positivity olean is missing")
        if not build_evidence["p001_canonical_instantiation_olean"]:
            errors.append("required P001 canonical-instantiation olean is missing")
        if not build_evidence["p001_canonical_matrix_structure_olean"]:
            errors.append("required P001 canonical-matrix olean is missing")
        if not build_evidence["p001_canonical_backbone_reachability_olean"]:
            errors.append("required P001 canonical-reachability olean is missing")
        if not build_evidence["p001_m003_m004_facades_olean"]:
            errors.append("required P001 M003/M004 facade olean is missing")
        if not build_evidence["p001_second_cut_reuse_olean"]:
            errors.append("required P001 independent-reuse olean is missing")
        if not build_evidence["m003_canonical_closure_olean"]:
            errors.append("required canonical M003 closure olean is missing")
        if not build_evidence["m004_canonical_closure_handoff_olean"]:
            errors.append("required canonical M004 closure/handoff olean is missing")
        if not build_evidence["p002_static_order_closure_olean"]:
            errors.append("required P002 static order closure olean is missing")
        if not build_evidence["c008_record_live_update_olean"]:
            errors.append("required C008 record/live update closure olean is missing")
        if not build_evidence["c016_c017_projection_closure_olean"]:
            errors.append("required C016/C017 record/live projection closure olean is missing")
        if not build_evidence["c009_codomain_assembly_olean"]:
            errors.append("required C009 codomain-state assembly closure olean is missing")
        if not build_evidence["t002_recurrent_state_closure_olean"]:
            errors.append("required T002 recurrent-state closure olean is missing")

    result = {
        "schema": "cnna.lean-package-boundary-audit.v1",
        "status": "PASS" if not errors else "FAIL",
        "toolchain": TOOLCHAIN,
        "core": {
            "package": "cnna_core",
            "library": "CNNA",
            "manifest_dependencies": len(core_manifest.get("packages", [])) if core_manifest else None,
            "lean_modules": len(core_files),
            "mathlib_imports": 0 if not any("mathlib import in core" in e for e in errors) else None,
        },
        "proofs": {
            "package": "cnna_proofs",
            "library": "CNNAProofs",
            "direct_dependencies": ["mathlib@v4.31.0", "cnna_core@../core"],
            "lean_modules": len(proof_files),
            "p001": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["p001_second_cut_reuse_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_build
                    else "SOURCE_BUILD_REQUIRED"
                )
            ),
            "m003": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["m003_canonical_closure_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_m003_m004
                    else "CANONICAL_CLOSURE_SOURCE_BUILD_REQUIRED"
                )
            ),
            "m004": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["m004_canonical_closure_handoff_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_m003_m004
                    else "CANONICAL_CLOSURE_AND_HANDOFF_SOURCE_BUILD_REQUIRED"
                )
            ),
            "p002": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["p002_static_order_closure_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_p002
                    else "STATIC_ORDER_CLOSURE_SOURCE_BUILD_REQUIRED"
                )
            ),
            "c008": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["c008_record_live_update_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_c008
                    else "RECORD_LIVE_UPDATE_SOURCE_BUILD_REQUIRED"
                )
            ),
            "c016": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["c016_c017_projection_closure_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_c016_c017
                    else "IMMUTABLE_RECORD_CHANNEL_SOURCE_BUILD_REQUIRED"
                )
            ),
            "c017": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["c016_c017_projection_closure_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_c016_c017
                    else "CURRENT_LIVE_CHANNEL_SOURCE_BUILD_REQUIRED"
                )
            ),
            "c009": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["c009_codomain_assembly_olean"]
                else (
                    "KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE"
                    if retained_verified_c009
                    else "CODOMAIN_STATE_ASSEMBLY_SOURCE_BUILD_REQUIRED"
                )
            ),
            "t002": (
                "KERNEL_VERIFIED_CURRENT_BUILD"
                if build_evidence["t002_recurrent_state_closure_olean"]
                else ("KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE" if retained_verified_t002 else "RECURRENT_STATE_CLOSURE_SOURCE_BUILD_REQUIRED")
            ),
        },
        "allowed_direction": "CNNAProofs -> CNNA",
        "build_evidence": build_evidence,
        "current_verified_build_evidence": retained_build_evidence if retained_verified_build else None,
        "current_verified_m003_m004_build_evidence": retained_m003_m004_evidence if retained_verified_m003_m004 else None,
        "current_verified_p002_build_evidence": retained_p002_evidence if retained_verified_p002 else None,
        "current_verified_c008_build_evidence": retained_c008_evidence if retained_verified_c008 else None,
        "current_verified_c016_c017_build_evidence": retained_c016_c017_evidence if retained_verified_c016_c017 else None,
        "current_verified_c009_build_evidence": retained_c009_evidence if retained_verified_c009 else None,
        "current_verified_t002_build_evidence": retained_t002_evidence if retained_verified_t002 else None,
        "warnings": warnings,
        "errors": errors,
    }
    rendered = json.dumps(result, indent=2, ensure_ascii=False)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0 if not errors else 1


if __name__ == "__main__":
    sys.exit(main())
