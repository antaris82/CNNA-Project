#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
LEAN_ROOT="$(cd "$HERE/.." && pwd -P)"
CORE="$LEAN_ROOT/core"
PROOFS="$LEAN_ROOT/proofs"
P001_HASH_FILE="$HERE/P001_CURRENT_SOURCE_SHA256.txt"
M003_M004_HASH_FILE="$HERE/M003M004_CURRENT_SOURCE_SHA256.txt"
P002_HASH_FILE="$HERE/P002_CURRENT_SOURCE_SHA256.txt"
C008_HASH_FILE="$HERE/C008_CURRENT_SOURCE_SHA256.txt"
C016_C017_HASH_FILE="$HERE/C016C017_CURRENT_SOURCE_SHA256.txt"
C009_HASH_FILE="$HERE/C009_CURRENT_SOURCE_SHA256.txt"
T002_HASH_FILE="$HERE/T002_CURRENT_SOURCE_SHA256.txt"
AUDIT_INFRA_HASH_FILE="$HERE/AUDIT_INFRASTRUCTURE_CURRENT_SOURCE_SHA256.txt"

fail() {
  echo "FAIL: $*" >&2
  exit 2
}

assert_not_trash_path() {
  local label="$1"
  local path="$2"
  case "$path" in
    */.local/share/Trash/*)
      fail "$label resolves inside the desktop Trash: $path. Extract/copy the package to a fresh workspace and run from there."
      ;;
  esac
}

assert_source_hash_manifest() {
  local label="$1"
  local manifest="$2"
  [[ -f "$manifest" ]] || fail "missing expected $label source hash manifest: $manifest"
  local expected relative actual source_path
  while read -r expected relative; do
    [[ -n "${expected:-}" ]] || continue
    [[ "${expected:0:1}" != "#" ]] || continue
    source_path="$LEAN_ROOT/$relative"
    [[ -f "$source_path" ]] || fail "missing $label source from hash manifest: $source_path"
    actual="$(sha256sum "$source_path" | awk '{print $1}')"
    [[ "$actual" == "$expected" ]] || fail "$label current source hash mismatch for $relative: expected $expected, got $actual"
  done < "$manifest"
}

assert_lake_environment_current() {
  local package_dir="$1"
  local label="$2"
  local env_path
  env_path="$(cd "$package_dir" && lake env printenv LEAN_PATH)"
  case "$env_path" in
    */.local/share/Trash/*)
      cat >&2 <<MSG
FAIL: stale Lake environment for $label still references the desktop Trash.
Current package root: $package_dir
LEAN_PATH: $env_path
Repair from the current lean root with:
  ./audit/run_package_boundary_audit.sh --reset-lake-state
Then rerun:
  ./audit/run_package_boundary_audit.sh --build
MSG
      exit 2
      ;;
  esac
}

assert_not_trash_path "audit directory" "$HERE"
assert_not_trash_path "Lean root" "$LEAN_ROOT"
assert_not_trash_path "core package" "$(cd "$CORE" && pwd -P)"
assert_not_trash_path "proof package" "$(cd "$PROOFS" && pwd -P)"
assert_source_hash_manifest "P001" "$P001_HASH_FILE"
assert_source_hash_manifest "M003/M004" "$M003_M004_HASH_FILE"
assert_source_hash_manifest "P002" "$P002_HASH_FILE"
assert_source_hash_manifest "C008" "$C008_HASH_FILE"
assert_source_hash_manifest "C016/C017" "$C016_C017_HASH_FILE"
assert_source_hash_manifest "C009" "$C009_HASH_FILE"
assert_source_hash_manifest "T002" "$T002_HASH_FILE"
assert_source_hash_manifest "audit infrastructure" "$AUDIT_INFRA_HASH_FILE"

python3 "$HERE/check_package_boundary.py"

case "${1:-}" in
  "")
    echo "STATIC_PACKAGE_BOUNDARY_AUDIT PASS"
    ;;
  --reset-lake-state)
    assert_not_trash_path "Lean root" "$LEAN_ROOT"
    echo "Removing stale local Lake state from current workspace only:"
    echo "  $CORE/.lake"
    echo "  $PROOFS/.lake"
    rm -rf "$CORE/.lake" "$PROOFS/.lake"
    rm -f "$PROOFS/lake-manifest.json"
    echo "LAKE_STATE_RESET PASS"
    ;;
  --build)
    command -v lake >/dev/null 2>&1 || fail "lake is not available in PATH"
    unset LEAN_PATH LEAN_SRC_PATH
    export ELAN_NO_OVERRIDE_NOTICE=1

    (
      cd "$CORE"
      lake update
      assert_lake_environment_current "$CORE" "core"
      lake --no-ansi build
    )
    PROOF_BUILD_LOG="$(mktemp)"
    AXIOM_LOG="$(mktemp)"
    M003_M004_AXIOM_LOG="$(mktemp)"
    P002_AXIOM_LOG="$(mktemp)"
    C008_AXIOM_LOG="$(mktemp)"
    C016_C017_AXIOM_LOG="$(mktemp)"
    C009_AXIOM_LOG="$(mktemp)"
    T002_AXIOM_LOG="$(mktemp)"
    trap 'rm -f "$PROOF_BUILD_LOG" "$AXIOM_LOG" "$M003_M004_AXIOM_LOG" "$P002_AXIOM_LOG" "$C008_AXIOM_LOG" "$C016_C017_AXIOM_LOG" "$C009_AXIOM_LOG" "$T002_AXIOM_LOG"' EXIT
    (
      cd "$PROOFS"
      lake update
      assert_lake_environment_current "$PROOFS" "proofs"
      lake exe cache get
      lake --no-ansi build 2>&1 | tee "$PROOF_BUILD_LOG"
      # C008 deliberately remains outside the retained CNNAProofs default root so
      # that the kernel-verified M003/M004 facade root and the P002 lakefile hash
      # remain byte-identical.  Lake supports explicit module targets via +Module.
      # Build the C008 public root (and therefore its imported proof facade) before
      # the axiom audit imports CNNAProofs.C008.
      lake --no-ansi build +CNNAProofs.C008 2>&1 | tee -a "$PROOF_BUILD_LOG"
      # C016/C017 are separate construction nodes but share one thin proof-facing
      # projection closure. Build its explicit public root before the axiom audit.
      lake --no-ansi build +CNNAProofs.C016C017 2>&1 | tee -a "$PROOF_BUILD_LOG"
      # C009 is the next isolated proof-facing construction root.
      lake --no-ansi build +CNNAProofs.C009 2>&1 | tee -a "$PROOF_BUILD_LOG"
      # T002 owns a separate proof-facing theorem root and consumes origin-local
      # closure modules without changing frozen predecessor source files.
      lake --no-ansi build +CNNAProofs.T002 2>&1 | tee -a "$PROOF_BUILD_LOG"
    )
    if grep -Eq "warning: src/(CNNAProofs/(P001|M003M004|C008|C016C017|C009|T002|Derivation/.*P002)|CNNAProofsP002\.lean)" "$PROOF_BUILD_LOG"; then
      fail "P001, M003/M004, P002, C008, C016/C017, C009, or T002 proof build emitted a source warning"
    fi

    (
      cd "$PROOFS"
      lake env lean "$HERE/P001_CurrentProofAxiomAudit.lean" 2>&1 | tee "$AXIOM_LOG"
    )
    python3 - "$AXIOM_LOG" <<'PYAXIOM'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
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
    "interiorLinearMap",
    "interiorLinearMap_apply",
    "interiorLinearMap_injective",
    "interiorLinearMap_surjective",
    "interiorRightHandSideSolveExists",
    "interiorSolveExists",
    "interiorSolveUnique",
    "interiorWellPosed",
    "exactMatrixValue_eq_of_matrixSameValue",
    "c006InteriorAdmissible",
    "responseExists",
    "responseRepresentativeAgreement",
    "responseWitnessIndependent",
    "responseWellDefined",
    "boundaryBasis",
    "boundaryBasis_nonnegative",
    "boundaryBasis_le_one",
    "harmonicBasisPotential",
    "interiorSolve_columnEquation",
    "harmonicBasisPotential_isInteriorHarmonic",
    "interior_le_of_harmonic_boundary_le",
    "interior_ge_of_harmonic_boundary_ge",
    "harmonicBasisPotential_nonnegative",
    "harmonicBasisPotential_le_one",
    "mathlibResponse_entry_eq_laplacianAction_harmonicBasis",
    "responseOffDiagonalNonpositive",
    "interiorSolve_rowSum_eq_neg_one",
    "mathlibResponse_rowConservative",
    "responseRowConservative",
    "responseDiagonalNonnegative_of_offDiagonal_rowConservative",
    "responseDiagonalNonnegative",
    "directedLaplacianClosure",
    "maximum_propagates_from_distinguished_boundary_across_positive_arc",
    "harmonicBasis_one_propagates_across_positive_arc",
    "harmonicBasis_one_propagates_along_positive_path",
    "harmonicBasis_distinguished_action_ne_zero",
    "distinguishedResponseDiagonal_ne_zero",
    "distinguishedPortStrictlyPositive",
    "directedSchurDtnClosure",
    "reusableDirectedClosureContract",
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
    "canonicalCutAddress",
    "canonicalCutAddress_injective",
    "canonicalCutCoordinate_exists",
    "conductanceSourceCoordinate_exists",
    "conductanceTargetCoordinate_exists",
    "ratOutgoingSum",
    "ratOrderedPairSum",
    "exactFractionValue_outgoingFold",
    "exactFractionValue_orderedPairFold",
    "exactFractionValue_outgoingSum",
    "exactFractionValue_orderedPairSum",
    "ratDirectedMatrixEntry",
    "exactFractionValue_directedMatrixEntry",
    "ratOrderedPairSum_nonnegative",
    "ratOrderedPairSum_pos_of_hasConductance",
    "ratOrderedPairSum_self_zero",
    "sum_single_edge_target_indicator",
    "sum_ratOrderedPairSum_eq_ratOutgoingSum",
    "ratDirectedMatrixEntry_eq_indicator_sub_pair",
    "ratDirectedMatrixEntry_row_sum_zero",
    "blockEntry_eq_ratDirectedMatrixEntry",
    "canonicalBlocks_offDiagonalNonpositive",
    "canonicalBlocks_rowConservative",
    "canonicalPositiveArc_of_hasConductance",
    "eq_snoc_of_parent?_eq_some",
    "depth_parent_lt_of_parent?_eq_some",
    "immediateParent_mem_causalPredecessorPorts",
    "hasConductance_endpoints_distinct",
    "firstProvenanceSlotOfState",
    "firstProvenanceAddress_born",
    "firstProvenanceAddress_mem_olderSiblingPorts_of_parent_root",
    "canonicalInteriorPathToBoundary_aux",
    "canonicalEveryInteriorReachesBoundary",
    "canonicalDistinguishedReachesOtherBoundary",
    "canonicalDirectedCutHypotheses",
    "canonicalBirthCutClosure_derived",
    "DerivedCanonicalBirthCutClosureContract",
    "derivedCanonicalBirthCutClosureContract",
    "DerivedPublicContract",
    "derivedPublicContract",
    "canonicalInPositiveSteeringDomain",
    "canonicalResponseSteeringPair_positive",
    "IsDerivedCanonicalBirthLaw",
    "derivedCanonicalBirthLaw_exists",
    "derivedCanonicalBirthLaw_unique",
    "derivedCanonicalBirthLaw_existsUnique",
    "canonicalActiveBirthInstruction_exists",
    "derivedCanonicalBirthLaws_sameValue",
    "M003M004ProofFacadeContract",
    "m003M004ProofFacadeContract",
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
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(f"FAIL: unresolved P001 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("p001_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("p001_current_proof_axiom_profiles END")
print("P001_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYAXIOM

    (
      cd "$PROOFS"
      lake env lean "$HERE/M003M004_CurrentProofAxiomAudit.lean" 2>&1 | tee "$M003_M004_AXIOM_LOG"
    )
    python3 - "$M003_M004_AXIOM_LOG" <<'PYM003M004'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
    "CanonicalM003Closure",
    "canonicalM003Closure",
    "CanonicalM003ClosureContract",
    "canonicalM003ClosureContract",
    "CanonicalM004Closure",
    "canonicalM004Closure",
    "IsCanonicalBirthInstructionHandoff",
    "canonicalBirthInstructionHandoff_exists",
    "canonicalBirthInstructionHandoff_sameValue",
    "CanonicalM004ClosureContract",
    "canonicalM004ClosureContract",
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(
            f"FAIL: unresolved M003/M004 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("m003_m004_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("m003_m004_current_proof_axiom_profiles END")
print("M003_M004_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYM003M004

    (
      cd "$PROOFS"
      lake env lean "$HERE/P002_CurrentProofAxiomAudit.lean" 2>&1 | tee "$P002_AXIOM_LOG"
    )
    python3 - "$P002_AXIOM_LOG" <<'PYP002'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
    "CanonicalScheduleStrictTotalOrderClosure",
    "canonicalScheduleStrictTotalOrderClosure",
    "IsMinimalSelectedChild",
    "minimalSelectedChild_unique",
    "CanonicalScheduleStrictTotalOrderContract",
    "canonicalScheduleStrictTotalOrderContract",
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(f"FAIL: unresolved P002 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("p002_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("p002_current_proof_axiom_profiles END")
print("P002_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYP002

    (
      cd "$PROOFS"
      lake env lean "$HERE/C008_CurrentProofAxiomAudit.lean" 2>&1 | tee "$C008_AXIOM_LOG"
    )
    python3 - "$C008_AXIOM_LOG" <<'PYC008'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
    "applyInstruction_respects_sameValue",
    "RecordLiveResponseCoupledUpdateContract",
    "recordLiveResponseCoupledUpdateContract",
    "CanonicalRecordLiveUpdateClosure",
    "canonicalRecordLiveUpdateClosure",
    "CanonicalRecordLiveUpdateContract",
    "canonicalRecordLiveUpdateContract",
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(f"FAIL: unresolved C008 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("c008_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("c008_current_proof_axiom_profiles END")
print("C008_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYC008


    (
      cd "$PROOFS"
      lake env lean "$HERE/C016C017_CurrentProofAxiomAudit.lean" 2>&1 | tee "$C016_C017_AXIOM_LOG"
    )
    python3 - "$C016_C017_AXIOM_LOG" <<'PYC016C017'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
    "ImmutableRecordChannel.afterInstruction_respects_sameValue",
    "ImmutableRecordChannel.ImmutableRecordChannelContract",
    "ImmutableRecordChannel.immutableRecordChannelContract",
    "CurrentLiveChannel.afterInstruction_respects_sameValue",
    "CurrentLiveChannel.CurrentLiveChannelContract",
    "CurrentLiveChannel.currentLiveChannelContract",
    "CanonicalImmutableRecordChannelClosure",
    "canonicalImmutableRecordChannelClosure",
    "CanonicalCurrentLiveChannelClosure",
    "canonicalCurrentLiveChannelClosure",
    "CanonicalRecordLiveChannelProjectionContract",
    "canonicalRecordLiveChannelProjectionContract",
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(f"FAIL: unresolved C016/C017 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("c016_c017_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("c016_c017_current_proof_axiom_profiles END")
print("C016_C017_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYC016C017

    (
      cd "$PROOFS"
      lake env lean "$HERE/C009_CurrentProofAxiomAudit.lean" 2>&1 | tee "$C009_AXIOM_LOG"
    )
    python3 - "$C009_AXIOM_LOG" <<'PYC009'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
    "CodomainStateX.assemble_respects_sameValue",
    "CodomainStateX.codomainAssembly_existsUnique",
    "CodomainStateX.CodomainStateAssemblyContract",
    "CodomainStateX.codomainStateAssemblyContract",
    "CanonicalCodomainStateAssemblyClosure",
    "canonicalCodomainStateAssemblyClosure",
    "CanonicalCodomainStateAssemblyContract",
    "canonicalCodomainStateAssemblyContract",
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(f"FAIL: unresolved C009 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("c009_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("c009_current_proof_axiom_profiles END")
print("C009_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYC009


    (
      cd "$PROOFS"
      lake env lean "$HERE/T002_CurrentProofAxiomAudit.lean" 2>&1 | tee "$T002_AXIOM_LOG"
    )
    python3 - "$T002_AXIOM_LOG" <<'PYT002'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
profiles = {}
for declaration, body in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, flags=re.S
):
    profiles[declaration] = tuple(
        sorted(item.strip() for item in body.replace("\n", " ").split(",") if item.strip())
    )
for declaration in re.findall(r"'([^']+)' does not depend on any axioms", text):
    profiles[declaration] = ()

required = [
    "NextOpenProvenanceSlot.successorBornPrefixClosure",
    "ExactFraction.toRat_eq_of_sameValue",
    "ExactFraction.toRat_represents",
    "ExactFraction.toRat_pos_of_num_pos",
    "InterBirthDirectedResponse.canonicalStateDirectedBlockRealization",
    "InterBirthDirectedResponse.stateDirectedBlockRealization_exists",
    "ResponseCapableState.conductancePairsUnique_append",
    "CanonicalBirthLocalMeasurementCut.PortSupportClosure",
    "CanonicalBirthLocalMeasurementCut.portSupportClosure",
    "ResponseCoupledBirthLawBirthlawB.LiveRelationDeltaClosure",
    "ResponseCoupledBirthLawBirthlawB.liveRelationDeltaClosure",
    "ResponseCoupledBirthLawBirthlawB.liveRelationDelta_positiveNum",
    "RecurrentStateClosureTheorem.realizedLiveDelta_sameValue",
    "RecurrentStateClosureTheorem.successorConductances_pairwise",
    "RecurrentStateClosureTheorem.successor_parentBackbone",
    "RecurrentStateClosureTheorem.successor_live_coherent",
    "RecurrentStateClosureTheorem.RecurrentStateClosure",
    "RecurrentStateClosureTheorem.recurrentStateClosure",
    "RecurrentStateClosureTheorem.RecurrentStateClosureContract",
    "RecurrentStateClosureTheorem.recurrentStateClosureContract",
    "CNNAProofs.T002.canonicalRecurrentStepInput_exists",
    "CNNAProofs.T002.canonicalRecurrentStateClosure_exists",
    "CNNAProofs.T002.CanonicalRecurrentStateClosure",
    "CNNAProofs.T002.canonicalRecurrentStateClosure",
    "CNNAProofs.T002.CanonicalRecurrentStateClosureContract",
    "CNNAProofs.T002.canonicalRecurrentStateClosureContract",
]
resolved = []
for suffix in required:
    matches = [(name, axioms) for name, axioms in profiles.items()
               if name == suffix or name.endswith("." + suffix)]
    if len(matches) != 1:
        raise SystemExit(f"FAIL: unresolved T002 axiom profile {suffix}: {len(matches)} matches")
    resolved.append(matches[0])

allowed = {"propext", "Quot.sound", "Classical.choice"}
for name, axioms in resolved:
    forbidden = set(axioms) - allowed
    if forbidden:
        raise SystemExit(f"FAIL: unexpected axiom profile for {name}: {sorted(forbidden)}")
    if "sorryAx" in axioms:
        raise SystemExit(f"FAIL: sorryAx in axiom profile for {name}")

print("t002_current_proof_axiom_profiles BEGIN")
for name, axioms in resolved:
    marker = "TRUSTED_TRANSITIVE_CHOICE" if "Classical.choice" in axioms else "ACCEPTED"
    print(f"  {marker} {name}: {list(axioms)}")
print("t002_current_proof_axiom_profiles END")
print("T002_CURRENT_PROOF_AXIOM_AUDIT PASS")
PYT002

    rm -f "$PROOF_BUILD_LOG" "$AXIOM_LOG" "$M003_M004_AXIOM_LOG" "$P002_AXIOM_LOG" "$C008_AXIOM_LOG" "$C016_C017_AXIOM_LOG" "$C009_AXIOM_LOG" "$T002_AXIOM_LOG"
    trap - EXIT

    python3 "$HERE/check_package_boundary.py" --require-build
    echo "FULL_PACKAGE_BOUNDARY_AUDIT PASS"
    ;;
  *)
    echo "usage: $0 [--build|--reset-lake-state]" >&2
    exit 2
    ;;
esac
