# 026 · M004 — Response-coupled birth law B_b

**Canonical node label:** `026 · M004`  
**Semantic ID:** `M004`  
**Current section path:** `1.3.10`  
**Documentation tier:** `D1`

## Position In Derivation
M004 follows C004, O001, M003, and P001. It constructs one immutable birth instruction and exposes the exact output boundary consumed by C008.

## Mathematical Contract
The zero-inclusive pure lift transports one exact nonnegative scalar over the provenance-determined support. The active law requires strict positivity. `CanonicalM004Closure realization` consumes `CanonicalM003Closure realization` and proves active instruction existence, uniqueness for each exact pair, and representative independence.

## Introduction Reason
The response must determine the birth data through an explicit, bias-free map while state mutation remains a separate C008 responsibility.

## Explicit Construction
```text
parent -> child          sigma
child -> parent          sigma
child -> strict ancestor sigma
older sibling -> child   sigma
child -> older sibling   sigma
birth lapse              sigma
```
`canonicalM004Closure` obtains a response-steering pair from M003, derives its positivity from M003, invokes the Core `birthLaw`, and packages the result. `IsCanonicalBirthInstructionHandoff` hides response representatives and proof witnesses while retaining the Core instruction.

## Invariants
- All endpoints are provenance addresses; no self-loop is emitted.
- The direct parent is excluded from the strict-ancestor updates.
- Sibling updates occur in paired orientations and canonical order.
- Every relation value and the lapse use the same exact steering value.
- No state mutation occurs in M004.

## Canonicity Or Uniqueness
For each exact response-steering pair, the active instruction exists uniquely. Any two canonical handoffs have `BirthInstructionSameValue`, so representative changes cannot alter provenance support or exact scalar values.

## Boundary Cases
The zero lift is exact and annihilates all values but is not an active C005 birth. Negative values are outside both domains. A root-parent birth has no strict-ancestor update.

## Python Lean Cross Layer
Python and Core Lean implement the same support and exact scalar transport. The proof module `S02_CanonicalM004ClosureAndHandoff.lean` imports only the closed M003 interface and uses it directly; it does not select a parent coordinate again.

## Countercheck
- Zero remains boundary data and fails active admission.
- Negative or noncanonical inputs are rejected.
- No rank, depth, load, mode, scale, baseline, clipping, fallback, or second newborn scalar occurs.
- C008 is not implemented here; the handoff proves M004 output closure without claiming state mutation.

## Axiom Profile
All seven M004 closure and handoff declarations are kernel-compiled and axiom-audited. Three declaration-level interfaces use `propext` and `Quot.sound`; four constructive theorems additionally use transitive `Classical.choice`. No project-local axiom or `sorry` is admitted.

## Result
M004 has a kernel-verified active-law interface and an immutable C008 handoff without external positivity or parent-index arguments.

## Downstream Handoff
`canonicalBirthInstructionHandoff_exists` supplies an instruction; `canonicalBirthInstructionHandoff_sameValue` proves representative-independent output equivalence. C008 alone applies it to record/live state.

## Code Anchors
### python / SOURCE: `s10_m004__response_coupled_birth_law_birthlaw_b.py`
Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s10_m004__response_coupled_birth_law_birthlaw_b.py`  
SHA-256: `fb5ae77e13b3596f806136edb4e4854631e3ee3911e7a6baf788409d9b67691c`

| Symbol | Kind | Lines |
|---|---|---:|
| `BirthLawDomainError` | `CLASS` | 57-58 |
| `DirectedRelationUpdate` | `CLASS` | 62-77 |
| `ResponseCoupledBirthInstruction` | `CLASS` | 81-136 |
| `direct_response_lift` | `FUNCTION` | 139-180 |
| `canonical_bias_free_birth_law_inputs` | `FUNCTION` | 183-221 |
| `response_coupled_birth_law` | `FUNCTION` | 224-243 |

### python_test / TEST: `test_s10_m004__response_coupled_birth_law_birthlaw_b.py`
Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s10_m004__response_coupled_birth_law_birthlaw_b.py`  
SHA-256: `364ae68fbcc74863b4756b271d38bf3c1444a02f2aa23db3eec4de54557f3dcf`

| Symbol | Kind | Lines |
|---|---|---:|
| `_bootstrap_state` | `FUNCTION` | 35-41 |
| `_state` | `FUNCTION` | 44-55 |
| `_instruction` | `FUNCTION` | 58-62 |
| `TestResponseCoupledBirthLaw` | `CLASS` | 65-201 |

### lean_core / SOURCE: `S10_M004_ResponseCoupledBirthLawBirthlawB.lean`
Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S10_M004_ResponseCoupledBirthLawBirthlawB.lean`  
SHA-256: `03d417a92f6591d4325ee62bda1d3d1f227456b58bfa91478b206251b721c382`

| Symbol | Kind | Lines |
|---|---|---:|
| `NonnegativeLiftValue` | `DEF` | 48-51 |
| `DirectedRelationUpdate` | `STRUCTURE` | 52-57 |
| `ResponseCoupledBirthInstruction` | `STRUCTURE` | 58-67 |
| `strictAncestorPorts` | `DEF` | 68-72 |
| `directRelationUpdate` | `DEF` | 73-80 |
| `parentChildUpdates` | `DEF` | 81-87 |
| `ancestorBackreactionUpdates` | `DEF` | 88-94 |
| `siblingBackreactionAux` | `DEF` | 95-105 |
| `siblingBackreactionUpdates` | `DEF` | 106-111 |
| `directResponseLift` | `DEF` | 112-122 |
| `candidateInputs` | `DEF` | 123-135 |
| `candidateInputs_admissible` | `THEOREM` | 136-143 |
| `biasFreeInputs` | `DEF` | 144-156 |
| `birthLaw` | `DEF` | 157-166 |
| `IsCanonicalBirthLaw` | `DEF` | 167-176 |
| `DirectedRelationUpdateSameValue` | `STRUCTURE` | 177-185 |
| `DirectedRelationUpdatesSameValue` | `INDUCTIVE` | 186-197 |
| `BirthInstructionSameValue` | `STRUCTURE` | 198-210 |
| `directRelationUpdate_respects_sameValue` | `THEOREM` | 211-221 |
| `ancestorAux_respects_sameValue` | `THEOREM` | 222-236 |
| `siblingAux_respects_sameValue` | `THEOREM` | 237-253 |
| `directResponseLift_respects_sameValue` | `THEOREM` | 254-277 |
| `birthLaw_respects_sameValue` | `THEOREM` | 278-295 |
| `birthLaw_exists` | `THEOREM` | 296-307 |
| `birthLaw_unique` | `THEOREM` | 308-321 |
| `responseSteeringPairs_give_same_birthLaw` | `THEOREM` | 322-342 |
| `birthLaw_parentChild_eq_directLift` | `THEOREM` | 343-354 |
| `birthLaw_lapse_eq_steering` | `THEOREM` | 355-366 |
| `directResponseLift_zero_lapse` | `THEOREM` | 367-371 |

### lean_proof / PROOF: `S02_CanonicalM004ClosureAndHandoff.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/M003M004/S02_CanonicalM004ClosureAndHandoff.lean`  
SHA-256: `2882f029f40a3b5742e987e3b201602ba5a5dd532121818418837747e825e93e`

| Symbol | Kind | Lines |
|---|---|---:|
| `CanonicalM004Closure` | `STRUCTURE` | 31-67 |
| `canonicalM004Closure` | `THEOREM` | 68-108 |
| `IsCanonicalBirthInstructionHandoff` | `DEF` | 109-119 |
| `canonicalBirthInstructionHandoff_exists` | `THEOREM` | 120-131 |
| `canonicalBirthInstructionHandoff_sameValue` | `THEOREM` | 132-146 |
| `CanonicalM004ClosureContract` | `DEF` | 147-159 |
| `canonicalM004ClosureContract` | `THEOREM` | 160-167 |


## Reference Context Retained

<!-- CNNA-EXTREF-BEGIN EXT-USE-M004-LEAN-INDUCTIVE -->
**EXT-REF-LEAN-001 — formalization guidance.** The Lean 4 Development Team, *The Lean Language Reference: Inductive Types*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_OFFICIAL_DOCUMENTATION`. Stable source: `https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/`; accessed 2026-07-31. Exact location: Section 4.4, constructors and generated recursors. Context: Documents the official source consulted when replacing unavailable List.Forall₂ with a module-local inductive relation. Formal status: `GUIDANCE_ONLY_NO_MATHLIB_DEPENDENCY`
<!-- CNNA-EXTREF-END EXT-USE-M004-LEAN-INDUCTIVE -->

<!-- CNNA-OPEN-PROVENANCE-BEGIN M004 -->
## Open-provenance role: Birth instruction before record/live mutation

M004 turns the positive response scalar into a representative-independent provenance instruction.  C008 remains responsible for applying that instruction to the immutable record and mutable live channels.

<!-- CNNA-OPEN-PROVENANCE-END M004 -->
