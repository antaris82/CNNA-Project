# 021 · C007 — Inter-birth directed response R_n(s_{n+1})

**Canonical node label:** `021 · C007`  
**Current section path:** `1.3.6`  
**Documentation tier:** `D1`

## Position In Derivation
C007 is the first state-dependent response node. It combines C005, C004/M001, M002, and C006 after all structural and domain ownership has been fixed.

## Mathematical Contract
Order the entire born carrier as M001 boundary followed by interior. From every stored directed conductance define the source/out-degree matrix `K[u,u]=sum_v c(u,v)` and `K[u,v]=-c(u,v)` for `u != v`. On M002 domain membership, `R_n(s_{n+1})` is the unique C006 Schur/DtN response.

## Introduction Reason
The later steering law needs a measured property of the existing network before the next birth. This response must use the current directed weights without symmetrization or a response-independent bias.

## Explicit Construction
Python assembles an exact `Fraction` matrix, slices the four blocks in M001 order, validates M002, and evaluates C006. Lean constructs exact-fraction outgoing/ordered-pair sums, defines raw blocks, and requires a `StateDirectedBlockRealization` proving that canonical rational inputs represent those exact values.

## Invariants
Rows are sources and columns targets. Off-diagonal entries are negative ordered-pair conductances; the diagonal is total outgoing conductance. All current born vertices occur exactly once. The unborn child occurs nowhere. No external port, grounded load, geometry, averaging, transpose, or regularization is added.

## Canonicity Or Uniqueness
M001 fixes coordinates, the directed conductance list fixes exact entries, M002 fixes the domain, and C006 proves response existence and value-level uniqueness. `response_of_sameValue` makes output-representative independence explicit.

## Boundary Cases
Zero interior reduces to the boundary block. Singular nonempty interior is outside the domain. Saturated states have no C004 slot and therefore no C007 pre-birth response indexed by `s_{n+1}`.

## Python Lean Cross Layer
Python normalizes fractions; Lean separates exact values from canonical `Rat` input representatives through `MatrixRepresents`. The P001 semantic bridge later identifies these with ordinary rational matrix arithmetic. Both layers preserve the same M001 coordinate order and source/out-degree sign convention.

## Countercheck
Symmetrizing would erase directional data. Reversing row/column ownership would transpose the model. Adding the unborn child would make the measurement anticipatory. A tolerance-based inverse would alter M002. Omitting additional born-born edges would fail to represent the live C005 state.

## Result
C007 is a verified exact directed pre-birth response on the stated M002 domain.

## Downstream Handoff
- `E024` to M003 is `ACTIVE_VERIFIED` and supplies the exact response consumed by the canonical steering functional;
- `E035`, `E037`, and `E038` feed null/robustness controls;
- `E137` supplies the directed block operator to P001.

## Code Anchors
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s06_c007__inter_birth_directed_response_rn_snplus1.py}
Source SHA-256: `9975a54c59b3385a416b6bb2f3df08135dd1f8caa0433ba809c65b1ba8462e0c`

- `_zero_matrix` - FUNCTION, lines 52-53; role `SOURCE`.
- `_freeze_block` - FUNCTION, lines 56-66; role `SOURCE`.
- `StateDirectedSchurRealization` - CLASS, lines 70-96; role `SOURCE`.
- `InterBirthDirectedResponse` - CLASS, lines 100-122; role `SOURCE`.
- `state_directed_schur_realization` - FUNCTION, lines 125-166; role `SOURCE`.
- `inter_birth_directed_response` - FUNCTION, lines 169-190; role `SOURCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s06_c007__inter_birth_directed_response_rn_snplus1.py}
Source SHA-256: `ddf93cee71f4da4c82ea4b17776e55ba63fb83b35c3ce9c8b3be68c5434f5426`

- `_bootstrap_state` - FUNCTION, lines 31-37; role `TEST`.
- `_state` - FUNCTION, lines 40-55; role `TEST`.
- `TestInterBirthDirectedResponse` - CLASS, lines 58-134; role `TEST`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S06_C007_InterBirthDirectedResponseRnSnplus1.lean}
Source SHA-256: `18ef5818a50460d6866847274cd196f581f7b7d15c8da940287e43b95a49eaaf`

- `outgoingSum` - DEF, lines 40-52; role `SOURCE`.
- `orderedPairSum` - DEF, lines 53-65; role `SOURCE`.
- `directedMatrixEntry` - DEF, lines 66-74; role `SOURCE`.
- `directedMatrixEntry_self` - THEOREM, lines 75-82; role `SOURCE`.
- `directedMatrixEntry_of_ne` - THEOREM, lines 83-93; role `SOURCE`.
- `boundaryAddress` - DEF, lines 94-98; role `SOURCE`.
- `interiorAddress` - DEF, lines 99-103; role `SOURCE`.
- `rawKBB` - DEF, lines 104-110; role `SOURCE`.
- `rawKBI` - DEF, lines 111-117; role `SOURCE`.
- `rawKIB` - DEF, lines 118-124; role `SOURCE`.
- `rawKII` - DEF, lines 125-132; role `SOURCE`.
- `RealizesStateDirectedBlocks` - DEF, lines 133-142; role `SOURCE`.
- `StateDirectedBlockRealization` - STRUCTURE, lines 143-148; role `SOURCE`.
- `IsInterBirthDirectedResponse` - DEF, lines 149-155; role `SOURCE`.
- `InResponseDomain` - DEF, lines 156-162; role `SOURCE`.
- `inResponseDomain_iff_m002` - THEOREM, lines 163-170; role `SOURCE`.
- `response_exists` - THEOREM, lines 171-182; role `SOURCE`.
- `response_unique` - THEOREM, lines 183-196; role `SOURCE`.
- `response_of_sameValue` - THEOREM, lines 197-208; role `SOURCE`.
- `unborn_child_not_in_boundary` - THEOREM, lines 209-213; role `SOURCE`.
- `unborn_child_not_in_interior` - THEOREM, lines 214-220; role `SOURCE`.

<!-- CNNA-OPEN-PROVENANCE-BEGIN C007 -->
## Open-provenance role: Effective response after complement elimination

C007 is the retained-port response of the pre-birth live state.  It is the finite directed-linear effective dynamics associated with the M001 cut, before scalar steering or event creation.

<!-- CNNA-OPEN-PROVENANCE-END C007 -->
