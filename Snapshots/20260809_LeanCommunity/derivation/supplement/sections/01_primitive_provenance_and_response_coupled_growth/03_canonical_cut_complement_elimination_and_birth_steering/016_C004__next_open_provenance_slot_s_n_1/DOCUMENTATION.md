# 016 · C004 — Next open provenance slot s_{n+1}

**Canonical node label:** `016 · C004`  
**Current section path:** `1.3.2`  
**Documentation tier:** `D1`

## Position In Derivation
C004 consumes a recurrent C005 state and the already fixed C018 order. It is the unique structural selector used by M001 and later birth nodes.

## Mathematical Contract
For an unsaturated state `X`, an admissible open address is a non-root C003 address within cutoff that is not born. `IsNextOpenAddress X a` means that `a` is admissible and no admissible open address precedes it under C018 `BirthBefore`. `NextOpenSlot X` packages this child with its uniquely reconstructed parent and final rank.

## Introduction Reason
The recurrent layer needs the next structural provenance location before it can define a local cut or measure a response. This selector must use no response value, geometry, or birth law.

## Explicit Construction
Python returns `state.schedule.slots[state.birth_count]` after checking unsaturation and verifies it through `is_next_open_provenance_slot`. Lean finitely enumerates the C003 carrier, filters open candidates, and chooses the least candidate constructively under C018.

## Invariants
The child is non-root, cutoff-admissible, not born, and least among all open addresses. Every admissible predecessor is born. The reconstructed parent is born and the child equals `parent.snoc(rank)`.

## Canonicity Or Uniqueness
`exists_of_unsaturated` proves existence; `child_unique` and `unique` prove uniqueness. `parent_rank_unique` proves that the child determines exactly one parent/rank pair.

## Boundary Cases
For a saturated finite approximant, `no_next_of_saturated` proves that no successor exists. No sentinel or out-of-cutoff child is introduced. At `L=0`, every recurrent state premise is already unavailable because C014 cannot be formed.

## Python Lean Cross Layer
Python is positional because C005 proves the born list is the exact schedule prefix. Lean is extensional and proves least-open uniqueness. Their semantic lock is the independent Python predicate matching the Lean relation.

## Countercheck
An arbitrary un-born child would not be canonical. A second schedule would duplicate C018. A sentinel would falsely add a provenance address beyond the finite carrier. Omitting parent-bornness would invalidate the M001 causal prefix cut.

## Result
C004 provides exactly one next open provenance slot for every unsaturated C005 state and none for a saturated state.

## Downstream Handoff
- `E017` to M001 localizes the cut;
- `E026` to M004 is `ACTIVE_VERIFIED` and supplies the unique next provenance slot used by the birth instruction;
- C004 also supplies the verified dynamic least-open content that P002 had attempted to own too early.

## Code Anchors
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s02_c004__next_open_provenance_slot_snplus1_n_ge_1.py}
Source SHA-256: `d939caa5a08845e0ee8faa737e79efebdec29031de08d5d52b51f77c3aab0535`

- `is_next_open_provenance_slot` - FUNCTION, lines 24-51; role `SOURCE`.
- `next_open_provenance_slot` - FUNCTION, lines 54-91; role `SOURCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s02_c004__next_open_provenance_slot_snplus1_n_ge_1.py}
Source SHA-256: `e03128bfa022ebd4939c778fee4cc19eda4711544922d965ae227457392b725f`

- `_state` - FUNCTION, lines 16-31; role `TEST`.
- `TestNextOpenProvenanceSlot` - CLASS, lines 34-107; role `TEST`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S02_C004_NextOpenProvenanceSlotSnplus1NGe1.lean}
Source SHA-256: `e729d8ac3ebcf263049f660b8ea33bd9087d60fd1796d076a7c55659e922281a`

- `addressesAtDepth` - DEF, lines 39-47; role `SOURCE`.
- `mem_addressesAtDepth_of_length_eq` - THEOREM, lines 48-63; role `SOURCE`.
- `addressesUpTo` - DEF, lines 64-69; role `SOURCE`.
- `mem_addressesUpTo_of_length_le` - THEOREM, lines 70-88; role `SOURCE`.
- `AdmissibleOpenAddress` - DEF, lines 89-95; role `SOURCE`.
- `Unsaturated` - DEF, lines 96-99; role `SOURCE`.
- `Saturated` - DEF, lines 100-107; role `SOURCE`.
- `IsNextOpenAddress` - DEF, lines 108-116; role `SOURCE`.
- `NextOpenSlot` - ABBREV, lines 117-123; role `SOURCE`.
- `admissibleOpenAddressDecidable` - INSTANCE, lines 124-133; role `SOURCE`.
- `birthBeforeDecidable` - INSTANCE, lines 134-145; role `SOURCE`.
- `preferEarlierOpen` - DEF, lines 146-157; role `SOURCE`.
- `MinimalAmong` - DEF, lines 158-165; role `SOURCE`.
- `minimalAmong_cons` - THEOREM, lines 166-208; role `SOURCE`.
- `leastOpenFrom` - DEF, lines 209-218; role `SOURCE`.
- `leastOpenFrom_minimal` - THEOREM, lines 219-235; role `SOURCE`.
- `exists_of_unsaturated` - THEOREM, lines 236-251; role `SOURCE`.
- `child_nonroot` - THEOREM, lines 252-256; role `SOURCE`.
- `child_withinCutoff` - THEOREM, lines 257-261; role `SOURCE`.
- `child_notBorn` - THEOREM, lines 262-266; role `SOURCE`.
- `no_open_before` - THEOREM, lines 267-273; role `SOURCE`.
- `child_unique` - THEOREM, lines 274-285; role `SOURCE`.
- `unique` - THEOREM, lines 286-292; role `SOURCE`.
- `born_before_next` - THEOREM, lines 293-311; role `SOURCE`.
- `earlier_admissible_is_born` - THEOREM, lines 312-327; role `SOURCE`.
- `admissible_born_iff_before_next` - THEOREM, lines 328-340; role `SOURCE`.
- `snoc_eq_append_singleton` - THEOREM, lines 341-351; role `SOURCE`.
- `child_ne_nil` - THEOREM, lines 352-359; role `SOURCE`.
- `parentAddress` - DEF, lines 360-364; role `SOURCE`.
- `rank` - DEF, lines 365-369; role `SOURCE`.
- `child_eq_snoc` - THEOREM, lines 370-375; role `SOURCE`.
- `child_parent` - THEOREM, lines 376-381; role `SOURCE`.
- `child_finalSlot` - THEOREM, lines 382-387; role `SOURCE`.
- `eq_root_of_depth_eq_zero` - THEOREM, lines 388-400; role `SOURCE`.
- `parent_born` - THEOREM, lines 401-429; role `SOURCE`.
- `parent_rank_unique` - THEOREM, lines 430-442; role `SOURCE`.
- `unsaturated_not_saturated` - THEOREM, lines 443-450; role `SOURCE`.
- `no_next_of_saturated` - THEOREM, lines 451-459; role `SOURCE`.

<!-- CNNA-OPEN-PROVENANCE-BEGIN C004 -->
## Open-provenance role: Open slot as state-relative incompleteness

C004 makes openness relative to a current born prefix: the next slot is absent from the present state but admissible in the fixed provenance grammar.  This is the finite CNNA specialization of openness relative to an incomplete state description.

<!-- CNNA-OPEN-PROVENANCE-END C004 -->
