# 028 · C016 — Immutable record channel

**Canonical node label:** `028 · C016`  
**Semantic ID:** `C016`  
**Current section path:** `1.4.2`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`  
**Formal state:** `KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE`

## Position In Derivation
C016 consumes the kernel-verified C008 record/live update and isolates its birth-time record projection. C009 consumes C016 together with C017 and the C005 state schema.

## Mathematical Contract
For arbitrary existing C008 channels and one admissible canonical M004 instruction `B`, C016 closes `record' = record ++ B.parentChildBirthUpdates`. The previous record is therefore a literal left prefix. Ancestor and sibling backreaction do not occur in the record delta. Exact-fraction representation changes are compared only through the established C006 `SameValue` relation.

## Introduction Reason
C008 already carries both channels, but downstream nodes need the historical record as a separately named construction boundary. Keeping C016 separate prevents later live information from being retrospectively written into provenance history.

## Explicit Construction
Python exposes `immutable_record_channel` and `record_channel_after_instruction`. Lean exposes `recordChannel`, `afterInstruction`, `afterInstruction_eq_append`, `previousRecord_isLeftPrefix`, and `afterInstruction_respects_sameValue`, packaged by `ImmutableRecordChannelContract`.

## Invariants
1. Bootstrap record equals the already-derived bootstrap relation pair.
2. Every one-step update preserves the complete previous record literally as a left prefix.
3. The only appended record block is the direct parent/newborn M004 birth pair.
4. Strict-ancestor and sibling backreaction never enter the C016 record suffix.
5. The projection respects C006/M004 `SameValue`.

## Canonicity Or Uniqueness
No independent C016 choice is made. The projection is definitionally determined by C008, and its representative independence is inherited from `applyInstruction_respects_sameValue`.

## Boundary Cases
The bootstrap coincidence of record and live is not promoted to a later identity. Empty and nonempty old records are both covered. C016 does **not** prove arbitrary-many-future-step invariance because the typed recurrent successor chain has not yet been constructed.

## Python Lean Cross Layer
Python uses immutable tuples; Lean uses lists. The semantic claim is the same append-only partition, not byte-level data-structure identity.

## Countercheck
The finalized Python suite reports `114 tests, 1086 subtests PASS`. C016-specific tests check exact projection, direct-birth-only append, nonmutation of the old tuple, and type rejection. This is finite regression evidence only.

## Result
The user-local Lean 4.31.0 build on 2026-08-08 reports `C016_C017_CURRENT_PROOF_AXIOM_AUDIT PASS`, both nodes as `KERNEL_VERIFIED_CURRENT_BUILD`, `c016_c017_projection_closure_olean: true`, all retained predecessor hash gates true, and `FULL_PACKAGE_BOUNDARY_AUDIT PASS`. The retained transcript SHA-256 is `2a4b7655de227e1e2ebdc5e5f4ea57e550a5ce1032b7df7aba0aaff7c677ee2a`.

Axiom-profile contribution: `afterInstruction_respects_sameValue` has `[propext, Quot.sound]`; C016 contract/facade declarations inherit `[propext, Classical.choice, Quot.sound]`. No project-local axiom and no `sorryAx` occurs.

## Downstream Handoff
C016 supplies the immutable record projection to C009 and later record/live comparison nodes. Global future invariance remains downstream of the recurrent chain.

## Code Anchors
- Python: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s04_record_live_update_backreaction_channels_and_finite_closure/s02_c016__immutable_record_channel.py`, lines 20–38.
- Python tests: `test_s02_c016__immutable_record_channel.py`, lines 35–66.
- Lean Core: `S02_C016_ImmutableRecordChannel.lean`, lines 29–115.
- Lean proof facade: `S01_CanonicalRecordLiveChannelProjectionClosure.lean`, lines 19–26 and 37–46.