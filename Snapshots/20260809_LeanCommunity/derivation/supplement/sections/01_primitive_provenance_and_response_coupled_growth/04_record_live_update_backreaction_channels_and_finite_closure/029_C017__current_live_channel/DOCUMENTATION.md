# 029 · C017 — Current live channel

**Canonical node label:** `029 · C017`  
**Semantic ID:** `C017`  
**Current section path:** `1.4.3`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`  
**Formal state:** `KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE`

## Position In Derivation
C017 consumes C008 and isolates its current-live relation projection. Together with C016 it provides the two channel components required by C009.

## Mathematical Contract
For arbitrary existing C008 channels and one canonical M004 instruction `B`, C017 closes `live' = live ++ (B.parentChildBirthUpdates ++ B.ancestorBackreactionUpdates ++ B.siblingBackreactionUpdates)`. The old live channel is a literal left prefix and the full M004 relation delta is appended. The projection respects C006/M004 `SameValue`.

## Introduction Reason
The mutable current channel must be kept distinct from immutable birth record before later effective-response and backreaction observables are formed.

## Explicit Construction
Python exposes `current_live_channel` and `live_channel_after_instruction`. Lean exposes `liveChannel`, `afterInstruction`, `afterInstruction_eq_append`, `previousLive_isLeftPrefix`, and `afterInstruction_respects_sameValue`, packaged by `CurrentLiveChannelContract`.

## Invariants
1. Bootstrap live equals the same already-derived bootstrap relation pair as record.
2. Every C008 step preserves the previous live channel as a literal left prefix.
3. The appended suffix is exactly the complete M004 direct-birth + ancestor + sibling delta.
4. No new response coefficient or Legacy mode is introduced.
5. The projection respects C006/M004 `SameValue`.

## Canonicity Or Uniqueness
C017 is a deterministic projection of C008. Any semantic representative freedom is exactly the upstream `SameValue` freedom already proved in C008/M004.

## Boundary Cases
Ancestor or sibling lists may be empty; the append equation specializes directly. C017 is not a Schur/DtN response and is not the later `live-record` current C024.

## Python Lean Cross Layer
Python tuple append and Lean list append implement the same ordered M004 delta partition. The Lean theorem is universal; the Python tests are finite regression evidence.

## Countercheck
The finalized Python suite reports `114 tests, 1086 subtests PASS`. C017-specific checks verify exact live projection, complete-delta append, inclusion of sibling backreaction when emitted, and type rejection.

## Result
The user-local Lean 4.31.0 build on 2026-08-08 reports `C016_C017_CURRENT_PROOF_AXIOM_AUDIT PASS`, both nodes as `KERNEL_VERIFIED_CURRENT_BUILD`, `c016_c017_projection_closure_olean: true`, all retained predecessor hash gates true, and `FULL_PACKAGE_BOUNDARY_AUDIT PASS`. The retained transcript SHA-256 is `2a4b7655de227e1e2ebdc5e5f4ea57e550a5ce1032b7df7aba0aaff7c677ee2a`.

Axiom-profile contribution: `afterInstruction_respects_sameValue` has `[propext, Quot.sound]`; C017 contract/facade declarations inherit `[propext, Classical.choice, Quot.sound]`. No project-local axiom and no `sorryAx` occurs.

## Downstream Handoff
C017 supplies the current-live projection to C009. The difference between live and record effective responses remains owned by C024.

## Code Anchors
- Python: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s04_record_live_update_backreaction_channels_and_finite_closure/s03_c017__current_live_channel.py`, lines 18–36.
- Python tests: `test_s03_c017__current_live_channel.py`, lines 35–67.
- Lean Core: `S03_C017_CurrentLiveChannel.lean`, lines 27–116.
- Lean proof facade: `S01_CanonicalRecordLiveChannelProjectionClosure.lean`, lines 28–46.