# 027 · C008 — Record/live response-coupled update

**Canonical node label:** `027 · C008`  
**Semantic ID:** `C008`  
**Current section path:** `1.4.1`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`  
**Formal state:** `KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE`

## Position In Derivation

C008 consumes the immutable canonical birth instruction closed by M004. It is the deterministic application boundary between the already verified response/birth calculation and the later construction of a complete successor state. Its only hard predecessor is M004 (`E027: M004 -> C008`).

C008 introduces two derived physics-carrying relation channels:

- `record`: immutable birth-time relation history;
- `live`: current relation history including later response-coupled backreaction.

Neither channel is an input parameter. C008 does not recompute M003 response data and does not yet construct the C009 successor `ResponseCapableState`.

## Mathematical Contract

For existing channels `(R_n,L_n)` and a canonical M004 instruction `B_n`, write

- `P(B_n)` for `parentChildBirthUpdates`;
- `A(B_n)` for `ancestorBackreactionUpdates`;
- `S(B_n)` for `siblingBackreactionUpdates`.

The C008 update is

\[
R_{n+1}=R_n\mathbin{\|}P(B_n),
\qquad
L_{n+1}=L_n\mathbin{\|}(P(B_n)\mathbin{\|}A(B_n)\mathbin{\|}S(B_n)).
\]

Here `||` denotes list/tuple append. The old channels are exact left prefixes of the new channels. The record equation contains no ancestor or sibling backreaction term.

At the exceptional bootstrap stage, `bootstrapRecordLiveChannels` converts the already-derived C014/C005 bidirected conductances into exact-fraction updates and initializes `record = live`. This is a base-state fact only.

## Introduction Reason

The M004 output is an immutable birth instruction. A separate application layer is needed because the same instruction has two distinct historical effects:

1. its direct parent/newborn pair becomes permanent birth record;
2. its complete relation support becomes current live response data.

Combining these effects into M004 would mix instruction generation with state mutation; snapshotting the live state into record would erase provenance history. C008 isolates exactly this boundary.

## Explicit Construction

Python defines:

```text
RecordLiveChannels(record, live)
bootstrap_record_live_channels(X1)
record_instruction_updates(B) = B.parent_child_birth_updates
live_instruction_updates(B) =
    B.parent_child_birth_updates
  + B.ancestor_backreaction_updates
  + B.sibling_backreaction_updates
apply_response_coupled_update(channels, B)
```

Lean defines the corresponding objects:

```text
RecordLiveChannels
bootstrapRecordLiveChannels
recordInstructionUpdates
liveInstructionUpdates
applyInstruction
```

and packages their exact local semantics in `RecordLiveResponseCoupledUpdateContract`.

The implementation contains no independent rank, rank-distance, depth attenuation, response mode, fitted coefficient, node-load scalar, or birth bias. Those historical Legacy controls are not migrated into the current DAG.

## Invariants

C008 closes the following invariants.

1. **Bootstrap coincidence:** `bootstrapRecordLiveChannels X` has equal record and live lists.
2. **Record prefix preservation:** the previous record is preserved exactly and only `parentChildBirthUpdates` are appended.
3. **Live prefix preservation:** the previous live list is preserved exactly and the full M004 relation-support delta is appended.
4. **Backreaction separation:** strict-ancestor and sibling backreaction never enter the C008 record delta.
5. **No new free update parameter:** the update consumes only existing channels and the M004 instruction.
6. **Semantic representative independence:** exact-fraction representation choices do not alter the output modulo the established SameValue relation.

## Canonicity Or Uniqueness

M004 proves existence of a canonical handoff instruction and SameValue equivalence of any two canonical representatives. C008 lifts this through append.

The core theorem

```text
applyInstruction_respects_sameValue
```

proves that SameValue-equivalent old channels updated by SameValue-equivalent instructions yield SameValue-equivalent output channels.

The proof facade then combines this with

```text
canonicalBirthInstructionHandoff_exists
canonicalBirthInstructionHandoff_sameValue
```

to prove `CanonicalRecordLiveUpdateClosure`. Literal equality of raw exact-fraction representations is intentionally not claimed.

## Boundary Cases

- **Bootstrap:** record and live coincide only because both represent the same first bidirected C014 relation pair.
- **No ancestor backreaction:** the live delta reduces accordingly; record semantics are unchanged.
- **No sibling backreaction:** likewise.
- **Empty previous channels:** the output is exactly the M004-derived deltas.
- **Nonempty previous channels:** all old entries remain exact prefixes; no historical entry is rewritten.
- **Different exact-fraction representatives:** output equality is SameValue, not structural fraction equality.

C008 does not define behavior beyond the M004 instruction domain and does not prove the full successor-state schema.

## Python Lean Cross Layer

The Python and Lean layers implement the same structural equations but serve different evidential roles.

Python source:

`derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s04_record_live_update_backreaction_channels_and_finite_closure/s01_c008__record_live_response_coupled_update.py`

Lean Core:

`derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S01_C008_RecordLiveResponseCoupledUpdate.lean`

Lean proof facade:

`derivation/code/lean/proofs/src/CNNAProofs/C008/S01_CanonicalRecordLiveUpdateClosure.lean`

Python uses immutable tuples and normalized `Fraction` values. Lean uses lists of M004 `DirectedRelationUpdate` values and C006 exact-fraction SameValue semantics. The cross-layer claim is semantic agreement of the update partition, not byte-level data-structure identity.

## Countercheck

The current Python regression suite was rerun on the finalized source snapshot:

```text
106 passed, 1086 subtests passed
```

Evidence file:

`derivation/registry/documentation/C008_PYTHON_REGRESSION_20260808.txt`

The C008-specific suite includes:

- bootstrap record/live equality;
- direct-birth-only record update;
- strict-ancestor backreaction live-only check;
- exact preservation of previous channel prefixes;
- rejection of reintroduced Legacy free controls by signature inspection;
- a 99-case finite `(b,L,n)` sweep checking the M004 channel partition.

The 99-case sweep is **finite evidence**, not a universal proof. The universal structural result is the Lean theorem/contract.

The historical Legacy code was used only to identify qualitative hypotheses worth retesting. Its free coefficients, node-load mutation, rank-distance factors, alternative schedules, and mode-dependent update laws are not copied into C008.

## Result

The user-local Lean 4.31.0 build on 2026-08-08 reached and passed the C008 proof audit. The final package-boundary result reports:

```text
"c008": "KERNEL_VERIFIED_CURRENT_BUILD"
"c008_record_live_update_olean": true
"retained_verified_p001_source_hash_match": true
"retained_verified_m003_m004_source_hash_match": true
"retained_verified_p002_source_hash_match": true
FULL_PACKAGE_BOUNDARY_AUDIT PASS
```

All four C008 source files are now bound to this transcript as exact-source kernel evidence.

### Axiom profile

Seven C008 declarations are enumerated by `#print axioms`:

- `applyInstruction_respects_sameValue`: `[propext, Quot.sound]`;
- `RecordLiveResponseCoupledUpdateContract`: `[propext, Classical.choice, Quot.sound]`;
- `recordLiveResponseCoupledUpdateContract`: `[propext, Classical.choice, Quot.sound]`;
- `CanonicalRecordLiveUpdateClosure`: `[propext, Quot.sound]`;
- `canonicalRecordLiveUpdateClosure`: `[propext, Classical.choice, Quot.sound]`;
- `CanonicalRecordLiveUpdateContract`: `[propext, Quot.sound]`;
- `canonicalRecordLiveUpdateContract`: `[propext, Classical.choice, Quot.sound]`.

Thus the profile counts are `4 choice+propext+quot`, `3 propext+quot`, `0 axiom-free`. There are no project-local axioms and no `sorryAx`. The explicit C008 source itself contains no `Classical`; the choice dependency is inherited transitively through the verified M004 proof layer.

Build evidence:

`derivation/code/lean/audit/evidence/USER_LOCAL_C008_FULL_BUILD_20260808.json`

Transcript SHA-256:

`f709a754198efd33915c9953e6efba6b09e17b3defabe3260c2f3c78fb63e3fa`

## Downstream Handoff

C008 now closes `E027: M004 -> C008`. Its two explicit downstream construction edges remain separate:

```text
C008 -> C016  creates_record_channel
C008 -> C017  updates_live_channel
```

The next active node is C016. C017 remains unfinished until its own construction boundary is explicitly closed. C009 depends on both C016 and C017 and is therefore not yet eligible to become active.

## Code Anchors

### Python source

- `RecordLiveChannels`, lines 29–42.
- `bootstrap_record_live_channels`, lines 52–63.
- `record_instruction_updates`, lines 66–72.
- `live_instruction_updates`, lines 75–85.
- `apply_response_coupled_update`, lines 88–100.

### Python regression

- `test_record_gets_only_new_birth_pair_while_live_gets_backreaction`, lines 73–83.
- `test_strict_ancestor_backreaction_is_live_only`, lines 86–98.
- `test_c008_has_no_legacy_free_update_controls`, lines 115–123.
- `test_small_finite_sweep_matches_m004_channel_partition_exactly`, lines 126–141.

### Lean Core

- `RecordLiveChannels`, lines 39–41.
- `recordInstructionUpdates`, lines 66–70.
- `liveInstructionUpdates`, lines 74–80.
- `applyInstruction`, lines 83–89.
- `applyInstruction_record_eq`, lines 99–105.
- `applyInstruction_live_eq`, lines 109–118.
- `applyInstruction_respects_sameValue`, lines 184–198.
- `RecordLiveResponseCoupledUpdateContract`, lines 203–224.
- `recordLiveResponseCoupledUpdateContract`, lines 227–238.

### Lean proof facade

- `CanonicalRecordLiveUpdateClosure`, lines 25–41.
- `canonicalRecordLiveUpdateClosure`, lines 45–62.
- `CanonicalRecordLiveUpdateContract`, lines 67–72.
- `canonicalRecordLiveUpdateContract`, lines 75–78.

## Infobox — SameValue Is the Correct Equality Boundary

M004 can admit distinct exact-fraction representations of the same rational values. Requiring literal structural equality in C008 would strengthen the upstream contract without justification. C008 therefore preserves exactly the equivalence M004 proves: endpoint equality plus exact-fraction SameValue entry by entry. This keeps the update canonical without smuggling in a representation-normalization postulate.
