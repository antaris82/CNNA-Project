# 015 · C005 — Response-capable state schema X_n, n >= 1

**Canonical node label:** `015 · C005`  
**Current section path:** `1.3.1`  
**Documentation tier:** `D1`

## Position In Derivation
C005 begins the recurrent layer after C014. It is the domain of every later pre-birth measurement and update step.

## Mathematical Contract
A state `X_n` consists of a C003 grammar, its C018 schedule, a nonempty list `bornNonRoot`, and a finite list of positive directed conductances. The mathematical birth count is `n = bornNonRoot.length`, hence `n >= 1`. The born non-root list is exactly the first `n` schedule children. The carrier is the root together with this prefix.

## Introduction Reason
C014 supplies only the exceptional base state. Recurrent growth needs a stable state type independent of the next-slot, cut, response, steering, and update constructions.

## Explicit Construction
`DirectedConductance` stores a source address, a distinct target address, and a strictly positive exact rational value. `ResponseCapableState` stores the grammar, schedule, born prefix, and conductance list. `fromBootstrap` transports the C014 root/newborn pair and its two directed unit values into the recurrent representation.

## Invariants
- grammar and schedule share the same branching parameter and cutoff;
- `bornNonRoot` is nonempty, duplicate-free, cutoff-admissible, and equal to the initial C018 prefix;
- every conductance has born endpoints, positive value, and distinct endpoints;
- ordered conductance pairs are unique;
- every born non-root address has both positive parent orientations;
- additional directed edges between already-born vertices are permitted.

## Canonicity Or Uniqueness
C005 does not claim a unique state for fixed `n`; live conductance values may differ. It claims a unique schema and a canonical embedding of C014. The theorem `fromBootstrap_n` fixes the base image at `n=1`.

## Boundary Cases
The schema excludes `n=0`; that regime is owned by C001/C002 before the first non-root birth. Self-loops, nonpositive values, unborn endpoints, duplicate ordered pairs, and non-prefix birth lists are rejected. Saturation is allowed as a state condition but yields no C004 successor.

## Python Lean Cross Layer
Python enforces the invariants in immutable dataclasses. Lean stores the same obligations as fields of `ResponseCapableState` and proves the C014 transport facts. Lean does not need to mirror Python exception classes; the semantic agreement is the accepted-state predicate.

## Countercheck
Removing the initial-prefix condition would make positional C004 selection unsound. Removing either parent orientation would destroy the guaranteed bidirectional provenance backbone. Forbidding additional born-born edges would impose an unsupported tree-only live network.

## Result
C005 is a verified response-capable recurrent state domain with exact rational directed conductances and a canonical C014 base inhabitant.

## Downstream Handoff
- `E015` to C004: exposes the next open slot;
- `E016` to M001: supplies the born carrier;
- `E022` to C007: supplies the current directed network;
- later codomain/update gates remain open.

## Code Anchors
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s01_c005__response_capable_state_schema_xn_n_ge_1.py}
Source SHA-256: `96b9867f44f4a5021cd017033e796f41e0fcc9195c09505796129bdbd469f240`

- `DirectedConductance` - CLASS, lines 24-37; role `SOURCE`.
- `ResponseCapableState` - CLASS, lines 41-104; role `SOURCE`.
- `response_capable_state_from_bootstrap` - FUNCTION, lines 107-124; role `SOURCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s01_c005__response_capable_state_schema_xn_n_ge_1.py}
Source SHA-256: `76c931c265f48c2abaac94e149d867f8c7c6871798465855b52a3baf9e070579`

- `_x1` - FUNCTION, lines 19-25; role `TEST`.
- `TestResponseCapableStateSchema` - CLASS, lines 28-59; role `TEST`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S01_C005_ResponseCapableStateSchemaXnNGe1.lean}
Source SHA-256: `732f5cf1227d57955c144b99043f0c58bb6535ae3a3d2bf3ac584385df0cb6cc`

- `DirectedConductance` - STRUCTURE, lines 26-33; role `SOURCE`.
- `NodeBorn` - DEF, lines 34-39; role `SOURCE`.
- `HasConductance` - DEF, lines 40-45; role `SOURCE`.
- `DistinctConductancePair` - DEF, lines 46-50; role `SOURCE`.
- `ResponseCapableState` - STRUCTURE, lines 51-81; role `SOURCE`.
- `n` - DEF, lines 82-85; role `SOURCE`.
- `one_le_n` - THEOREM, lines 86-95; role `SOURCE`.
- `rootAddress` - DEF, lines 96-99; role `SOURCE`.
- `rootBorn` - THEOREM, lines 100-104; role `SOURCE`.
- `bootstrap_root_ne_newborn` - THEOREM, lines 105-116; role `SOURCE`.
- `bootstrapForwardConductance` - DEF, lines 117-127; role `SOURCE`.
- `bootstrapBackwardConductance` - DEF, lines 128-138; role `SOURCE`.
- `base_case_transports_c014_forward_value` - THEOREM, lines 139-144; role `SOURCE`.
- `base_case_transports_c014_backward_value` - THEOREM, lines 145-150; role `SOURCE`.
- `bootstrap_bornOrdered` - THEOREM, lines 151-158; role `SOURCE`.
- `bootstrap_bornInitial` - THEOREM, lines 159-178; role `SOURCE`.
- `bootstrap_conductancePairsUnique` - THEOREM, lines 179-194; role `SOURCE`.
- `fromBootstrap` - DEF, lines 195-245; role `SOURCE`.
- `fromBootstrap_n` - THEOREM, lines 246-251; role `SOURCE`.

<!-- CNNA-OPEN-PROVENANCE-BEGIN C005 -->
## Open-provenance role: Sufficient finite provenance state

C005 is the current finite candidate for a provenance-sufficient state: it carries the born prefix and response data needed by the next CNNA update.  Whether an arbitrary empirical reduced state admits such a completion is outside the present theorem scope.

<!-- CNNA-OPEN-PROVENANCE-END C005 -->
