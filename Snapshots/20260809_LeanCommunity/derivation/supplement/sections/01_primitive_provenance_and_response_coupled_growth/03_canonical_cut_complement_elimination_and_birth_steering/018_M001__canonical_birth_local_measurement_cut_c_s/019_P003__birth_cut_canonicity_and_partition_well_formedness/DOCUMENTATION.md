# 019 · P003 — Birth-cut canonicity and partition well-formedness

**Canonical node label:** `019 · P003`  
**Current section path:** `1.3.4.1`  
**Documentation tier:** `D2`

## Position In Derivation
P003 is the explicit proof-certification expansion of M001. It introduces no new cut and no parallel derivation branch.

## Formal Statement
For every valid C005 state and C004 successor, the M001 boundary and interior are born-only, disjoint, exhaustive on the current born carrier, preserve inherited carrier order, exclude the unborn child, and are uniquely determined by the canonical selector.

## Hypotheses
Exactly the hypotheses already carried by M001: C005 state invariants and the C004 next-slot certificate. C018 order is inherited transitively. No P002 dependency is required by the proof term.

## Introduction Reason
M001's construction is scientifically usable by C007 only after its partition and pre-birth properties are independently visible as one falsifiable proof gate.

## Proof Strategy
Reuse the owner definitions. Bornness is proved for the port predicate; complementary filters yield disjointness and coverage; filter order is inherited definitionally; canonical-cut equality yields uniqueness; C004 non-bornness yields child exclusion.

## Lemma Chain
`canonicalCarrier`, `boundary`, `interior`, `IsCanonicalCut`, `canonicalCut_isCanonical`, `unique`, `boundary_node_born`, `interior_node_born`, `boundary_interior_disjoint`, `carrier_covered`, `child_not_in_boundary`, and `child_not_in_interior`.

## Formal Realization
The complete certificate is intentionally internal to the M001 Lean module. P003's code register therefore contains supporting-evidence anchors into that owner module and its independent Python construction/test, rather than a duplicate P003 source file.

## Counterexamples Or Necessity Checks
A boundary containing an un-born address violates the C005 domain. Non-disjoint blocks duplicate matrix coordinates. Non-exhaustive blocks omit live conductances. Reordering a filter result changes the matrix basis. Including the next child imports nonexistent state. Without `IsCanonicalCut`, multiple witnesses could satisfy a weaker partition predicate.

## Axiom Profile
The supporting theorems are in the mathlib-free core and contain no project-local axiom or admitted proof. No new proof source is introduced in D7.

## Result
P003 is closed by exact owner-internal theorems. Its certification edge to M001 is active and verified.

## Remaining Limits
General-cut proof P007 remains future work.

## Downstream Handoff
`E146` certifies M001. `E165` later allows P007 to reuse this birth-local special case but remains blocked.

## Code Line Register
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s04_m001__canonical_birth_local_measurement_cut_cn_snplus1.py}
Source SHA-256: `5b840dcb3b47316e54241816804710479d193db236765717d10fb53a970b120a`

- `is_canonical_birth_local_measurement_cut` - FUNCTION, lines 78-95; role `SUPPORTING_EVIDENCE`.
- `canonical_birth_local_measurement_cut` - FUNCTION, lines 98-147; role `SUPPORTING_EVIDENCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s04_m001__canonical_birth_local_measurement_cut_cn_snplus1.py}
Source SHA-256: `537c5f7f7d66d77c5c906f7dd59e05d640dbe7a7e0b84ee7ce141d08536766b7`

- `TestCanonicalBirthLocalMeasurementCut` - CLASS, lines 39-96; role `SUPPORTING_EVIDENCE`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S04_M001_CanonicalBirthLocalMeasurementCutCnSnplus1.lean}
Source SHA-256: `f8c7821fe45245ba62934d55daa5ab57323895df9ac11a55f14db3e491b5f3e4`

- `canonicalCarrier` - DEF, lines 40-45; role `SUPPORTING_EVIDENCE`.
- `boundary` - DEF, lines 203-207; role `SUPPORTING_EVIDENCE`.
- `interior` - DEF, lines 208-212; role `SUPPORTING_EVIDENCE`.
- `IsCanonicalCut` - DEF, lines 224-228; role `SUPPORTING_EVIDENCE`.
- `canonicalCut_isCanonical` - THEOREM, lines 229-233; role `SUPPORTING_EVIDENCE`.
- `unique` - THEOREM, lines 234-252; role `SUPPORTING_EVIDENCE`.
- `carrier_mem_implies_born` - THEOREM, lines 253-261; role `SUPPORTING_EVIDENCE`.
- `born_implies_carrier_mem` - THEOREM, lines 262-272; role `SUPPORTING_EVIDENCE`.
- `boundary_node_born` - THEOREM, lines 300-306; role `SUPPORTING_EVIDENCE`.
- `interior_node_born` - THEOREM, lines 307-313; role `SUPPORTING_EVIDENCE`.
- `boundary_interior_disjoint` - THEOREM, lines 314-327; role `SUPPORTING_EVIDENCE`.
- `carrier_covered` - THEOREM, lines 328-349; role `SUPPORTING_EVIDENCE`.
- `child_not_in_boundary` - THEOREM, lines 364-369; role `SUPPORTING_EVIDENCE`.
- `child_not_in_interior` - THEOREM, lines 370-378; role `SUPPORTING_EVIDENCE`.
