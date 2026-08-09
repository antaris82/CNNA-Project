# 018 · M001 — Canonical birth-local measurement cut C_n(s_{n+1})

**Canonical node label:** `018 · M001`  
**Current section path:** `1.3.4`  
**Documentation tier:** `D2`

## Position In Derivation
M001 follows C005 and C004. It owns the state- and slot-dependent ordered cut and owns proof gate P003 internally.

## Formal Statement
For `X_n` and next slot `(p,rho,c)`, the boundary is the canonical-carrier subsequence consisting of the root-to-parent prefix chain of `p` together with born same-parent siblings of ranks `< rho`. The interior is the complementary canonical-carrier subsequence. The unborn child `c` is in neither list.

## Hypotheses
A valid C005 state, a valid C004 `NextOpenSlot`, the inherited C003 grammar, and the inherited C018 order. No response, conductance value, geometry, or downstream steering hypothesis is used.

## Introduction Reason
The C006 operator requires explicit ordered boundary/interior coordinates. Birth locality must therefore be derived from provenance before numerical block entries are assembled.

## Proof Strategy
Construct one canonical carrier list, define a decidable birth-local port predicate, and obtain boundary/interior by complementary filtering. Prove that every selected causal predecessor and older sibling is born, then derive partition properties from the common carrier filter.

## Lemma Chain
`prefixChainAux_mem_prefix` -> `causalPredecessorPort_born`; `earlier_admissible_is_born` from C004 -> `olderSiblingPort_born`; these yield `birthLocalPort_born`. Filtering yields `boundary` and `interior`; `canonicalCut_isCanonical` and `unique` close canonicity. `boundary_node_born`, `interior_node_born`, `boundary_interior_disjoint`, `carrier_covered`, and the child-exclusion theorems close P003.

## Formal Realization
Python constructs immutable filtered tuples and performs runtime partition assertions. Lean defines the same predicates over the canonical carrier and proves the complete owner certificate in `S04_M001_CanonicalBirthLocalMeasurementCutCnSnplus1.lean`.

## Counterexamples Or Necessity Checks
Including the unborn child would turn a pre-birth measurement into a postulated-node measurement. Sorting the two blocks anew would add a second ordering convention. Using weights to select ports would make locality response-dependent. Omitting complementary coverage would leave the C007 state matrix under-specified.

## Axiom Profile
The module is in the mathlib-free core and contains no project-local `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, or `partial` declaration. The current 26-job core build evidence certifies the listed source.

## Result
M001 and its P003 owner gate are closed: the cut is unique, born-only, disjoint, exhaustive, order-preserving by filtering, and strictly pre-birth.

## Remaining Limits
M001 supplies no numerical block entries and proves no interior admissibility. P007 remains a later general-cut generalization and does not keep M001 yellow.

## Downstream Handoff
- `E018` to M002 supplies cut dimensions;
- `E020` to C007 supplies coordinate order;
- `E146` records P003 certification of this owner.

## Code Line Register
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s04_m001__canonical_birth_local_measurement_cut_cn_snplus1.py}
Source SHA-256: `5b840dcb3b47316e54241816804710479d193db236765717d10fb53a970b120a`

- `BirthLocalMeasurementCut` - CLASS, lines 34-53; role `SOURCE`.
- `causal_predecessor_ports` - FUNCTION, lines 56-61; role `SOURCE`.
- `older_sibling_ports` - FUNCTION, lines 64-68; role `SOURCE`.
- `is_birth_local_port` - FUNCTION, lines 71-75; role `SOURCE`.
- `is_canonical_birth_local_measurement_cut` - FUNCTION, lines 78-95; role `SOURCE`.
- `canonical_birth_local_measurement_cut` - FUNCTION, lines 98-147; role `SOURCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s04_m001__canonical_birth_local_measurement_cut_cn_snplus1.py}
Source SHA-256: `537c5f7f7d66d77c5c906f7dd59e05d640dbe7a7e0b84ee7ce141d08536766b7`

- `_state` - FUNCTION, lines 23-36; role `TEST`.
- `TestCanonicalBirthLocalMeasurementCut` - CLASS, lines 39-96; role `TEST`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S04_M001_CanonicalBirthLocalMeasurementCutCnSnplus1.lean}
Source SHA-256: `f8c7821fe45245ba62934d55daa5ab57323895df9ac11a55f14db3e491b5f3e4`

- `canonicalCarrier` - DEF, lines 40-45; role `SOURCE`.
- `prefixChainAux` - DEF, lines 46-54; role `SOURCE`.
- `prefixChainAux_mem_prefix` - THEOREM, lines 55-80; role `SOURCE`.
- `causalPredecessorPorts` - DEF, lines 81-86; role `SOURCE`.
- `olderSiblingPorts` - DEF, lines 87-93; role `SOURCE`.
- `BirthLocalPort` - DEF, lines 94-100; role `SOURCE`.
- `causalPredecessorPort_born` - THEOREM, lines 101-141; role `SOURCE`.
- `olderSiblingPort_born` - THEOREM, lines 142-181; role `SOURCE`.
- `birthLocalPort_born` - THEOREM, lines 182-190; role `SOURCE`.
- `birthLocalPortDecidable` - INSTANCE, lines 191-197; role `SOURCE`.
- `portFlag` - DEF, lines 198-202; role `SOURCE`.
- `boundary` - DEF, lines 203-207; role `SOURCE`.
- `interior` - DEF, lines 208-212; role `SOURCE`.
- `BirthLocalMeasurementCut` - STRUCTURE, lines 213-217; role `SOURCE`.
- `canonicalCut` - DEF, lines 218-223; role `SOURCE`.
- `IsCanonicalCut` - DEF, lines 224-228; role `SOURCE`.
- `canonicalCut_isCanonical` - THEOREM, lines 229-233; role `SOURCE`.
- `unique` - THEOREM, lines 234-252; role `SOURCE`.
- `carrier_mem_implies_born` - THEOREM, lines 253-261; role `SOURCE`.
- `born_implies_carrier_mem` - THEOREM, lines 262-272; role `SOURCE`.
- `birthLocalPort_mem_boundary` - THEOREM, lines 273-285; role `SOURCE`.
- `boundary_mem_iff_birthLocalPort` - THEOREM, lines 286-299; role `SOURCE`.
- `boundary_node_born` - THEOREM, lines 300-306; role `SOURCE`.
- `interior_node_born` - THEOREM, lines 307-313; role `SOURCE`.
- `boundary_interior_disjoint` - THEOREM, lines 314-327; role `SOURCE`.
- `carrier_covered` - THEOREM, lines 328-349; role `SOURCE`.
- `child_not_in_carrier` - THEOREM, lines 350-363; role `SOURCE`.
- `child_not_in_boundary` - THEOREM, lines 364-369; role `SOURCE`.
- `child_not_in_interior` - THEOREM, lines 370-378; role `SOURCE`.

<!-- CNNA-OPEN-PROVENANCE-BEGIN M001 -->
## Open-provenance role: Cut-relative system and environment

M001 selects retained boundary ports and an eliminated interior.  The interior is the environment relative to this cut, not a second primitive substance; changing the cut changes the system/environment roles.

<!-- CNNA-OPEN-PROVENANCE-END M001 -->
