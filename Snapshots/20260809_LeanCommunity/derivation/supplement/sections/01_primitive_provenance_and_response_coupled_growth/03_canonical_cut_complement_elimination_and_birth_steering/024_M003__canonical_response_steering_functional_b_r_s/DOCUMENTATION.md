# 024 · M003 — Canonical response-steering functional Sigma_b[R_n,s]

**Canonical node label:** `024 · M003`  
**Semantic ID:** `M003`  
**Current section path:** `1.3.9`  
**Documentation tier:** `D2`

## Position In Derivation
M003 receives the exact C007 response in M001 boundary order and supplies the unique exact scalar and proved positive domain consumed by M004.

## Formal Statement
For `p = parentAddress(next)`, `sigma(next,lambda)` is the address-filtered sum of the `lambda[i,i]` terms whose boundary address equals `p`. With `C_star = 1` and the C015 identity transform, no further normalization changes the value. `CanonicalM003Closure realization` states that the canonical realization lies in `InPositiveSteeringDomain`, has a response-steering pair, and every response-steering pair has `PositiveSteering`.

## Hypotheses
- `next` is the canonical C004 slot of a C005 response-capable state.
- `realization` is the actual C005/M001/C006/C007 state-directed block realization.
- The P001 reusable directed-cut hypotheses are derived for that realization; no parent coordinate or positivity witness is a public input.

## Introduction Reason
C007 returns a boundary response matrix while M004 requires one provenance-selected scalar. The closure must discharge the distinguished coordinate internally so downstream code cannot choose a different port.

## Proof Strategy
Core establishes address membership, exact aggregation, uniqueness, and representative invariance. P001 establishes response well-posedness and strict distinguished-port positivity. `canonicalM003Closure` obtains the parent coordinate from `distinguishedParentIndex_exists`, constructs the internal witness, and packages the resulting domain, existence, and universal positivity statements.

## Lemma Chain
```text
parent_mem_boundary -> sigma -> responseSteeringPair_exists
P001 canonical cut closure -> canonicalInPositiveSteeringDomain
canonicalInPositiveSteeringDomain -> canonicalResponseSteeringPair_positive
internal distinguishedParentIndex_exists -> canonicalM003Closure
```

## Formal Realization
The mathlib-free Core defines the scalar and predicates. The proof module `S01_CanonicalM003Closure.lean` imports only the verified P001 facade and exports a public theorem whose only explicit data argument is the canonical realization.

## Counterexamples Or Necessity Checks
- A missing or duplicated parent address cannot be repaired by a selected coordinate.
- Zero is retained as an exact negative control but is not in the active positive domain.
- Equivalent fraction or matrix representatives must not alter the scalar.
- Rank, sibling number, depth, clipping, baseline, or hidden mode parameters are absent.

## Axiom Profile
P001 remains bound to its verified 142-declaration profile. All four M003 closure declarations are kernel-compiled and axiom-audited: two use `propext` and `Quot.sound`, and two additionally use transitive `Classical.choice`. No project-local axiom or `sorry` is admitted.

## Result
M003 has a closed end-to-end interface without an external parent index: canonical response-domain inhabitance, response-steering existence, and universal strict positivity are packaged in `CanonicalM003Closure`.

## Remaining Limits
The result is finite and rational. Transitive `propext`, `Classical.choice`, and `Quot.sound` remain within the explicitly admitted Lean/mathlib trust boundary; their elimination is not claimed.

## Downstream Handoff
M004 consumes `CanonicalM003Closure` directly. It does not reconstruct the Schur/DtN proof and does not receive positivity as a caller-supplied assumption.

## Code Line Register
### python / SOURCE: `s09_m003__canonical_response_steering_functional_sigma_b_rn_s.py`
Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s09_m003__canonical_response_steering_functional_sigma_b_rn_s.py`  
SHA-256: `bee99c2edb4d1de28d4366dea75f1d587eb0c25146f104f98862cc85120a1009`

| Symbol | Kind | Lines |
|---|---|---:|
| `CanonicalResponseSteering` | `CLASS` | 47-72 |
| `is_positive_response_steering` | `FUNCTION` | 75-82 |
| `parent_port_self_response` | `FUNCTION` | 85-99 |
| `canonical_response_steering_functional` | `FUNCTION` | 102-120 |

### python_test / TEST: `test_s09_m003__canonical_response_steering_functional_sigma_b_rn_s.py`
Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s09_m003__canonical_response_steering_functional_sigma_b_rn_s.py`  
SHA-256: `911102ca3ae3fe8a4a822b1569f4d8b52e9cf040635971dc3812baa324a8a067`

| Symbol | Kind | Lines |
|---|---|---:|
| `_bootstrap_state` | `FUNCTION` | 33-39 |
| `_state` | `FUNCTION` | 42-53 |
| `TestCanonicalResponseSteeringFunctional` | `CLASS` | 56-148 |

### lean_core / SOURCE: `S09_M003_CanonicalResponseSteeringFunctionalSigmaBRnS.lean`
Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S09_M003_CanonicalResponseSteeringFunctionalSigmaBRnS.lean`  
SHA-256: `1ecd0f0d2afe74458cae30490db430306c0ee9e79550eada2b2f80b66f398c8e`

| Symbol | Kind | Lines |
|---|---|---:|
| `terminal_mem_prefixChainAux` | `THEOREM` | 38-60 |
| `parent_mem_causalPredecessorPorts` | `THEOREM` | 61-71 |
| `parent_mem_boundary` | `THEOREM` | 72-79 |
| `parentDiagonalTerm` | `DEF` | 80-90 |
| `parentSelfResponse` | `DEF` | 91-101 |
| `unitNormalizedParentResponse` | `DEF` | 102-108 |
| `selected_conductance_unit_eq_one` | `THEOREM` | 109-114 |
| `sigma` | `DEF` | 115-121 |
| `IsCanonicalResponseSteering` | `DEF` | 122-128 |
| `sigma_eq_unitNormalizedParentResponse` | `THEOREM` | 129-136 |
| `sigma_eq_parentSelfResponse` | `THEOREM` | 137-145 |
| `PositiveSteering` | `DEF` | 146-150 |
| `parentDiagonalTerm_respects_matrixSameValue` | `THEOREM` | 151-168 |
| `parentSelfResponse_respects_matrixSameValue` | `THEOREM` | 169-184 |
| `sigma_respects_matrixSameValue` | `THEOREM` | 185-197 |
| `steering_exists` | `THEOREM` | 198-206 |
| `steering_unique` | `THEOREM` | 207-218 |
| `response_representatives_give_same_steering` | `THEOREM` | 219-231 |
| `IsResponseSteeringPair` | `DEF` | 232-241 |
| `IsPositiveResponseSteeringPair` | `DEF` | 242-252 |
| `DirectedKronParentPositivityAt` | `DEF` | 253-262 |
| `InPositiveSteeringDomain` | `DEF` | 263-268 |
| `inPositiveSteeringDomain_iff` | `THEOREM` | 269-276 |
| `responseSteeringPair_exists` | `THEOREM` | 277-289 |
| `responseSteeringPair_value_unique` | `THEOREM` | 290-311 |

### lean_proof / PROOF: `S01_CanonicalM003Closure.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/M003M004/S01_CanonicalM003Closure.lean`  
SHA-256: `d96d928f48f0780e3b728b3777d2b58e99349ef901743113f172b1a5c0e7ce9c`

| Symbol | Kind | Lines |
|---|---|---:|
| `CanonicalM003Closure` | `STRUCTURE` | 28-44 |
| `canonicalM003Closure` | `THEOREM` | 45-65 |
| `CanonicalM003ClosureContract` | `DEF` | 66-72 |
| `canonicalM003ClosureContract` | `THEOREM` | 73-76 |

<!-- CNNA-OPEN-PROVENANCE-BEGIN M003 -->
## Open-provenance role: Response-to-event specialization

M003 converts the effective boundary response into the unique positive scalar used by the next event.  This is the response-coupling step of the current deterministic specialization, not a universal law for all open systems.

<!-- CNNA-OPEN-PROVENANCE-END M003 -->
