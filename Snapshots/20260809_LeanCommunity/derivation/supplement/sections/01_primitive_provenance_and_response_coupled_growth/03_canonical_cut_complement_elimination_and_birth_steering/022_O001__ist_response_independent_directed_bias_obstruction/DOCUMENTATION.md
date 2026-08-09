# 022 · O001 — IST response-independent directed-bias obstruction

**Canonical node label:** `022 · O001`  
**Semantic ID:** `O001`  
**Current section path:** `1.3.7`  
**Documentation tier:** `D2`

## Position In Derivation
O001 is introduced after the exact pre-birth response C007 and before the active steering and birth-law handoff. Its role is to prevent the retained legacy implementation from reintroducing numerical channels that are independent of the response-derived scalar.

## Formal Statement
Let

```text
chi = (rank, forward, backward, node_load_scalar, nonlinear_mode,
       backreaction_scale, additive_baseline, geometric_attenuation)
```

be the explicit Boolean presence record. A candidate `(state, slot, response, steering, chi)` is admissible exactly when `chi` equals the all-false record. The accepted output preserves `state`, `slot`, `response`, and `steering` exactly and contains no bias record.

## Hypotheses
The obstruction is source-bound to the retained legacy growth path and to the eight represented mechanism classes. It assumes neither that these names exhaust every imaginable response-independent mechanism nor that no alternative mathematical growth law could contain additional terms.

## Introduction Reason
Earlier auditing covered only rank and forward/backward asymmetry. A later completeness review of the same executable path exposed five further classes: node-load scalars, nonlinear modes, fixed backreaction scales, additive baselines, and geometric attenuation. The admission gate must therefore cover all eight classes before M004 can be regarded as bias-free.

## Proof Strategy
Python supplies an executable AST audit and a runtime admission guard. Lean supplies a generic eight-field record, exact equality with the all-false witness, field-preservation theorems, and one contradiction theorem per active field. The two layers agree on field names, the complete witness, and the four-field admitted output.

## Lemma Chain

```text
IndependentDirectedBiasPresence
  -> noIndependentDirectedBias
  -> IsRemoved / IsAdmissible
  -> acceptBiasFree
  -> accepted_preserves_state/slot/response/steering

one active field
  -> *_blocks_acceptance

legacyResponseIndependentChannels
  -> legacy_channels_not_removed
  -> legacy_candidate_not_admissible
```

## Formal Realization
The Python AST traversal records executable names and assignments in six bound growth functions. Comments and docstrings are not AST symbol uses. Synthetic detection of additive baselines and geometric attenuation is restricted to executable arithmetic patterns. The Lean module contains no Mathlib import and was included in the user-reported prefix-free 26-job Core build.

## Counterexamples Or Necessity Checks
- Activating any one of the eight fields must reject the candidate.
- The incomplete three-channel witness must still reject, but it is not treated as complete.
- The full eight-channel witness must reject.
- A source containing the forbidden words only in comments or docstrings must not trigger the AST audit.
- Acceptance must preserve object identity for all four admitted Python fields and must erase the bias record.

## Axiom Profile
O001 belongs to the Mathlib-free Core. The current evidence is a successful Lean typecheck/root build plus a static policy scan. No stronger claim about a separate `#print axioms` transcript for O001 is made.

## Result
The represented legacy mechanisms are excluded from the active M004 dependency tuple. O001 is a closed and falsifiable implementation obstruction.

## Remaining Limits
This is not a universal mathematical no-go theorem and does not prove M003 positivity. The AST audit is exact for the bound retained source and the declared mechanism classes only.

## Downstream Handoff
O001 hands M004 exactly `(X_n, s_{n+1}, R_n, Sigma_b)` and certifies that the canonical candidate uses the all-false presence record.

## Code Line Register
### python / SOURCE: `s07_o001__ist_response_independent_directed_bias_obstruction.py`
Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s07_o001__ist_response_independent_directed_bias_obstruction.py`  
SHA-256: `f7b9e6366d2f3b2bb9190d24625ca3afd7647e6f83b4f999905597486527e04b`

| Symbol | Kind | Lines |
|---|---|---:|
| `IndependentDirectedBiasPresence` | `CLASS` | 99-117 |
| `CandidateGrowthLawInputs` | `CLASS` | 157-164 |
| `AdmittedGrowthLawInputs` | `CLASS` | 168-174 |
| `ResponseIndependentBiasError` | `CLASS` | 177-178 |
| `LegacyBiasFinding` | `CLASS` | 182-186 |
| `LegacyBiasAudit` | `CLASS` | 190-207 |
| `admit_growth_law_inputs` | `FUNCTION` | 210-229 |
| `_function_symbol_references` | `FUNCTION` | 232-241 |
| `_target_names` | `FUNCTION` | 244-249 |
| `_contains_numeric_one` | `FUNCTION` | 252-258 |
| `_contains_addition` | `FUNCTION` | 261-262 |
| `_synthetic_findings` | `FUNCTION` | 265-300 |
| `audit_legacy_response_independent_bias` | `FUNCTION` | 303-348 |
| `audit_legacy_response_independent_bias_file` | `FUNCTION` | 351-353 |

### python_test / TEST: `test_s07_o001__ist_response_independent_directed_bias_obstruction.py`
Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s07_o001__ist_response_independent_directed_bias_obstruction.py`  
SHA-256: `838e65efd3035c9a02cb326a7e6734403873f3b5caf874b833a6cf7a9dba7d20`

| Symbol | Kind | Lines |
|---|---|---:|
| `_presence_only` | `FUNCTION` | 18-20 |
| `TestIstResponseIndependentDirectedBiasObstruction` | `CLASS` | 23-129 |

### lean_core / SOURCE: `S07_O001_IstResponseIndependentDirectedBiasObstruction.lean`
Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S07_O001_IstResponseIndependentDirectedBiasObstruction.lean`  
SHA-256: `94a45ef69de61a5339b6f288295122ff6e36a386b67ef225a64b5dc6ea2d66a8`

| Symbol | Kind | Lines |
|---|---|---:|
| `IndependentDirectedBiasPresence` | `STRUCTURE` | 30-40 |
| `noIndependentDirectedBias` | `DEF` | 41-51 |
| `legacyRankForwardBackwardBias` | `DEF` | 52-63 |
| `legacyResponseIndependentChannels` | `DEF` | 64-74 |
| `IsRemoved` | `DEF` | 75-78 |
| `CandidateGrowthLawInputs` | `STRUCTURE` | 79-88 |
| `BiasFreeGrowthLawInputs` | `STRUCTURE` | 89-97 |
| `IsAdmissible` | `DEF` | 98-103 |
| `acceptBiasFree` | `DEF` | 104-114 |
| `accepted_preserves_state` | `THEOREM` | 115-121 |
| `accepted_preserves_slot` | `THEOREM` | 122-128 |
| `accepted_preserves_response` | `THEOREM` | 129-135 |
| `accepted_preserves_steering` | `THEOREM` | 136-141 |
| `true_ne_false` | `THEOREM` | 142-146 |
| `rank_bias_blocks_acceptance` | `THEOREM` | 147-156 |
| `forward_bias_blocks_acceptance` | `THEOREM` | 157-166 |
| `backward_bias_blocks_acceptance` | `THEOREM` | 167-176 |
| `node_load_scalar_blocks_acceptance` | `THEOREM` | 177-186 |
| `nonlinear_mode_blocks_acceptance` | `THEOREM` | 187-196 |
| `backreaction_scale_blocks_acceptance` | `THEOREM` | 197-206 |
| `additive_baseline_blocks_acceptance` | `THEOREM` | 207-216 |
| `geometric_attenuation_blocks_acceptance` | `THEOREM` | 217-226 |
| `legacy_channels_not_removed` | `THEOREM` | 227-233 |
| `legacy_candidate_not_admissible` | `THEOREM` | 234-248 |
