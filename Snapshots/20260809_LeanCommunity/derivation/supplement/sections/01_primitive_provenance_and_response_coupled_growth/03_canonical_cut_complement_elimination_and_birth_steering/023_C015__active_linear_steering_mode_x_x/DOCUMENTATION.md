# 023 · C015 — Active linear steering convention phi(x)=x

**Canonical node label:** `023 · C015`  
**Semantic ID:** `C015`  
**Current section path:** `1.3.8`  
**Documentation tier:** `D0`

## Position In Derivation
C015 is placed after the obstruction gate and before M003. It fixes how an already selected exact response scalar is transformed on the active path.

## Definition Or Statement
For every scalar type `S`,

```text
phi : S -> S
phi(x) = x
```

## Introduction Reason
M003 needs one explicit active-path transform, while robustness controls must remain separate and falsifiable. The identity convention introduces no new model parameter.

## Construction Or Encoding
Python returns its single positional-only argument unchanged. Lean defines `phi x := x` and proves `phi_eq_input` and `phi_eq_identity` by reflexivity.

## Boundary Case Or Countercheck
The API must preserve the exact input object and expose no `mode`, `scale`, `slope`, or `coefficient`. Names associated with logarithmic, saturated, symmetric, or null controls must not appear in the public export set.

## Result
C015 contributes no numerical operation beyond identity and no branch selection.

## Downstream Handoff
The unchanged exact scalar is consumed by M003 after N001/M005 unit normalization.

## Code Anchors
### python / SOURCE: `s08_c015__active_linear_steering_mode_phi_x_x.py`
Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s08_c015__active_linear_steering_mode_phi_x_x.py`  
SHA-256: `92458bb05b2008b7458fa2a5d72fac8676796c696769993b989374a7b574c129`

| Symbol | Kind | Lines |
|---|---|---:|
| `active_linear_steering` | `FUNCTION` | 20-22 |

### python_test / TEST: `test_s08_c015__active_linear_steering_mode_phi_x_x.py`
Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s08_c015__active_linear_steering_mode_phi_x_x.py`  
SHA-256: `97b94a48f62c0a1bd840bc13310a490f42ffded93f6bf433ff37f2edb8d9f394`

| Symbol | Kind | Lines |
|---|---|---:|
| `TestActivePathIdentityTransform` | `CLASS` | 14-50 |

### lean_core / SOURCE: `S08_C015_ActiveLinearSteeringModePhiXX.lean`
Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S08_C015_ActiveLinearSteeringModePhiXX.lean`  
SHA-256: `34378ada95397d5c421585f94834e6fc5e019613bc87a873771e0b32a1630013`

| Symbol | Kind | Lines |
|---|---|---:|
| `phi` | `DEF` | 23-25 |
| `phi_eq_input` | `THEOREM` | 26-28 |
| `phi_eq_identity` | `THEOREM` | 29-34 |
