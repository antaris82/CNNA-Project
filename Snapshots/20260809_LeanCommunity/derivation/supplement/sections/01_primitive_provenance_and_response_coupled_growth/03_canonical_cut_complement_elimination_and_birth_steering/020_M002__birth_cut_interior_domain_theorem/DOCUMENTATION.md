# 020 · M002 — Birth-cut interior-domain theorem

**Canonical node label:** `020 · M002`  
**Current section path:** `1.3.5`  
**Documentation tier:** `D2`

## Position In Derivation
M002 connects the M001 cut to the partial C006 primitive before C007 supplies state-dependent numerical entries.

## Formal Statement
`BirthCutBlocks next` has exactly `|B_n|` boundary and `|I_n|` interior coordinates. `InExactDomain next blocks` is definitionally C006 `IsInteriorAdmissible blocks`. On this domain a C006 response exists and is unique in exact fraction value.

## Hypotheses
A valid M001 next-slot cut and explicitly supplied C006 blocks of the cut-induced dimensions. Nonempty-interior admissibility is a hypothesis, not a consequence of dimensions alone.

## Introduction Reason
The original obligation allowed either a universal invertibility theorem or an exact domain statement. M001 contains no numerical entries, so only the exact-domain branch is derivable at this point.

## Proof Strategy
Derive nonempty boundary from the root causal port. Encode dimension agreement in the type of `BirthCutBlocks`. Reuse C006 admissibility for response existence/uniqueness. Prove zero-interior membership directly from C006.

## Lemma Chain
`root_is_birthLocalPort` -> `canonicalBoundary_nonempty`; `mkBirthCutBlocks`; `InExactDomain`; `inExactDomain_iff_c006_admissible`; `exactDomain_response_exists`; `exactDomain_response_unique`; `zeroInterior_inExactDomain`.

## Formal Realization
Python validates dimensions, calls the exact C006 domain predicate, and constructs an identity-versus-zero same-cut contrast witness. Lean encodes dimensions in types and proves the exact handoff without duplicating the executable contrast.

## Counterexamples Or Necessity Checks
For any nonempty interior, identity `K_II` and zero `K_II` have the same dimensions but different admissibility. Therefore dimensions, provenance locality, boundary nonemptiness, positivity of stored conductances, or notation alone cannot justify a total Schur complement.

## Axiom Profile
The module belongs to the mathlib-free core and introduces no project-local admitted theorem. Its source is unchanged by D7.

## Result
M002 closes the domain obligation exactly: zero interior is unconditional; every other case requires exact unique solvability.

## Remaining Limits
M002 does not prove that every reachable C007 realization lies in the domain. Generic first-hit reachability and linear well-posedness are treated later in P001; exact canonical-cut instantiation remains a separate proof target there.

## Downstream Handoff
- `E021` certifies C007's domain;
- `E136` supplies the exact interior-domain interface to P001.

## Code Line Register
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s05_m002__birth_cut_interior_domain_theorem.py}
Source SHA-256: `bf0b213349892ba660a958398cf6d808dca41f1f05bf0c7ac7a832c31bec041d`

- `_zero_matrix` - FUNCTION, lines 37-38; role `SOURCE`.
- `_identity_matrix` - FUNCTION, lines 41-45; role `SOURCE`.
- `validate_birth_cut_block_dimensions` - FUNCTION, lines 48-60; role `SOURCE`.
- `birth_cut_interior_is_admissible` - FUNCTION, lines 63-77; role `SOURCE`.
- `DomainContrastWitness` - CLASS, lines 81-94; role `SOURCE`.
- `domain_contrast_witness` - FUNCTION, lines 97-131; role `SOURCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s05_m002__birth_cut_interior_domain_theorem.py}
Source SHA-256: `5c58c474588d868b35de0066273e40d0edf26c7aa3fdfdb5f5a0ecfddbaedc26`

- `_state` - FUNCTION, lines 22-33; role `TEST`.
- `_zero` - FUNCTION, lines 36-37; role `TEST`.
- `TestBirthCutInteriorDomainTheorem` - CLASS, lines 40-91; role `TEST`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S05_M002_BirthCutInteriorDomainTheorem.lean}
Source SHA-256: `171d52d05001dcffc60fd1a325e1b5ce4c0025bbce75a57cc172e10efdbae669`

- `root_is_birthLocalPort` - THEOREM, lines 36-46; role `SOURCE`.
- `canonicalBoundary_nonempty` - THEOREM, lines 47-54; role `SOURCE`.
- `BirthCutBlocks` - ABBREV, lines 55-60; role `SOURCE`.
- `mkBirthCutBlocks` - DEF, lines 61-74; role `SOURCE`.
- `InExactDomain` - DEF, lines 75-80; role `SOURCE`.
- `inExactDomain_iff_c006_admissible` - THEOREM, lines 81-86; role `SOURCE`.
- `exactDomain_response_exists` - THEOREM, lines 87-95; role `SOURCE`.
- `exactDomain_response_unique` - THEOREM, lines 96-106; role `SOURCE`.
- `admissible_of_interiorSize_eq_zero` - THEOREM, lines 107-117; role `SOURCE`.
- `zeroInterior_inExactDomain` - THEOREM, lines 118-128; role `SOURCE`.
