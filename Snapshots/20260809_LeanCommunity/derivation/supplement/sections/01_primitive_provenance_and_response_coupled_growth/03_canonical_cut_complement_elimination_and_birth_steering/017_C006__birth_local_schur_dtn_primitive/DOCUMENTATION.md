# 017 · C006 — Birth-local Schur/DtN primitive

**Canonical node label:** `017 · C006`  
**Current section path:** `1.3.3`  
**Documentation tier:** `D1`

## Position In Derivation
C006 is introduced at the first use of block elimination, before any state-dependent matrix assembly. It is a generic exact partial operator used by M002, C007, and P001.

## Mathematical Contract
For ordered blocks `K_BB`, `K_BI`, `K_IB`, `K_II` with nonempty boundary, an interior solve `X` satisfies `K_II X = K_IB`. The exact domain is existence of exactly one encoded solve. On that domain the response value is `K_BB - K_BI X`.

## Introduction Reason
The cut selector and the network realization must not be conflated with the algebraic elimination rule. C006 isolates the reusable mathematical primitive and makes partiality explicit.

## Explicit Construction
Python uses exact `Fraction` matrices and Gauss-Jordan elimination without tolerance. Lean defines positive-denominator raw fractions, cross-multiplication value equality, matrix multiplication/subtraction, solve and response predicates, and the zero-interior witness.

## Invariants
Boundary coordinates precede interior coordinates. Matrix dimensions are type- or constructor-checked. No transpose, symmetrization, pseudoinverse, regularization, threshold, or condition-number rule is admitted.

## Canonicity Or Uniqueness
`response_exists_of_admissible` and `response_unique_of_admissible` prove existence and value-level uniqueness. `response_of_sameValue` proves independence of raw fraction representation. Structural numerator/denominator equality is intentionally not required.

## Boundary Cases
Boundary size must be positive. Interior size may be zero; then the unique empty solve exists and the response is `K_BB`. A singular nonempty `K_II` is outside the domain rather than regularized numerically.

## Python Lean Cross Layer
Python returns normalized fractions. Lean's core relation compares raw positive-denominator encodings by cross multiplication. P001 later proves the exact semantic bridge to ordinary rational matrix arithmetic; that later theorem is not silently imported into C006.

## Countercheck
Making the operator total with a pseudoinverse would change the model. Comparing raw encodings structurally would make the response depend on normalization. Permuting coordinates inside C006 would violate ownership of the M001 order.

## Result
C006 is a verified exact, partial, representative-independent Schur/DtN response primitive.

## Downstream Handoff
- `E019` to C007 supplies elimination;
- `E135` to P001 supplies the native exact interface;
- later general-cut reuse remains open.

## Code Anchors
### python

Path: \path{derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/s03_c006__birth_local_schur_dtn_primitive.py}
Source SHA-256: `7a16beb12e9cf5e892dbef27b783f4d0a13684aad72b95b6b5e8ef73c75eb64a`

- `InteriorNotAdmissibleError` - CLASS, lines 32-33; role `SOURCE`.
- `_validate_matrix` - FUNCTION, lines 36-47; role `SOURCE`.
- `matrix_subtract` - FUNCTION, lines 50-61; role `SOURCE`.
- `matrix_multiply` - FUNCTION, lines 64-94; role `SOURCE`.
- `OrderedSchurBlocks` - CLASS, lines 98-122; role `SOURCE`.
- `is_interior_solve` - FUNCTION, lines 125-138; role `SOURCE`.
- `_unique_interior_solve` - FUNCTION, lines 141-179; role `SOURCE`.
- `interior_is_admissible` - FUNCTION, lines 182-190; role `SOURCE`.
- `schur_dtn_response_from_solve` - FUNCTION, lines 193-208; role `SOURCE`.
- `schur_dtn_response` - FUNCTION, lines 211-216; role `SOURCE`.

### python_test

Path: \path{derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s03_recurrent_pre_birth_measurement_and_steering/test_s03_c006__birth_local_schur_dtn_primitive.py}
Source SHA-256: `7a8ff76ba2f23fc500aee3c73e81a1f2e8c3adeb701389493acd7b49b2468d94`

- `_raw_of_fraction` - FUNCTION, lines 18-21; role `TEST`.
- `_raw_value` - FUNCTION, lines 24-26; role `TEST`.
- `_raw_add` - FUNCTION, lines 29-32; role `TEST`.
- `_raw_mul` - FUNCTION, lines 35-38; role `TEST`.
- `_raw_sub` - FUNCTION, lines 41-44; role `TEST`.
- `TestBirthLocalSchurDtnPrimitive` - CLASS, lines 47-204; role `TEST`.

### lean_core

Path: \path{derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S03_RecurrentPreBirthMeasurementAndSteering/S03_C006_BirthLocalSchurDtnPrimitive.lean}
Source SHA-256: `da65a94576a7272e5bd0caae1a5f2b690fe8d57faac99283b68f0a9ae92b5fad`

- `RatMatrix` - ABBREV, lines 41-45; role `SOURCE`.
- `ExactFraction` - STRUCTURE, lines 46-53; role `SOURCE`.
- `ofRat` - DEF, lines 54-59; role `SOURCE`.
- `zero` - DEF, lines 60-65; role `SOURCE`.
- `add` - DEF, lines 66-71; role `SOURCE`.
- `mul` - DEF, lines 72-77; role `SOURCE`.
- `sub` - DEF, lines 78-84; role `SOURCE`.
- `SameValue` - DEF, lines 85-89; role `SOURCE`.
- `Represents` - DEF, lines 90-93; role `SOURCE`.
- `sameValue_refl` - THEOREM, lines 94-97; role `SOURCE`.
- `sameValue_symm` - THEOREM, lines 98-102; role `SOURCE`.
- `sameValue_trans` - THEOREM, lines 103-123; role `SOURCE`.
- `sameValue_equivalence` - THEOREM, lines 124-133; role `SOURCE`.
- `congrArgTwoInt` - THEOREM, lines 134-144; role `SOURCE`.
- `add_respects_sameValue` - THEOREM, lines 145-196; role `SOURCE`.
- `mul_respects_sameValue` - THEOREM, lines 197-220; role `SOURCE`.
- `sub_respects_sameValue` - THEOREM, lines 221-272; role `SOURCE`.
- `ofRat_represents` - THEOREM, lines 273-278; role `SOURCE`.
- `add_of_representatives` - THEOREM, lines 279-284; role `SOURCE`.
- `mul_of_representatives` - THEOREM, lines 285-290; role `SOURCE`.
- `sub_of_representatives` - THEOREM, lines 291-296; role `SOURCE`.
- `foldl_add_respects_sameValue` - THEOREM, lines 297-318; role `SOURCE`.
- `ExactFractionMatrix` - ABBREV, lines 319-322; role `SOURCE`.
- `MatrixSameValue` - DEF, lines 323-328; role `SOURCE`.
- `MatrixRepresents` - DEF, lines 329-333; role `SOURCE`.
- `matrixSameValue_refl` - THEOREM, lines 334-339; role `SOURCE`.
- `matrixSameValue_symm` - THEOREM, lines 340-346; role `SOURCE`.
- `matrixSameValue_trans` - THEOREM, lines 347-354; role `SOURCE`.
- `matrixSameValue_equivalence` - THEOREM, lines 355-364; role `SOURCE`.
- `rawMatrixMul` - DEF, lines 365-376; role `SOURCE`.
- `matrixMul` - DEF, lines 377-384; role `SOURCE`.
- `rawMatrixMul_respects_sameValue` - THEOREM, lines 385-399; role `SOURCE`.
- `rawMatrixMul_matches_canonicalEncoding` - THEOREM, lines 400-413; role `SOURCE`.
- `rawMatrixSub` - DEF, lines 414-418; role `SOURCE`.
- `matrixSub` - DEF, lines 419-424; role `SOURCE`.
- `rawMatrixSub_respects_sameValue` - THEOREM, lines 425-434; role `SOURCE`.
- `OrderedSchurBlocks` - STRUCTURE, lines 435-444; role `SOURCE`.
- `IsInteriorSolve` - DEF, lines 445-451; role `SOURCE`.
- `IsInteriorAdmissible` - DEF, lines 452-459; role `SOURCE`.
- `responseFromSolve` - DEF, lines 460-467; role `SOURCE`.
- `IsSchurDtnResponse` - DEF, lines 468-475; role `SOURCE`.
- `response_of_solve` - THEOREM, lines 476-483; role `SOURCE`.
- `response_exists_of_admissible` - THEOREM, lines 484-493; role `SOURCE`.
- `response_unique_of_admissible` - THEOREM, lines 494-513; role `SOURCE`.
- `response_of_sameValue` - THEOREM, lines 514-522; role `SOURCE`.
- `emptyInteriorSolve` - DEF, lines 523-526; role `SOURCE`.
- `zeroInterior_solve` - THEOREM, lines 527-534; role `SOURCE`.
- `zeroInterior_admissible` - THEOREM, lines 535-545; role `SOURCE`.

<!-- CNNA-OPEN-PROVENANCE-BEGIN C006 -->
## Open-provenance role: Exact complement elimination

C006 realizes one specific open-provenance reduction: exact directed Schur/DtN elimination by a unique interior solve.  It is not a partial trace, marginalization, or quantum instrument.

<!-- CNNA-OPEN-PROVENANCE-END C006 -->
