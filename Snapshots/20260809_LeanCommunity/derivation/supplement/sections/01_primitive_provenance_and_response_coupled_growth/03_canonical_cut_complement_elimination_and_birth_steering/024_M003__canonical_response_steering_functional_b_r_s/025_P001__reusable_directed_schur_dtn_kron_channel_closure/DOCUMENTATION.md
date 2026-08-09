# 025 · P001 — Reusable directed Schur/DtN/Kron channel closure

**Canonical node label:** `025 · P001`  
**Semantic ID:** `P001`  
**Current section path:** `1.3.9.1`  
**Documentation tier:** `D2`

## Position In Derivation
P001 is the sole proof owner for the reusable directed Schur/DtN/Kron closure used by C006, C007, M003, and M004. The Core package remains mathlib-free. The proof package may import pinned mathlib and may depend on Core; the reverse dependency is forbidden.

## Formal Statement
For finite boundary and interior index types, ordered rational blocks `kBB`, `kBI`, `kIB`, and `kII`, and a distinguished boundary coordinate, P001 proves the unregularized closure from four explicit hypotheses:

- all off-diagonal entries of the full block operator are nonpositive;
- every full row sum is exactly zero;
- every interior coordinate reaches the boundary along positive arcs;
- the distinguished boundary coordinate reaches a different boundary coordinate along a positive path.

The resulting public contract includes exact semantic agreement, interior-solve existence and uniqueness, C006 admissibility, response existence, response-witness independence, directed-Laplacian response structure, strict distinguished-port positivity, the canonical M003 scalar handoff, M003/M004 supporting theorems, and independent reuse on a second cut family.

## Hypotheses
The theorem uses the original ordered blocks. It assumes no symmetry, reversibility, inverse, pseudoinverse, regularization, additional grounding vertex, or separately postulated strong connectivity. For the canonical birth-local cut, the four generic hypotheses are derived from C005, M001, M002, and C007. For the independent cut, they are proved directly from two strictly positive rational edge weights.

## Introduction Reason
C006 defines a directed Schur/DtN response at the Core level, while M003 requires a strict positive parent-port response. Without one explicit proof owner, analytic invertibility, sign conventions, representative independence, and the canonical connectivity argument could be duplicated or silently strengthened. P001 centralizes those obligations and makes reuse falsifiable.

## Proof Strategy
### Exact semantic bridge
Core `ExactFraction` values are mapped to rational values, and Core matrix addition, multiplication, subtraction, interior solve, harmonic sign, and response construction are proved entrywise equivalent to transparent rational operations. Rectangular multiplication is stated as the explicit row-by-column finite sum.

### Directed maximum principle and finite solve
A zero-boundary harmonic function satisfies a maximum-defect sum identity. Every defect is nonnegative; zero total defect forces equality across each positive arc. Positive reachability propagates an interior maximum to the boundary, forcing the zero-boundary solution to vanish. The resulting interior linear map is injective; finite equal dimension gives surjectivity and hence existence and uniqueness of the solve.

### Response structure and strict positivity
Harmonic boundary basis functions lie between zero and one. This yields nonpositive off-diagonal response entries and exact row conservation. The distinguished diagonal is nonnegative. If it were zero, the value one would propagate along the distinguished positive path to a different boundary port whose Dirichlet value is zero, a contradiction.

### Canonical cut derivation
M001 coordinates are proved duplicate-free and complete. C007 entries are rewritten as outgoing-degree indicators minus ordered-pair conductance sums. Stored positive conductances induce positive arcs. Interior paths follow the provenance parent relation and decrease depth strictly until the boundary is reached. The distinguished parent reaches another boundary port through the stored bidirectional backbone.

### M003/M004 supporting interface
The unique canonical parent coordinate reduces M003’s address-filtered parent aggregate to the distinguished response diagonal. The P001 M004 predicate hides only proposition-valued positivity evidence; `Subsingleton.elim` aligns such proofs before invoking the existing Core uniqueness theorem. No proof witness is retained as physical model data.

### Independent cut-family reuse
For positive `leftWeight` and `rightWeight`, S11 defines two boundary coordinates and one interior coordinate with blocks

```text
KBB = diag(leftWeight, rightWeight)
KBI = (-leftWeight, -rightWeight)^T
KIB = (-leftWeight, -rightWeight)
KII = (leftWeight + rightWeight)
```

All four generic hypotheses are proved directly, and `independentBidirectedChainClosure` calls only `directedSchurDtnClosure`. The module has no state, next-slot, provenance-address, M001, or C007 parameter.

## Lemma Chain
1. exact fraction and matrix semantics;
2. zero-boundary extension and Laplacian action;
3. maximum-defect nonnegativity and positive-arc propagation;
4. interior-kernel triviality;
5. finite linear existence and uniqueness;
6. response existence and witness independence;
7. harmonic boundary basis bounds;
8. response off-diagonal sign, row conservation, and diagonal nonnegativity;
9. strict distinguished-port positivity;
10. canonical coordinate, matrix, and reachability derivation;
11. M003/M004 supporting theorems;
12. independent bidirected-chain hypotheses and closure.

## Formal Realization
Lean source is split into the aggregate contract module plus S01–S11. The aggregate import is `CNNAProofs.P001.S11_IndependentBidirectedChainCutReuse`, so the public package includes the independent reuse theorem. The proof build is pinned to Lean 4.31.0 and mathlib v4.31.0.

## Counterexamples Or Necessity Checks
- Dropping interior-to-boundary reachability permits a nontrivial zero-boundary interior kernel.
- Dropping the distinguished path to another boundary port removes the strict-positivity contradiction.
- Replacing row conservation by an approximate identity does not prove the exact directed-Laplacian contract.
- Assuming symmetry would exclude the intended directed setting rather than prove it.
- Using an inverse or regularizer would change the C006 model and is therefore forbidden.
- Verifying only the canonical birth cut would not establish generic reuse; the independent bidirected-chain family closes this countercheck.

## Axiom Profile
The exact user-local build completed 26 Core jobs and 8595 proof jobs. All 142 registered declarations passed `P001_CURRENT_PROOF_AXIOM_AUDIT`; `FULL_PACKAGE_BOUNDARY_AUDIT` passed; and the P001 source emitted no warning. The exact transcript is:

```text
derivation/code/lean/audit/evidence/USER_LOCAL_P001_FULL_BUILD_20260806.txt
SHA-256 3329291658b2d7a5f46acc6c1bf48b8a60f6bade5d010aa96d7978be3943170a
```

The registered profile partition is:

```text
117 declarations: propext, Classical.choice, Quot.sound
23 declarations:  propext, Quot.sound
2 declarations:   no axioms
```

No project-local axiom or `sorryAx` occurs. The three transitive Lean/mathlib axioms remain part of the declared trust boundary; their constructive elimination is not claimed.

## Result
P001 is kernel-verified for all 142 registered declarations. The generic directed closure is instantiated on the canonical birth-local cut and independently on a state-free bidirected-chain cut. M003 strict positive steering and the unique M004 birth-law relation are derived without changing their Core definitions.

## Remaining Limits
The result is finite and rational. It does not by itself establish continuum limits, spectral asymptotics, infinite-volume operator algebras, or elimination of the transitive Lean/mathlib axioms. Those claims require separate proof nodes.

## Downstream Handoff
M003 receives a verified positive-domain witness and strict response-steering theorem. M004 receives existence, uniqueness, and representative independence for the derived canonical birth law. Later cuts may reuse `directedSchurDtnClosure` after proving their own four explicit hypotheses.

## Code Line Register

### lean_proof: `S04_ResponseWellDefinedness.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S04_ResponseWellDefinedness.lean`  
SHA-256: `c80d1dc00f55cd84420beb3d747d8b3ec33c0137a41a2a97627f23c94f7ffa07`

| Symbol | Kind | Lines |
|---|---|---:|
| `exactMatrixValue_eq_of_matrixSameValue` | `THEOREM` | 32-41 |
| `c006InteriorAdmissible` | `THEOREM` | 42-56 |
| `responseExists` | `THEOREM` | 57-66 |
| `responseRepresentativeAgreement` | `THEOREM` | 67-84 |
| `responseWitnessIndependent` | `THEOREM` | 85-95 |
| `responseWellDefined` | `THEOREM` | 96-107 |

### lean_proof: `S02_DirectedMaximumPrinciple.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S02_DirectedMaximumPrinciple.lean`  
SHA-256: `9cc036efcd855b49df4a8c0abe5d58a0ef793b0bc2c302e8f312a654ab561aa4`

| Symbol | Kind | Lines |
|---|---|---:|
| `maximumDefectTerm` | `DEF` | 30-37 |
| `zeroBoundaryExtension_vanishesOnBoundary` | `THEOREM` | 38-44 |
| `laplacianAction_zeroBoundaryExtension` | `THEOREM` | 45-66 |
| `zeroBoundaryExtension_isInteriorHarmonic` | `THEOREM` | 67-77 |
| `laplacianAction_neg` | `THEOREM` | 78-95 |
| `maximumDefectSum_eq_zero` | `THEOREM` | 96-126 |
| `maximumDefectTerm_nonnegative` | `THEOREM` | 127-145 |
| `maximum_propagates_across_positive_arc` | `THEOREM` | 146-186 |
| `maximum_propagates_to_boundary` | `THEOREM` | 187-225 |
| `interior_le_zero_of_harmonic_zero_boundary` | `THEOREM` | 226-263 |
| `interior_nonnegative_of_harmonic_zero_boundary` | `THEOREM` | 264-289 |
| `interior_eq_zero_of_harmonic_zero_boundary` | `THEOREM` | 290-305 |
| `interiorKernelTrivial` | `THEOREM` | 306-322 |

### lean_proof: `S05_ResponseDirectedLaplacian.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S05_ResponseDirectedLaplacian.lean`  
SHA-256: `7cfb905f5c409e8daa737037527f364ccc6fb6a23a49b1d851a0c6cf941270dc`

| Symbol | Kind | Lines |
|---|---|---:|
| `boundaryBasis` | `DEF` | 35-39 |
| `boundaryBasis_nonnegative` | `THEOREM` | 40-48 |
| `boundaryBasis_le_one` | `THEOREM` | 49-58 |
| `harmonicBasisPotential` | `DEF` | 59-67 |
| `interiorSolve_columnEquation` | `THEOREM` | 68-82 |
| `harmonicBasisPotential_isInteriorHarmonic` | `THEOREM` | 83-127 |
| `interior_le_of_harmonic_boundary_le` | `THEOREM` | 128-165 |
| `interior_ge_of_harmonic_boundary_ge` | `THEOREM` | 166-193 |
| `harmonicBasisPotential_nonnegative` | `THEOREM` | 194-213 |
| `harmonicBasisPotential_le_one` | `THEOREM` | 214-234 |
| `mathlibResponse_entry_eq_laplacianAction_harmonicBasis` | `THEOREM` | 235-281 |
| `responseOffDiagonalNonpositive` | `THEOREM` | 282-314 |
| `interiorSolve_rowSum_eq_neg_one` | `THEOREM` | 315-387 |
| `mathlibResponse_rowConservative` | `THEOREM` | 388-444 |
| `responseRowConservative` | `THEOREM` | 445-465 |
| `responseDiagonalNonnegative_of_offDiagonal_rowConservative` | `THEOREM` | 466-508 |
| `responseDiagonalNonnegative` | `THEOREM` | 509-523 |
| `directedLaplacianClosure` | `THEOREM` | 524-540 |

### lean_proof: `S03_FiniteLinearWellPosedness.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S03_FiniteLinearWellPosedness.lean`  
SHA-256: `b0ef0574fd41c4f11e6dd43b81e73634030776a8d9265021d07e8ea4f302f317`

| Symbol | Kind | Lines |
|---|---|---:|
| `interiorLinearMap` | `DEF` | 31-37 |
| `interiorLinearMap_apply` | `THEOREM` | 38-51 |
| `interiorLinearMap_injective` | `THEOREM` | 52-75 |
| `interiorLinearMap_surjective` | `THEOREM` | 76-83 |
| `interiorRightHandSideSolveExists` | `THEOREM` | 84-93 |
| `interiorSolveExists` | `THEOREM` | 94-120 |
| `interiorSolveUnique` | `THEOREM` | 121-163 |
| `interiorWellPosed` | `THEOREM` | 164-171 |

### lean_proof: `DirectedSchurDtnKronChannelClosure.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/DirectedSchurDtnKronChannelClosure.lean`  
SHA-256: `19fce24b2000c8ff64690c0b78e4dacc9115bdf34b713bf6054f95f37886db43`

| Symbol | Kind | Lines |
|---|---|---:|
| `RationalMatrix` | `ABBREV` | 46-50 |
| `coreRatMatrixValue` | `DEF` | 51-57 |
| `rationalMatrixMul` | `DEF` | 58-63 |
| `CutVertex` | `ABBREV` | 64-67 |
| `exactFractionValue` | `DEF` | 68-71 |
| `exactMatrixValue` | `DEF` | 72-76 |
| `blockEntry` | `DEF` | 77-87 |
| `PositiveArc` | `DEF` | 88-93 |
| `PositivePath` | `INDUCTIVE` | 94-107 |
| `InteriorPathToBoundary` | `INDUCTIVE` | 108-120 |
| `DirectedCutHypotheses` | `STRUCTURE` | 121-137 |
| `CutPotential` | `ABBREV` | 138-141 |
| `laplacianAction` | `DEF` | 142-148 |
| `VanishesOnBoundary` | `DEF` | 149-153 |
| `IsInteriorHarmonic` | `DEF` | 154-160 |
| `IsInteriorKernelVector` | `DEF` | 161-166 |
| `zeroBoundaryExtension` | `DEF` | 167-175 |
| `InteriorKernelTrivial` | `DEF` | 176-182 |
| `IsMathlibInteriorSolve` | `DEF` | 183-189 |
| `IsHarmonicExtension` | `DEF` | 190-196 |
| `mathlibResponseFromSolve` | `DEF` | 197-204 |
| `ExactSemanticBridge` | `STRUCTURE` | 205-219 |
| `InteriorSolveExists` | `DEF` | 220-225 |
| `InteriorSolveUnique` | `DEF` | 226-234 |
| `ResponseWitnessIndependent` | `DEF` | 235-242 |
| `ResponseOffDiagonalNonpositive` | `DEF` | 243-247 |
| `ResponseRowConservative` | `DEF` | 248-252 |
| `ResponseDiagonalNonnegative` | `DEF` | 253-258 |
| `IsDirectedLaplacianResponse` | `DEF` | 259-265 |
| `DistinguishedPortStrictlyPositive` | `DEF` | 266-271 |
| `DirectedSchurDtnClosure` | `STRUCTURE` | 272-293 |
| `ReusableDirectedClosureContract` | `DEF` | 294-302 |
| `DistinguishedParentIndex` | `STRUCTURE` | 303-310 |
| `CanonicalBirthCutClosure` | `STRUCTURE` | 311-321 |
| `CanonicalBirthCutClosureContract` | `DEF` | 322-332 |
| `PublicContract` | `DEF` | 333-336 |

### lean_proof: `S01_ExactSemanticBridge.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S01_ExactSemanticBridge.lean`  
SHA-256: `7139f45922bc14d7f8de4180075f7fe4ac687bd9d54b893dcb0e21a092b723d1`

| Symbol | Kind | Lines |
|---|---|---:|
| `exactFractionValue_ofRat` | `THEOREM` | 29-34 |
| `sameValue_iff_exactFractionValue_eq` | `THEOREM` | 35-43 |
| `represents_iff_exactFractionValue_eq` | `THEOREM` | 44-50 |
| `exactFractionValue_zero` | `THEOREM` | 51-56 |
| `exactFractionValue_add` | `THEOREM` | 57-65 |
| `exactFractionValue_mul` | `THEOREM` | 66-72 |
| `exactFractionValue_sub` | `THEOREM` | 73-92 |
| `exactFractionValue_finFoldl_add` | `THEOREM` | 93-111 |
| `finFoldl_add_eq_initial_add_sum` | `THEOREM` | 112-123 |
| `finFoldl_add_eq_sum` | `THEOREM` | 124-129 |
| `exactFractionValue_matrixMul_entry` | `THEOREM` | 130-145 |
| `exactMatrixValue_matrixMul` | `THEOREM` | 146-156 |
| `exactMatrixValue_matrixSub` | `THEOREM` | 157-181 |
| `matrixRepresents_iff_exactMatrixValue_eq` | `THEOREM` | 182-197 |
| `rationalMatrixMul_neg_right` | `THEOREM` | 198-213 |
| `interiorSolveAgreement` | `THEOREM` | 214-223 |
| `harmonicSignAgreement` | `THEOREM` | 224-239 |
| `responseValueAgreement` | `THEOREM` | 240-250 |
| `exactSemanticBridge` | `THEOREM` | 251-258 |

### lean_proof: `S06_DistinguishedPortStrictPositivity.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S06_DistinguishedPortStrictPositivity.lean`  
SHA-256: `4a4c4a94cd888638f483bdefa345798337acd39bbe0d5734524599ad1aa761c5`

| Symbol | Kind | Lines |
|---|---|---:|
| `maximum_propagates_from_distinguished_boundary_across_positive_arc` | `THEOREM` | 35-74 |
| `harmonicBasis_one_propagates_across_positive_arc` | `THEOREM` | 80-146 |
| `harmonicBasis_one_propagates_along_positive_path` | `THEOREM` | 150-174 |
| `harmonicBasis_distinguished_action_ne_zero` | `THEOREM` | 179-208 |
| `distinguishedResponseDiagonal_ne_zero` | `THEOREM` | 212-246 |
| `distinguishedPortStrictlyPositive` | `THEOREM` | 250-267 |
| `directedSchurDtnClosure` | `THEOREM` | 270-288 |
| `reusableDirectedClosureContract` | `THEOREM` | 292-294 |

### lean_proof: `S07_CanonicalBirthCutInstantiation.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S07_CanonicalBirthCutInstantiation.lean`  
SHA-256: `b2ebfafbb319bc64049eacec675f34fb4b7473280b73e03ba6d5d31a31217146`

| Symbol | Kind | Lines |
|---|---|---:|
| `bornNonRoot_nodup` | `THEOREM` | 33-39 |
| `root_not_mem_bornNonRoot` | `THEOREM` | 42-48 |
| `canonicalCarrier_nodup` | `THEOREM` | 51-57 |
| `boundary_nodup` | `THEOREM` | 58-61 |
| `interior_nodup` | `THEOREM` | 64-70 |
| `distinguishedParentIndex_exists` | `THEOREM` | 71-80 |
| `positiveSteering_of_exactFractionValue_pos` | `THEOREM` | 81-98 |
| `parentSelfResponse_value_eq_parentDiagonal` | `THEOREM` | 99-135 |
| `m003ParentPositivity_of_genericClosure` | `THEOREM` | 136-164 |
| `canonicalBirthCutClosure_of_hypotheses` | `THEOREM` | 165-181 |
| `canonicalBirthCutClosureContract` | `THEOREM` | 182-184 |

### lean_proof: `S08_CanonicalDirectedMatrixStructure.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S08_CanonicalDirectedMatrixStructure.lean`  
SHA-256: `0975bb3958c81032d07f27d1d0c58c5057942d70b884d4ad5bc69aeea99475f5`

| Symbol | Kind | Lines |
|---|---|---:|
| `canonicalCutAddress` | `DEF` | 30-38 |
| `canonicalCutAddress_injective` | `THEOREM` | 39-89 |
| `canonicalCutCoordinate_exists` | `THEOREM` | 90-103 |
| `conductanceSourceCoordinate_exists` | `THEOREM` | 104-111 |
| `conductanceTargetCoordinate_exists` | `THEOREM` | 112-120 |
| `ratOutgoingSum` | `DEF` | 121-128 |
| `ratOrderedPairSum` | `DEF` | 129-138 |
| `exactFractionValue_outgoingFold` | `THEOREM` | 139-175 |
| `exactFractionValue_orderedPairFold` | `THEOREM` | 176-223 |
| `exactFractionValue_outgoingSum` | `THEOREM` | 224-230 |
| `exactFractionValue_orderedPairSum` | `THEOREM` | 231-239 |
| `ratDirectedMatrixEntry` | `DEF` | 240-246 |
| `exactFractionValue_directedMatrixEntry` | `THEOREM` | 247-259 |
| `ratOrderedPairSum_nonnegative` | `THEOREM` | 260-284 |
| `ratOrderedPairSum_pos_of_hasConductance` | `THEOREM` | 285-328 |
| `ratOrderedPairSum_self_zero` | `THEOREM` | 329-349 |
| `sum_single_edge_target_indicator` | `THEOREM` | 350-388 |
| `sum_ratOrderedPairSum_eq_ratOutgoingSum` | `THEOREM` | 389-456 |
| `ratDirectedMatrixEntry_eq_indicator_sub_pair` | `THEOREM` | 457-481 |
| `ratDirectedMatrixEntry_row_sum_zero` | `THEOREM` | 482-544 |
| `blockEntry_eq_ratDirectedMatrixEntry` | `THEOREM` | 545-607 |
| `canonicalBlocks_offDiagonalNonpositive` | `THEOREM` | 608-624 |
| `canonicalBlocks_rowConservative` | `THEOREM` | 625-641 |
| `canonicalPositiveArc_of_hasConductance` | `THEOREM` | 642-670 |

### lean_proof: `S09_CanonicalBackboneReachability.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S09_CanonicalBackboneReachability.lean`  
SHA-256: `49110c72b52c07384f0f67a37945f53b88565940464a5c5e62c9dcbaa60074a1`

| Symbol | Kind | Lines |
|---|---|---:|
| `eq_snoc_of_parent?_eq_some` | `THEOREM` | 101-123 |
| `depth_parent_lt_of_parent?_eq_some` | `THEOREM` | 124-155 |
| `immediateParent_mem_causalPredecessorPorts` | `THEOREM` | 156-166 |
| `hasConductance_endpoints_distinct` | `THEOREM` | 167-176 |
| `firstProvenanceSlotOfState` | `DEF` | 177-181 |
| `firstProvenanceAddress_born` | `THEOREM` | 182-222 |
| `firstProvenanceAddress_mem_olderSiblingPorts_of_parent_root` | `THEOREM` | 223-296 |
| `canonicalInteriorPathToBoundary_aux` | `THEOREM` | 297-371 |
| `canonicalEveryInteriorReachesBoundary` | `THEOREM` | 372-400 |
| `canonicalDistinguishedReachesOtherBoundary` | `THEOREM` | 401-489 |
| `canonicalDirectedCutHypotheses` | `THEOREM` | 490-502 |
| `canonicalBirthCutClosure_derived` | `THEOREM` | 503-511 |
| `DerivedCanonicalBirthCutClosureContract` | `DEF` | 512-519 |
| `derivedCanonicalBirthCutClosureContract` | `THEOREM` | 520-526 |
| `DerivedPublicContract` | `DEF` | 527-530 |
| `derivedPublicContract` | `THEOREM` | 531-534 |

### lean_proof: `S10_M003M004ProofFacades.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S10_M003M004ProofFacades.lean`  
SHA-256: `1b0432d2df791fb24dc4d70937b078bea8f89fe42824b9aeb41113977088c53e`

| Symbol | Kind | Lines |
|---|---|---:|
| `canonicalInPositiveSteeringDomain` | `THEOREM` | 32-43 |
| `canonicalResponseSteeringPair_positive` | `THEOREM` | 44-59 |
| `IsDerivedCanonicalBirthLaw` | `DEF` | 60-71 |
| `derivedCanonicalBirthLaw_exists` | `THEOREM` | 72-90 |
| `derivedCanonicalBirthLaw_unique` | `THEOREM` | 91-111 |
| `derivedCanonicalBirthLaw_existsUnique` | `THEOREM` | 112-131 |
| `canonicalActiveBirthInstruction_exists` | `THEOREM` | 132-152 |
| `derivedCanonicalBirthLaws_sameValue` | `THEOREM` | 153-182 |
| `M003M004ProofFacadeContract` | `DEF` | 183-214 |
| `m003M004ProofFacadeContract` | `THEOREM` | 215-229 |

### lean_proof: `S11_IndependentBidirectedChainCutReuse.lean`
Path: `derivation/code/lean/proofs/src/CNNAProofs/P001/S11_IndependentBidirectedChainCutReuse.lean`  
SHA-256: `1bf9b8cb1a7793c1a2c15f07b1d09fe3f959588f8f7eabcd4591bf1c9f85f470`

| Symbol | Kind | Lines |
|---|---|---:|
| `independentChainBoundaryWeight` | `DEF` | 28-30 |
| `independentBidirectedChainBlocks` | `DEF` | 34-45 |
| `independentBidirectedChainOffDiagonalNonpositive` | `THEOREM` | 48-81 |
| `independentBidirectedChainRowConservative` | `THEOREM` | 84-156 |
| `independentBidirectedChainInteriorReachesBoundary` | `THEOREM` | 159-175 |
| `independentBidirectedChainDistinguishedReachesOtherBoundary` | `THEOREM` | 179-202 |
| `independentBidirectedChainHypotheses` | `THEOREM` | 206-223 |
| `independentBidirectedChainClosure` | `THEOREM` | 227-236 |
| `SecondCutReuseContract` | `DEF` | 240-245 |
| `secondCutReuseContract` | `THEOREM` | 249-252 |

## External References

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-MULVECLIN-SUPP -->
**EXT-REF-MATHLIB-009 — api reuse.** Johannes Hölzl, Patrick Massot, Casper Putz, and Anne Baanen, *Mathlib module: LinearAlgebra.Matrix.ToLin*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html`; accessed 2026-08-03. Exact location: Matrix.mulVecLin; Matrix.mulVecLin_apply; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Context: Documents the exact bundled matrix action used by the kernel-verified finite-linear proof. Formal status: `PROOF_API_USED_FINITE_LINEAR_WELL_POSEDNESS`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-MULVECLIN-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-RAT-SUPP -->
**EXT-REF-LEAN-004 — api reuse.** The Lean 4 Development Team, *Lean core module: Init.Data.Rat.Lemmas*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Init/Data/Rat/Lemmas.html`; accessed 2026-08-03. Exact location: Rat.mkRat_self; Rat.mkRat_eq_iff; Rat.mkRat_add_mkRat; Rat.mkRat_mul_mkRat; Rat.neg_mkRat; Lean toolchain v4.31.0. Context: Supplies the exact constructor lemmas used to identify C006 fraction arithmetic with ℚ. Formal status: `PROOF_API_USED_EXACT_SEMANTIC_BRIDGE`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-RAT-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-FINFOLD-SUPP -->
**EXT-REF-LEAN-005 — api reuse.** The Lean 4 Development Team, *Lean core module: Init.Data.Fin.Fold*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Init/Data/Fin/Fold.html`; accessed 2026-08-03. Exact location: Fin.foldl_zero; Fin.foldl_succ; Lean toolchain v4.31.0. Context: Supplies the recursion equations used by the fold-to-sum induction. Formal status: `PROOF_API_USED_EXACT_SEMANTIC_BRIDGE`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-FINFOLD-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-FINSUM-SUPP -->
**EXT-REF-MATHLIB-005 — api reuse.** Leanprover Community, *Mathlib module: Algebra.BigOperators.Fin*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html`; accessed 2026-08-03. Exact location: Fin.sum_univ_zero; Fin.sum_univ_succ; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Context: Supplies the finite-sum recursion paired with Fin.foldl. Formal status: `PROOF_API_USED_EXACT_SEMANTIC_BRIDGE`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-FINSUM-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-MATRIX-MUL-SUPP -->
**EXT-REF-MATHLIB-004 — api reuse.** Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, and Lu-Ming Zhang, *Mathlib module: Data.Matrix.Mul*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Mul.html`; accessed 2026-08-03. Exact location: implementation notes and rectangular multiplication definition; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Context: Documents the transparent rectangular product at the Core-to-proof boundary. Formal status: `PROOF_API_USED_EXACT_SEMANTIC_BRIDGE`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-MATRIX-MUL-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-ORDERED-SUM-SUPP -->
**EXT-REF-MATHLIB-007 — api reuse.** Leanprover Community, *Mathlib module: Algebra.Order.BigOperators.Group.Finset*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/BigOperators/Group/Finset.html`; accessed 2026-08-03. Exact location: Finset.sum_eq_zero_iff_of_nonneg; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Context: Documents the exact finite ordered-sum implication used by the directed maximum-principle proof. Formal status: `PROOF_API_USED_DIRECTED_MAXIMUM_PRINCIPLE_AND_STRICT_POSITIVITY`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-ORDERED-SUM-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-FINSET-MAX-SUPP -->
**EXT-REF-MATHLIB-006 — api reuse.** Leanprover Community, *Mathlib module: Data.Finset.Max*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html`; accessed 2026-08-03. Exact location: Finset.exists_max_image; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Context: Documents the finite maximum-selection theorem used in the directed maximum-principle proof. Formal status: `PROOF_API_USED_DIRECTED_MAXIMUM_PRINCIPLE`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-FINSET-MAX-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-SUM-TYPE-SUPP -->
**EXT-REF-MATHLIB-008 — api reuse.** Leanprover Community, *Mathlib module: Data.Fintype.BigOperators*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/BigOperators.html`; accessed 2026-08-03. Exact location: Fintype.sum_sum_type; Fintype.sum_eq_single; Fintype.sum_eq_zero; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Context: Documents the sum-type decomposition and whole-Fintype selected/zero sum APIs used by P001. Formal status: `PROOF_API_USED_DIRECTED_MAXIMUM_PRINCIPLE`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-SUM-TYPE-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-FD-SUPP -->
**EXT-REF-MATHLIB-002 — api reuse.** Chris Hughes, *Mathlib module: FiniteDimensional.Basic*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional/Basic.html`; accessed 2026-08-03. Exact location: `LinearMap.surjective_of_injective`; `LinearMap.injective_iff_surjective`; pinned source commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Context: Documents the finite-dimensional injectivity-to-surjectivity bridge used by the kernel-verified P001 finite-linear proof. Formal status: `PROOF_API_USED_FINITE_LINEAR_WELL_POSEDNESS`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-FD-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-SUPP -->
**EXT-REF-MATHLIB-001 — api coverage audit.** Alexander Bentkamp, Eric Wieser, Jeremy Avigad, and Johan Commelin, *Mathlib module: Matrix.SchurComplement*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/SchurComplement.html`; accessed 2026-08-03. Exact location: module header and main results; pinned source commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Context: Records the exact mathlib Schur-complement API boundary used by the declared contract. Formal status: `API_CONTEXT_ONLY_NO_IMPORTED_HYPOTHESIS`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-MATHLIB-POSDEF-SUPP -->
**EXT-REF-MATHLIB-003 — api scope.** Alexander Bentkamp and Mohanad Ahmed, *Mathlib module: Matrix.PosDef*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html`; accessed 2026-08-03. Exact location: module header; Matrix.PosSemidef and Matrix.PosDef definitions; pinned source commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Context: Documents the deliberate exclusion of Hermitian positive definiteness from the directed P001 contract. Formal status: `API_CONTEXT_ONLY_NO_IMPORTED_HYPOTHESIS`
<!-- CNNA-EXTREF-END EXT-USE-P001-MATHLIB-POSDEF-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-DKP-SUPP -->
**EXT-REF-DKP-001 — load-bearing theorem source.** Tomohiro Sugiyama and Kazuhiro Sato, *Kron Reduction and Effective Resistance of Directed Graphs*, SIAM Journal on Matrix Analysis and Applications 44(1) (2023), 270--292. DOI: `10.1137/22M1480823`. arXiv: `2202.12560v2`; arXiv DOI: `10.48550/arXiv.2202.12560`. Exact location: Definition 3.2; Lemmas 3.3--3.4; Theorem 3.9; arXiv v2 PDF pp. 4, 5, 7. Context: Exact source provenance and theorem-to-CNNA assumption map for the analytical positivity closure. Formal status: `REFERENCE_CONTEXT_INTERNAL_KERNEL_VERIFIED`
<!-- CNNA-EXTREF-END EXT-USE-P001-DKP-SUPP -->

<!-- CNNA-EXTREF-BEGIN EXT-USE-P001-LEAN-SUBSINGLETON-SUPP -->
**EXT-REF-LEAN-006 — formalization guidance.** The Lean 4 Development Team, *Lean 4 source module: Init.Core*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Init/Core.html`; accessed 2026-08-05. Exact location: Subsingleton.elim declaration; Lean 4.31.0 Init.Core. Context: Official Core API used to align proposition-valued positivity witnesses. Formal status: `GUIDANCE_ONLY_INTERNAL_PROOF_TERM`
<!-- CNNA-EXTREF-END EXT-USE-P001-LEAN-SUBSINGLETON-SUPP -->

<!-- CNNA-OPEN-PROVENANCE-BEGIN P001 -->
## Open-provenance role: Reusable elimination theorem

P001 certifies the directed Schur/DtN/Kron specialization independently of the canonical birth cut.  Its generality is mathematical reuse across admissible finite cuts; it does not identify Schur reduction with other open-system reductions.

<!-- CNNA-OPEN-PROVENANCE-END P001 -->
