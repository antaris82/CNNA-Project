import CNNAProofs.P001.S11_IndependentBidirectedChainCutReuse

/-!
# P001 current proof axiom audit

This audit prints the transitive kernel axiom profile of every declaration
through the current R7 M003/M004 thin proof-facade source step.  The shell gate accepts
only Lean's standard proposition/quotient boundary (`propext`, `Quot.sound`)
and `Classical.choice` inherited transitively from the pinned Lean/mathlib
library.  It rejects `sorryAx` and every unregistered axiom.
-/

open CNNAProofs.P001

#print axioms exactFractionValue_ofRat
#print axioms sameValue_iff_exactFractionValue_eq
#print axioms represents_iff_exactFractionValue_eq
#print axioms exactFractionValue_zero
#print axioms exactFractionValue_add
#print axioms exactFractionValue_mul
#print axioms exactFractionValue_sub
#print axioms exactFractionValue_finFoldl_add
#print axioms finFoldl_add_eq_initial_add_sum
#print axioms finFoldl_add_eq_sum
#print axioms exactFractionValue_matrixMul_entry
#print axioms exactMatrixValue_matrixMul
#print axioms exactMatrixValue_matrixSub
#print axioms matrixRepresents_iff_exactMatrixValue_eq
#print axioms rationalMatrixMul_neg_right
#print axioms interiorSolveAgreement
#print axioms harmonicSignAgreement
#print axioms responseValueAgreement
#print axioms exactSemanticBridge

#print axioms zeroBoundaryExtension_vanishesOnBoundary
#print axioms laplacianAction_zeroBoundaryExtension
#print axioms zeroBoundaryExtension_isInteriorHarmonic
#print axioms laplacianAction_neg
#print axioms maximumDefectSum_eq_zero
#print axioms maximumDefectTerm_nonnegative
#print axioms maximum_propagates_across_positive_arc
#print axioms maximum_propagates_to_boundary
#print axioms interior_le_zero_of_harmonic_zero_boundary
#print axioms interior_nonnegative_of_harmonic_zero_boundary
#print axioms interior_eq_zero_of_harmonic_zero_boundary
#print axioms interiorKernelTrivial

#print axioms interiorLinearMap
#print axioms interiorLinearMap_apply
#print axioms interiorLinearMap_injective
#print axioms interiorLinearMap_surjective
#print axioms interiorRightHandSideSolveExists
#print axioms interiorSolveExists
#print axioms interiorSolveUnique
#print axioms interiorWellPosed

#print axioms exactMatrixValue_eq_of_matrixSameValue
#print axioms c006InteriorAdmissible
#print axioms responseExists
#print axioms responseRepresentativeAgreement
#print axioms responseWitnessIndependent
#print axioms responseWellDefined

#print axioms boundaryBasis
#print axioms boundaryBasis_nonnegative
#print axioms boundaryBasis_le_one
#print axioms harmonicBasisPotential
#print axioms interiorSolve_columnEquation
#print axioms harmonicBasisPotential_isInteriorHarmonic
#print axioms interior_le_of_harmonic_boundary_le
#print axioms interior_ge_of_harmonic_boundary_ge
#print axioms harmonicBasisPotential_nonnegative
#print axioms harmonicBasisPotential_le_one
#print axioms mathlibResponse_entry_eq_laplacianAction_harmonicBasis
#print axioms responseOffDiagonalNonpositive
#print axioms interiorSolve_rowSum_eq_neg_one
#print axioms mathlibResponse_rowConservative
#print axioms responseRowConservative
#print axioms responseDiagonalNonnegative_of_offDiagonal_rowConservative
#print axioms responseDiagonalNonnegative
#print axioms directedLaplacianClosure

#print axioms maximum_propagates_from_distinguished_boundary_across_positive_arc
#print axioms harmonicBasis_one_propagates_across_positive_arc
#print axioms harmonicBasis_one_propagates_along_positive_path
#print axioms harmonicBasis_distinguished_action_ne_zero
#print axioms distinguishedResponseDiagonal_ne_zero
#print axioms distinguishedPortStrictlyPositive
#print axioms directedSchurDtnClosure
#print axioms reusableDirectedClosureContract

#print axioms bornNonRoot_nodup
#print axioms root_not_mem_bornNonRoot
#print axioms canonicalCarrier_nodup
#print axioms boundary_nodup
#print axioms interior_nodup
#print axioms distinguishedParentIndex_exists
#print axioms positiveSteering_of_exactFractionValue_pos
#print axioms parentSelfResponse_value_eq_parentDiagonal
#print axioms m003ParentPositivity_of_genericClosure
#print axioms canonicalBirthCutClosure_of_hypotheses
#print axioms canonicalBirthCutClosureContract

/-! R6B.1 canonical directed matrix structure -/
#print axioms canonicalCutAddress
#print axioms canonicalCutAddress_injective
#print axioms canonicalCutCoordinate_exists
#print axioms conductanceSourceCoordinate_exists
#print axioms conductanceTargetCoordinate_exists
#print axioms ratOutgoingSum
#print axioms ratOrderedPairSum
#print axioms exactFractionValue_outgoingFold
#print axioms exactFractionValue_orderedPairFold
#print axioms exactFractionValue_outgoingSum
#print axioms exactFractionValue_orderedPairSum
#print axioms ratDirectedMatrixEntry
#print axioms exactFractionValue_directedMatrixEntry
#print axioms ratOrderedPairSum_nonnegative
#print axioms ratOrderedPairSum_pos_of_hasConductance
#print axioms ratOrderedPairSum_self_zero
#print axioms sum_single_edge_target_indicator
#print axioms sum_ratOrderedPairSum_eq_ratOutgoingSum
#print axioms ratDirectedMatrixEntry_eq_indicator_sub_pair
#print axioms ratDirectedMatrixEntry_row_sum_zero
#print axioms blockEntry_eq_ratDirectedMatrixEntry
#print axioms canonicalBlocks_offDiagonalNonpositive
#print axioms canonicalBlocks_rowConservative
#print axioms canonicalPositiveArc_of_hasConductance

/-! R6B.2 canonical backbone reachability and derived closure -/
#print axioms eq_snoc_of_parent?_eq_some
#print axioms depth_parent_lt_of_parent?_eq_some
#print axioms immediateParent_mem_causalPredecessorPorts
#print axioms hasConductance_endpoints_distinct
#print axioms firstProvenanceSlotOfState
#print axioms firstProvenanceAddress_born
#print axioms firstProvenanceAddress_mem_olderSiblingPorts_of_parent_root
#print axioms canonicalInteriorPathToBoundary_aux
#print axioms canonicalEveryInteriorReachesBoundary
#print axioms canonicalDistinguishedReachesOtherBoundary
#print axioms canonicalDirectedCutHypotheses
#print axioms canonicalBirthCutClosure_derived
#print axioms DerivedCanonicalBirthCutClosureContract
#print axioms derivedCanonicalBirthCutClosureContract
#print axioms DerivedPublicContract
#print axioms derivedPublicContract
/-! R7 thin M003/M004 proof facades -/
#print axioms canonicalInPositiveSteeringDomain
#print axioms canonicalResponseSteeringPair_positive
#print axioms IsDerivedCanonicalBirthLaw
#print axioms derivedCanonicalBirthLaw_exists
#print axioms derivedCanonicalBirthLaw_unique
#print axioms derivedCanonicalBirthLaw_existsUnique
#print axioms canonicalActiveBirthInstruction_exists
#print axioms derivedCanonicalBirthLaws_sameValue
#print axioms M003M004ProofFacadeContract
#print axioms m003M004ProofFacadeContract


/-! R8 independent bidirected-chain cut reuse -/
#print axioms independentChainBoundaryWeight
#print axioms independentBidirectedChainBlocks
#print axioms independentBidirectedChainOffDiagonalNonpositive
#print axioms independentBidirectedChainRowConservative
#print axioms independentBidirectedChainInteriorReachesBoundary
#print axioms independentBidirectedChainDistinguishedReachesOtherBoundary
#print axioms independentBidirectedChainHypotheses
#print axioms independentBidirectedChainClosure
#print axioms SecondCutReuseContract
#print axioms secondCutReuseContract
