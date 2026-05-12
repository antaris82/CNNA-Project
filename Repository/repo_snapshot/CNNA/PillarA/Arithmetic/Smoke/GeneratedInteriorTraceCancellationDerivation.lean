import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3cTraceCancellationSourceStatus where
  | sourceFromSM3cRSM3db2RSM3db3RSM3db4aRSM3db5RSM3db6RSM3db7RR3a
  deriving DecidableEq, Repr

inductive SM3eRr3cTraceCancellationDerivationStatus where
  | traceCancellationDerivedFromSM3dbChain
  deriving DecidableEq, Repr

inductive SM3eRr3cTraceCancellationDerivationLedgerStatus where
  | traceCancellationDerivationClosed
  deriving DecidableEq, Repr

inductive SM3eRr3cR4GateStatus where
  | r4MayConsumeOnlyProductCancellationLedger
  deriving DecidableEq, Repr

structure GeneratedInteriorSM3db7RTraceCancellationSource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) where
  interiorBlockProfile : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  productNormalFormLedger :
    GeneratedInteriorSM3db7RProductNormalFormLedger Cell p A P wp W E K T M S H
  sourceStatus : SM3eRr3cTraceCancellationSourceStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  noMatrixInvStatus : SM3eRReRunNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3eRReRunNoExternalInverseOracleStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRReRunNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRReRunNoArithmeticTargetStatus
  interiorBlockProfile_eq_SM3cR :
    interiorBlockProfile.profile = InteriorBlockStructureProfile.treeRecursive
  interiorBlockRestriction_eq_SM3cR :
    interiorBlockProfile.restrictionStatus =
      SM3cRInteriorRestrictionStatus.interiorRestrictionFromSM3bRDirichletMatrix
  interiorBlockEntryClassification_eq_SM3cR :
    interiorBlockProfile.entryClassificationStatus =
      SM3cREntryClassificationStatus.interiorEntriesClassifiedFromGeneratedDirichletEntries
  interiorBlockNoFreeTable_eq_SM3cR :
    interiorBlockProfile.noFreeInteriorBlockStatus =
      SM3cRNoFreeInteriorBlockStatus.noFreeInteriorBlockTable
  localStepStatus_eq_SM3db2R :
    ∀ i : GeneratedInteriorIndex A,
      (T.localStepOf i).stepStatus =
        SM3db2REliminationStepStatus.generatedInteriorEliminationLocalStepClosed
  localStepResidual_eq_SM3cR :
    ∀ i j : GeneratedInteriorIndex A,
      (T.localStepOf i).residualDatum.rowResidual j =
        generatedInteriorLocalRowResidual W (T.localStepOf i).pivotDatum.pivotIndex j
  localStepColumnResidual_eq_SM3cR :
    ∀ i j : GeneratedInteriorIndex A,
      (T.localStepOf i).residualDatum.columnResidual j =
        generatedInteriorLocalColumnResidual W (T.localStepOf i).pivotDatum.pivotIndex j
  traceSource_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  traceTermination_eq_SM3db3R :
    T.terminationStatus = SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier
  accumulatedSourceStatus_eq_SM3db4aR :
    H.sourceAccumulatedEntry.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  matrixSourceStatus_eq_SM3db5R :
    H.sourceMatrix.sourceStatus =
      SM3db5RInverseCandidateMatrixSourceStatus.matrixEntriesFromSM3db4aRAccumulatedEntry
  shapeSeparationStatus_eq_SM3db6R :
    H.sourceShapeSeparation.shapeSeparationStatus =
      SM3db6RShapeSeparationStatus.shapeSeparationFromSM3db5RMatrix
  sourceSeparationStatus_eq_SM3db6R :
    H.sourceShapeSeparation.sourceSeparationStatus =
      SM3db6RSourceSeparationStatus.sourceSeparatedAsSM3db4aRAccumulatedEntry
  handoffConsumptionStatus_eq_SM3db7R :
    H.consumptionGateStatus =
      SM3db7RSM3eRConsumptionGateStatus.sm3eRMayConsumeOnlySM3dbRInverseCandidate
  handoffCandidateEntry_eq_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      H.candidateMatrix i j = generatedInteriorAccumulatedEntryValue T i j
  leftProductNormalForm_eq_r3a :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i j =
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j
  rightProductNormalForm_eq_r3a :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i j =
        GeneratedInteriorSM3db7RRightProductNormalForm T i j
  sourceStatus_eq :
    sourceStatus =
      SM3eRr3cTraceCancellationSourceStatus.sourceFromSM3cRSM3db2RSM3db3RSM3db4aRSM3db5RSM3db6RSM3db7RR3a
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun

namespace GeneratedInteriorSM3db7RTraceCancellationSource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}

def fromSM3dbChain
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInteriorSM3db7RTraceCancellationSource Cell p A P wp W E K T M S H where
  interiorBlockProfile := GeneratedInteriorBlockStructureProfile.fromEntryLemmas W
  productNormalFormLedger := GeneratedInteriorSM3db7RProductNormalFormLedger.fromHandoff H
  sourceStatus :=
    SM3eRr3cTraceCancellationSourceStatus.sourceFromSM3cRSM3db2RSM3db3RSM3db4aRSM3db5RSM3db6RSM3db7RR3a
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus := SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus :=
    SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus := SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus :=
    SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun
  interiorBlockProfile_eq_SM3cR := by
    rfl
  interiorBlockRestriction_eq_SM3cR := by
    rfl
  interiorBlockEntryClassification_eq_SM3cR := by
    rfl
  interiorBlockNoFreeTable_eq_SM3cR := by
    rfl
  localStepStatus_eq_SM3db2R := by
    intro i
    exact (T.localStepOf i).stepStatus_eq
  localStepResidual_eq_SM3cR := by
    intro i j
    exact T.traceStep_residual_eq_SM3cR_interiorBlock i j
  localStepColumnResidual_eq_SM3cR := by
    intro i j
    exact T.traceStep_columnResidual_eq_SM3cR_interiorBlock i j
  traceSource_eq_SM3db3R :=
    T.sourceStatus_eq
  traceTermination_eq_SM3db3R :=
    T.terminationStatus_eq
  accumulatedSourceStatus_eq_SM3db4aR :=
    H.accumulatedSourceStatus_eq_SM3db4aR
  matrixSourceStatus_eq_SM3db5R :=
    H.sourceStatus_eq_SM3db5R
  shapeSeparationStatus_eq_SM3db6R :=
    H.shapeSeparationStatus_eq_SM3db6R
  sourceSeparationStatus_eq_SM3db6R :=
    H.sourceSeparationStatus_eq_SM3db6R
  handoffConsumptionStatus_eq_SM3db7R :=
    H.consumptionGateStatus_eq
  handoffCandidateEntry_eq_accumulatedTraceValue := by
    intro i j
    exact H.candidateMatrixEntry_eq_accumulatedTraceValue i j
  leftProductNormalForm_eq_r3a := by
    intro i j
    exact generatedInteriorSM3db7RLeftProductEntry_eq_sum_accumulated H i j
  rightProductNormalForm_eq_r3a := by
    intro i j
    exact generatedInteriorSM3db7RRightProductEntry_eq_sum_accumulated H i j
  sourceStatus_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RTraceCancellationSource

structure GeneratedInteriorSM3db7RTraceCancellationDerivation
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) where
  source : GeneratedInteriorSM3db7RTraceCancellationSource Cell p A P wp W E K T M S H
  derivationStatus : SM3eRr3cTraceCancellationDerivationStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  noMatrixInvStatus : SM3eRReRunNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3eRReRunNoExternalInverseOracleStatus
  noProductIdentityProofStatus : SM3eRReRunNoProductIdentityProofStatus
  sm3fGateStatus : SM3eRReRunSM3fGateStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRReRunNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRReRunNoArithmeticTargetStatus
  leftNormalForm_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductNormalForm T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightNormalForm_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductNormalForm T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftNormalForm_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductNormalForm T i i = 1
  leftNormalForm_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RLeftProductNormalForm T i j = 0
  rightNormalForm_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductNormalForm T i i = 1
  rightNormalForm_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RRightProductNormalForm T i j = 0
  derivationStatus_eq :
    derivationStatus =
      SM3eRr3cTraceCancellationDerivationStatus.traceCancellationDerivedFromSM3dbChain
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus_eq :
    sm3fGateStatus = SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun

namespace GeneratedInteriorSM3db7RTraceCancellationDerivation

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}

def fromSource
    (Q : GeneratedInteriorSM3db7RTraceCancellationSource Cell p A P wp W E K T M S H)
    (leftEntryIdentity :
      ∀ i j : GeneratedInteriorIndex A,
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j =
          (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j)
    (rightEntryIdentity :
      ∀ i j : GeneratedInteriorIndex A,
        GeneratedInteriorSM3db7RRightProductNormalForm T i j =
          (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j)
    (leftDiagonal :
      ∀ i : GeneratedInteriorIndex A,
        GeneratedInteriorSM3db7RLeftProductNormalForm T i i = 1)
    (leftOffdiag :
      ∀ i j : GeneratedInteriorIndex A,
        i ≠ j → GeneratedInteriorSM3db7RLeftProductNormalForm T i j = 0)
    (rightDiagonal :
      ∀ i : GeneratedInteriorIndex A,
        GeneratedInteriorSM3db7RRightProductNormalForm T i i = 1)
    (rightOffdiag :
      ∀ i j : GeneratedInteriorIndex A,
        i ≠ j → GeneratedInteriorSM3db7RRightProductNormalForm T i j = 0) :
    GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H where
  source := Q
  derivationStatus :=
    SM3eRr3cTraceCancellationDerivationStatus.traceCancellationDerivedFromSM3dbChain
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus := SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus :=
    SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noProductIdentityProofStatus :=
    SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus := SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus := SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus :=
    SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun
  leftNormalForm_entry_eq_identity := leftEntryIdentity
  rightNormalForm_entry_eq_identity := rightEntryIdentity
  leftNormalForm_diagonal_entry := leftDiagonal
  leftNormalForm_offdiag_entry := leftOffdiag
  rightNormalForm_diagonal_entry := rightDiagonal
  rightNormalForm_offdiag_entry := rightOffdiag
  derivationStatus_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  sm3fGateStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RTraceCancellationDerivation

def traceCancellationInvariant_from_SM3dbChain
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H) :
    GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H where
  productNormalFormLedger := D.source.productNormalFormLedger
  status := SM3eRReRunTraceCancellationStatus.traceCancellationFromSM3db4aRAccumulatedEntryAndR3aNormalForms
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus := SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus :=
    SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  trace_source_eq_SM3db3R := D.source.traceSource_eq_SM3db3R
  accumulatedSourceStatus_eq_SM3db4aR := D.source.accumulatedSourceStatus_eq_SM3db4aR
  productNormalFormStatus_eq := D.source.productNormalFormLedger.status_eq
  leftNormalForm_entry_eq_identity := D.leftNormalForm_entry_eq_identity
  rightNormalForm_entry_eq_identity := D.rightNormalForm_entry_eq_identity
  leftNormalForm_diagonal_entry := D.leftNormalForm_diagonal_entry
  leftNormalForm_offdiag_entry := D.leftNormalForm_offdiag_entry
  rightNormalForm_diagonal_entry := D.rightNormalForm_diagonal_entry
  rightNormalForm_offdiag_entry := D.rightNormalForm_offdiag_entry
  status_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl

theorem leftNormalFormCancellation_from_traceDerivation
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductNormalForm T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.leftNormalForm_entry_eq_identity i j

theorem rightNormalFormCancellation_from_traceDerivation
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductNormalForm T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.rightNormalForm_entry_eq_identity i j

def productCancellationLedger_from_traceCancellationDerivation
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H) :
    GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H :=
  GeneratedInteriorSM3db7RProductCancellationLedger.fromTraceCancellationInvariant
    (traceCancellationInvariant_from_SM3dbChain D)

structure SM3eRr3cTraceCancellationDerivationLedger
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) where
  derivation : GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H
  traceCancellationInvariant :
    GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H
  productCancellationLedger :
    GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H
  status : SM3eRr3cTraceCancellationDerivationLedgerStatus
  r4GateStatus : SM3eRr3cR4GateStatus
  noProductIdentityProofStatus : SM3eRReRunNoProductIdentityProofStatus
  sm3fGateStatus : SM3eRReRunSM3fGateStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRReRunNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRReRunNoArithmeticTargetStatus
  invariant_eq_derivation :
    traceCancellationInvariant = traceCancellationInvariant_from_SM3dbChain derivation
  productLedger_eq_derivation :
    productCancellationLedger = productCancellationLedger_from_traceCancellationDerivation derivation
  productLedgerStatus_eq :
    productCancellationLedger.status =
      SM3eRReRunProductCancellationLedgerStatus.productCancellationLedgerFromTraceCancellation
  productLedgerNoProductIdentityProof_eq :
    productCancellationLedger.noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  productLedgerSM3fGate_eq :
    productCancellationLedger.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  status_eq :
    status = SM3eRr3cTraceCancellationDerivationLedgerStatus.traceCancellationDerivationClosed
  r4GateStatus_eq :
    r4GateStatus = SM3eRr3cR4GateStatus.r4MayConsumeOnlyProductCancellationLedger
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus_eq :
    sm3fGateStatus = SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun

namespace SM3eRr3cTraceCancellationDerivationLedger

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}

def fromTraceCancellationDerivation
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H) :
    SM3eRr3cTraceCancellationDerivationLedger Cell p A P wp W E K T M S H where
  derivation := D
  traceCancellationInvariant := traceCancellationInvariant_from_SM3dbChain D
  productCancellationLedger := productCancellationLedger_from_traceCancellationDerivation D
  status := SM3eRr3cTraceCancellationDerivationLedgerStatus.traceCancellationDerivationClosed
  r4GateStatus := SM3eRr3cR4GateStatus.r4MayConsumeOnlyProductCancellationLedger
  noProductIdentityProofStatus :=
    SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus := SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus := SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus :=
    SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun
  invariant_eq_derivation := by
    rfl
  productLedger_eq_derivation := by
    rfl
  productLedgerStatus_eq := by
    rfl
  productLedgerNoProductIdentityProof_eq := by
    rfl
  productLedgerSM3fGate_eq := by
    rfl
  status_eq := by
    rfl
  r4GateStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  sm3fGateStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

end SM3eRr3cTraceCancellationDerivationLedger

def regularTraceCancellationSource_from_SM3dbChain
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RTraceCancellationSource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RTraceCancellationSource.fromSM3dbChain
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableTraceCancellationSource_from_SM3dbChain
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RTraceCancellationSource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RTraceCancellationSource.fromSM3dbChain
    (variableSM3dbRToSM3eRHandoff β p wp)

def regularTraceCancellationInvariant_from_SM3dbChain
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp)) :
    GeneratedInteriorSM3db7RTraceCancellationInvariant
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  traceCancellationInvariant_from_SM3dbChain D

def variableTraceCancellationInvariant_from_SM3dbChain
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (D : GeneratedInteriorSM3db7RTraceCancellationDerivation
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp)) :
    GeneratedInteriorSM3db7RTraceCancellationInvariant
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  traceCancellationInvariant_from_SM3dbChain D

end Smoke

end CNNA.PillarA.Arithmetic
