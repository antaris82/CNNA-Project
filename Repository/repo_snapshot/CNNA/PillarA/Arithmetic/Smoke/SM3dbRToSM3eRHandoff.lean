import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db7RHandoffStatus where
  | handoffFromSM3db6RShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db7RSM3eRConsumptionGateStatus where
  | sm3eRMayConsumeOnlySM3dbRInverseCandidate
  deriving DecidableEq, Repr

inductive SM3db7RNoLeftProductStatus where
  | noLeftProductInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoRightProductStatus where
  | noRightProductInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoProductValidationStatus where
  | noProductValidationInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoRepairFormulaStatus where
  | noRepairFormulaInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoNewCandidateEntryStatus where
  | noNewCandidateEntryInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoSM3daRFallbackStatus where
  | noSM3daRFallbackInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoFreeMatrixStatus where
  | noFreeMatrixOrEntryTableInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoMatrixInvStatus where
  | noMatrixInvInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db7RHandoff
  deriving DecidableEq, Repr

inductive SM3db7RNextGateStatus where
  | positiveSM3eRReRunAfterHandoff
  deriving DecidableEq, Repr

inductive SM3db7RGeneratedInverseCandidateLedgerStatus where
  | generatedInverseCandidateHandoffClosed
  deriving DecidableEq, Repr

structure SM3dbRToSM3eRHandoff
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) where
  sourceShapeSeparation :
    GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M
  sourceMatrix : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T
  sourceAccumulatedEntry :
    GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T
  sourceCandidateEntry : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W
  candidateMatrix : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ
  handoffStatus : SM3db7RHandoffStatus
  consumptionGateStatus : SM3db7RSM3eRConsumptionGateStatus
  noLeftProductStatus : SM3db7RNoLeftProductStatus
  noRightProductStatus : SM3db7RNoRightProductStatus
  noProductValidationStatus : SM3db7RNoProductValidationStatus
  noRepairFormulaStatus : SM3db7RNoRepairFormulaStatus
  noNewCandidateEntryStatus : SM3db7RNoNewCandidateEntryStatus
  noSM3daRFallbackStatus : SM3db7RNoSM3daRFallbackStatus
  noFreeMatrixStatus : SM3db7RNoFreeMatrixStatus
  noMatrixInvStatus : SM3db7RNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noTwoSidedInvStatus : SM3db7RNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus :
    SM3db7RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db7RNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db7RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db7RNoArithmeticTargetStatus
  nextGateStatus : SM3db7RNextGateStatus
  sourceShapeSeparation_eq : sourceShapeSeparation = S
  sourceMatrix_eq_SM3db6R_sourceMatrix : sourceMatrix = S.sourceMatrix
  sourceMatrix_eq_SM3db5R_matrixExport : sourceMatrix = M
  sourceAccumulatedEntry_eq_SM3db6R_accumulatedEntry :
    sourceAccumulatedEntry = S.accumulatedInverseCandidateEntry
  sourceCandidateEntry_eq_SM3db6R_sourceCandidateEntry :
    sourceCandidateEntry = S.sourceCandidateEntry
  candidateMatrix_eq_SM3db6R_shapeSeparationMatrix : candidateMatrix = S.matrix
  candidateMatrixEntry_eq_SM3db6R_shapeSeparationMatrix :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix i j = S.matrix i j
  candidateMatrixEntry_eq_SM3db5R_matrixExport :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix i j = M.matrix i j
  candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix i j = S.accumulatedInverseCandidateEntry.entry i j
  candidateMatrixEntry_eq_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix i j = generatedInteriorAccumulatedEntryValue T i j
  sourceStatus_eq_SM3db5R :
    sourceMatrix.sourceStatus =
      SM3db5RInverseCandidateMatrixSourceStatus.matrixEntriesFromSM3db4aRAccumulatedEntry
  accumulatedSourceStatus_eq_SM3db4aR :
    sourceAccumulatedEntry.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  shapeSeparationStatus_eq_SM3db6R :
    sourceShapeSeparation.shapeSeparationStatus =
      SM3db6RShapeSeparationStatus.shapeSeparationFromSM3db5RMatrix
  sourceSeparationStatus_eq_SM3db6R :
    sourceShapeSeparation.sourceSeparationStatus =
      SM3db6RSourceSeparationStatus.sourceSeparatedAsSM3db4aRAccumulatedEntry
  handoffStatus_eq :
    handoffStatus = SM3db7RHandoffStatus.handoffFromSM3db6RShapeSeparation
  consumptionGateStatus_eq :
    consumptionGateStatus =
      SM3db7RSM3eRConsumptionGateStatus.sm3eRMayConsumeOnlySM3dbRInverseCandidate
  noLeftProductStatus_eq :
    noLeftProductStatus = SM3db7RNoLeftProductStatus.noLeftProductInSM3db7RHandoff
  noRightProductStatus_eq :
    noRightProductStatus = SM3db7RNoRightProductStatus.noRightProductInSM3db7RHandoff
  noProductValidationStatus_eq :
    noProductValidationStatus =
      SM3db7RNoProductValidationStatus.noProductValidationInSM3db7RHandoff
  noRepairFormulaStatus_eq :
    noRepairFormulaStatus = SM3db7RNoRepairFormulaStatus.noRepairFormulaInSM3db7RHandoff
  noNewCandidateEntryStatus_eq :
    noNewCandidateEntryStatus =
      SM3db7RNoNewCandidateEntryStatus.noNewCandidateEntryInSM3db7RHandoff
  noSM3daRFallbackStatus_eq :
    noSM3daRFallbackStatus =
      SM3db7RNoSM3daRFallbackStatus.noSM3daRFallbackInSM3db7RHandoff
  noFreeMatrixStatus_eq :
    noFreeMatrixStatus =
      SM3db7RNoFreeMatrixStatus.noFreeMatrixOrEntryTableInSM3db7RHandoff
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db7RNoMatrixInvStatus.noMatrixInvInSM3db7RHandoff
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3db7RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db7RHandoff
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db7RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db7RHandoff
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db7RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db7RHandoff
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db7RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db7RHandoff
  nextGateStatus_eq :
    nextGateStatus = SM3db7RNextGateStatus.positiveSM3eRReRunAfterHandoff

namespace SM3dbRToSM3eRHandoff

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

def fromShapeSeparation
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S where
  sourceShapeSeparation := S
  sourceMatrix := M
  sourceAccumulatedEntry := S.accumulatedInverseCandidateEntry
  sourceCandidateEntry := S.sourceCandidateEntry
  candidateMatrix := S.matrix
  handoffStatus := SM3db7RHandoffStatus.handoffFromSM3db6RShapeSeparation
  consumptionGateStatus :=
    SM3db7RSM3eRConsumptionGateStatus.sm3eRMayConsumeOnlySM3dbRInverseCandidate
  noLeftProductStatus := SM3db7RNoLeftProductStatus.noLeftProductInSM3db7RHandoff
  noRightProductStatus := SM3db7RNoRightProductStatus.noRightProductInSM3db7RHandoff
  noProductValidationStatus :=
    SM3db7RNoProductValidationStatus.noProductValidationInSM3db7RHandoff
  noRepairFormulaStatus := SM3db7RNoRepairFormulaStatus.noRepairFormulaInSM3db7RHandoff
  noNewCandidateEntryStatus :=
    SM3db7RNoNewCandidateEntryStatus.noNewCandidateEntryInSM3db7RHandoff
  noSM3daRFallbackStatus :=
    SM3db7RNoSM3daRFallbackStatus.noSM3daRFallbackInSM3db7RHandoff
  noFreeMatrixStatus :=
    SM3db7RNoFreeMatrixStatus.noFreeMatrixOrEntryTableInSM3db7RHandoff
  noMatrixInvStatus := SM3db7RNoMatrixInvStatus.noMatrixInvInSM3db7RHandoff
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noTwoSidedInvStatus := SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff
  noInteriorEliminationCertificateStatus :=
    SM3db7RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db7RHandoff
  noInteriorEliminationDataStatus :=
    SM3db7RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db7RHandoff
  noDtnDataStatus :=
    SM3db7RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db7RHandoff
  noArithmeticTargetStatus :=
    SM3db7RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db7RHandoff
  nextGateStatus := SM3db7RNextGateStatus.positiveSM3eRReRunAfterHandoff
  sourceShapeSeparation_eq := by
    rfl
  sourceMatrix_eq_SM3db6R_sourceMatrix := S.sourceMatrix_eq.symm
  sourceMatrix_eq_SM3db5R_matrixExport := by
    rfl
  sourceAccumulatedEntry_eq_SM3db6R_accumulatedEntry := by
    rfl
  sourceCandidateEntry_eq_SM3db6R_sourceCandidateEntry := by
    rfl
  candidateMatrix_eq_SM3db6R_shapeSeparationMatrix := by
    rfl
  candidateMatrixEntry_eq_SM3db6R_shapeSeparationMatrix := by
    intro i j
    rfl
  candidateMatrixEntry_eq_SM3db5R_matrixExport := by
    intro i j
    exact S.matrixEntry_from_SM3db5RMatrix i j
  candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry := by
    intro i j
    exact S.matrixEntry_from_accumulatedEntry i j
  candidateMatrixEntry_eq_accumulatedTraceValue := by
    intro i j
    exact S.matrixEntry_from_accumulatedTraceValue i j
  sourceStatus_eq_SM3db5R := M.sourceStatus_eq
  accumulatedSourceStatus_eq_SM3db4aR := S.accumulatedSourceStatus_eq_SM3db4aR
  shapeSeparationStatus_eq_SM3db6R := S.shapeSeparationStatus_eq
  sourceSeparationStatus_eq_SM3db6R := S.sourceSeparationStatus_eq
  handoffStatus_eq := by
    rfl
  consumptionGateStatus_eq := by
    rfl
  noLeftProductStatus_eq := by
    rfl
  noRightProductStatus_eq := by
    rfl
  noProductValidationStatus_eq := by
    rfl
  noRepairFormulaStatus_eq := by
    rfl
  noNewCandidateEntryStatus_eq := by
    rfl
  noSM3daRFallbackStatus_eq := by
    rfl
  noFreeMatrixStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextGateStatus_eq := by
    rfl

end SM3dbRToSM3eRHandoff

def sm3dbRToSM3eRHandoff_from_shapeSeparation
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S :=
  SM3dbRToSM3eRHandoff.fromShapeSeparation S

def SM3eRMayConsumeOnlySM3dbRInverseCandidate
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) : Prop :=
  H.consumptionGateStatus =
    SM3db7RSM3eRConsumptionGateStatus.sm3eRMayConsumeOnlySM3dbRInverseCandidate

theorem sm3eRMayConsumeOnlySM3dbRInverseCandidate_for_handoff
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    SM3eRMayConsumeOnlySM3dbRInverseCandidate H :=
  H.consumptionGateStatus_eq

theorem handoffCandidate_eq_SM3db6R_shapeSeparationMatrix
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    H.candidateMatrix = S.matrix :=
  H.candidateMatrix_eq_SM3db6R_shapeSeparationMatrix

theorem handoffCandidate_source_eq_SM3db5R_matrixExport
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    H.candidateMatrix i j = M.matrix i j :=
  H.candidateMatrixEntry_eq_SM3db5R_matrixExport i j

theorem handoffCandidate_source_eq_SM3db4aR_accumulatedEntry
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    H.candidateMatrix i j = S.accumulatedInverseCandidateEntry.entry i j :=
  H.candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry i j

theorem noLeftProduct_for_SM3db7R
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    H.noLeftProductStatus = SM3db7RNoLeftProductStatus.noLeftProductInSM3db7RHandoff :=
  H.noLeftProductStatus_eq

theorem noRightProduct_for_SM3db7R
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    H.noRightProductStatus = SM3db7RNoRightProductStatus.noRightProductInSM3db7RHandoff :=
  H.noRightProductStatus_eq

theorem noTwoSidedInv_for_SM3db7R
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    H.noTwoSidedInvStatus = SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff :=
  H.noTwoSidedInvStatus_eq

theorem noInteriorEliminationCertificate_for_SM3db7R
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    H.noInteriorEliminationCertificateStatus =
      SM3db7RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db7RHandoff :=
  H.noInteriorEliminationCertificateStatus_eq

theorem noInteriorEliminationData_for_SM3db7R
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    H.noInteriorEliminationDataStatus =
      SM3db7RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db7RHandoff :=
  H.noInteriorEliminationDataStatus_eq

def regularSM3dbRToSM3eRHandoff
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    SM3dbRToSM3eRHandoff
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp) :=
  sm3dbRToSM3eRHandoff_from_shapeSeparation
    (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)

def variableSM3dbRToSM3eRHandoff
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    SM3dbRToSM3eRHandoff
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp) :=
  sm3dbRToSM3eRHandoff_from_shapeSeparation
    (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)

structure SM3dbRGeneratedInverseCandidateLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3db7RGeneratedInverseCandidateLedgerStatus
  shapeSeparationLedger :
    SM3dbRShapeSeparationLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularHandoff :
    SM3dbRToSM3eRHandoff
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
  variableHandoff :
    SM3dbRToSM3eRHandoff
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
  shapeSeparationLedger_eq_main :
    shapeSeparationLedger =
      sm3dbRShapeSeparationLedger
        b β p regularWeight variableWeight regularPivot variablePivot
  regularHandoff_eq_main :
    regularHandoff = regularSM3dbRToSM3eRHandoff b p regularWeight
  variableHandoff_eq_main :
    variableHandoff = variableSM3dbRToSM3eRHandoff β p variableWeight
  regularCandidateFromSM3db6R :
    regularHandoff.candidateMatrix =
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight).matrix
  variableCandidateFromSM3db6R :
    variableHandoff.candidateMatrix =
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight).matrix
  regularCandidateFromSM3db5R :
    ∀ i j : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p),
      regularHandoff.candidateMatrix i j =
        (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight).matrix i j
  variableCandidateFromSM3db5R :
    ∀ i j : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p),
      variableHandoff.candidateMatrix i j =
        (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight).matrix i j
  regularCandidateFromSM3db4aR :
    ∀ i j : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p),
      regularHandoff.candidateMatrix i j =
        (regularGeneratedInteriorInverseCandidateShapeSeparation
          b p regularWeight).accumulatedInverseCandidateEntry.entry i j
  variableCandidateFromSM3db4aR :
    ∀ i j : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p),
      variableHandoff.candidateMatrix i j =
        (variableGeneratedInteriorInverseCandidateShapeSeparation
          β p variableWeight).accumulatedInverseCandidateEntry.entry i j
  regularMayConsumeOnlyHandoff :
    SM3eRMayConsumeOnlySM3dbRInverseCandidate regularHandoff
  variableMayConsumeOnlyHandoff :
    SM3eRMayConsumeOnlySM3dbRInverseCandidate variableHandoff
  regularNoLeftProduct :
    regularHandoff.noLeftProductStatus =
      SM3db7RNoLeftProductStatus.noLeftProductInSM3db7RHandoff
  variableNoLeftProduct :
    variableHandoff.noLeftProductStatus =
      SM3db7RNoLeftProductStatus.noLeftProductInSM3db7RHandoff
  regularNoRightProduct :
    regularHandoff.noRightProductStatus =
      SM3db7RNoRightProductStatus.noRightProductInSM3db7RHandoff
  variableNoRightProduct :
    variableHandoff.noRightProductStatus =
      SM3db7RNoRightProductStatus.noRightProductInSM3db7RHandoff
  regularNoTwoSidedInv :
    regularHandoff.noTwoSidedInvStatus =
      SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff
  variableNoTwoSidedInv :
    variableHandoff.noTwoSidedInvStatus =
      SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff
  regularNoInteriorEliminationCertificate :
    regularHandoff.noInteriorEliminationCertificateStatus =
      SM3db7RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db7RHandoff
  variableNoInteriorEliminationCertificate :
    variableHandoff.noInteriorEliminationCertificateStatus =
      SM3db7RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db7RHandoff
  regularNoInteriorEliminationData :
    regularHandoff.noInteriorEliminationDataStatus =
      SM3db7RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db7RHandoff
  variableNoInteriorEliminationData :
    variableHandoff.noInteriorEliminationDataStatus =
      SM3db7RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db7RHandoff
  status_eq_closed :
    status =
      SM3db7RGeneratedInverseCandidateLedgerStatus.generatedInverseCandidateHandoffClosed

def sm3dbRGeneratedInverseCandidateLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3dbRGeneratedInverseCandidateLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status := SM3db7RGeneratedInverseCandidateLedgerStatus.generatedInverseCandidateHandoffClosed
  shapeSeparationLedger :=
    sm3dbRShapeSeparationLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularHandoff := regularSM3dbRToSM3eRHandoff b p regularWeight
  variableHandoff := variableSM3dbRToSM3eRHandoff β p variableWeight
  shapeSeparationLedger_eq_main := by
    rfl
  regularHandoff_eq_main := by
    rfl
  variableHandoff_eq_main := by
    rfl
  regularCandidateFromSM3db6R := by
    rfl
  variableCandidateFromSM3db6R := by
    rfl
  regularCandidateFromSM3db5R := by
    intro i j
    exact
      (regularSM3dbRToSM3eRHandoff
        b p regularWeight).candidateMatrixEntry_eq_SM3db5R_matrixExport i j
  variableCandidateFromSM3db5R := by
    intro i j
    exact
      (variableSM3dbRToSM3eRHandoff
        β p variableWeight).candidateMatrixEntry_eq_SM3db5R_matrixExport i j
  regularCandidateFromSM3db4aR := by
    intro i j
    exact
      (regularSM3dbRToSM3eRHandoff
        b p regularWeight).candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry i j
  variableCandidateFromSM3db4aR := by
    intro i j
    exact
      (variableSM3dbRToSM3eRHandoff
        β p variableWeight).candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry i j
  regularMayConsumeOnlyHandoff :=
    (regularSM3dbRToSM3eRHandoff b p regularWeight).consumptionGateStatus_eq
  variableMayConsumeOnlyHandoff :=
    (variableSM3dbRToSM3eRHandoff β p variableWeight).consumptionGateStatus_eq
  regularNoLeftProduct :=
    (regularSM3dbRToSM3eRHandoff b p regularWeight).noLeftProductStatus_eq
  variableNoLeftProduct :=
    (variableSM3dbRToSM3eRHandoff β p variableWeight).noLeftProductStatus_eq
  regularNoRightProduct :=
    (regularSM3dbRToSM3eRHandoff b p regularWeight).noRightProductStatus_eq
  variableNoRightProduct :=
    (variableSM3dbRToSM3eRHandoff β p variableWeight).noRightProductStatus_eq
  regularNoTwoSidedInv :=
    (regularSM3dbRToSM3eRHandoff b p regularWeight).noTwoSidedInvStatus_eq
  variableNoTwoSidedInv :=
    (variableSM3dbRToSM3eRHandoff β p variableWeight).noTwoSidedInvStatus_eq
  regularNoInteriorEliminationCertificate :=
    (regularSM3dbRToSM3eRHandoff b p regularWeight).noInteriorEliminationCertificateStatus_eq
  variableNoInteriorEliminationCertificate :=
    (variableSM3dbRToSM3eRHandoff β p variableWeight).noInteriorEliminationCertificateStatus_eq
  regularNoInteriorEliminationData :=
    (regularSM3dbRToSM3eRHandoff b p regularWeight).noInteriorEliminationDataStatus_eq
  variableNoInteriorEliminationData :=
    (variableSM3dbRToSM3eRHandoff β p variableWeight).noInteriorEliminationDataStatus_eq
  status_eq_closed := by
    rfl

theorem sm3dbRGeneratedInverseCandidateLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3dbRGeneratedInverseCandidateLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3db7RGeneratedInverseCandidateLedgerStatus.generatedInverseCandidateHandoffClosed := by
  rfl

theorem sm3dbRGeneratedInverseCandidateLedger_regularMayConsumeOnlyHandoff
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3eRMayConsumeOnlySM3dbRInverseCandidate
      (sm3dbRGeneratedInverseCandidateLedger
        b β p regularWeight variableWeight regularPivot variablePivot).regularHandoff :=
  (sm3dbRGeneratedInverseCandidateLedger
    b β p regularWeight variableWeight regularPivot variablePivot).regularMayConsumeOnlyHandoff

theorem sm3dbRGeneratedInverseCandidateLedger_regularNoTwoSidedInv
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3dbRGeneratedInverseCandidateLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularHandoff.noTwoSidedInvStatus =
      SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
