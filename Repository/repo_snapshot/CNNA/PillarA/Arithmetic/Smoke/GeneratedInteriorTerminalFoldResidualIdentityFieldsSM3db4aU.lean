import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db4aUTerminalIdentityFieldExposureStatus where
  | terminalIdentityFieldsNotYetDerivedFromCurrentSM3db4aRAPI
  | terminalIdentityFieldsProvidedByExplicitCertificate
  deriving DecidableEq, Repr

inductive SM3db4aUTerminalIdentityFieldSourceStatus where
  | terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  | terminalIdentityFieldSourceCarriedByCertificate
  deriving DecidableEq, Repr

inductive SM3db4aUTerminalFoldInductionEquationStatus where
  | foldInvarianceAvailableButTerminalIdentityEquationMissing
  deriving DecidableEq, Repr

inductive SM3db4aUResidualClosureEquationStatus where
  | residualContributionAvailableButNoIdentityClosureEquation
  deriving DecidableEq, Repr

inductive SM3db4aUFoldOrderCoverageEquationStatus where
  | foldUpdateOrderAvailableButNoIdentityClosureEquation
  deriving DecidableEq, Repr

inductive SM3db4aULeftRightTerminalIdentityStatus where
  | separateLeftAndRightTerminalIdentityFieldsRequired
  deriving DecidableEq, Repr

inductive SM3db4aUTerminalCoverageExportStatus where
  | terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  | terminalCoverageSourcePreparedFromTerminalIdentityFieldCertificate
  deriving DecidableEq, Repr

inductive SM3db4aUNoAccumulatedEntryCancellationStatus where
  | noAccumulatedEntryCancellationInvariantInTerminalIdentityFieldExpose
  deriving DecidableEq, Repr

inductive SM3db4aUNoProductIdentityProofStatus where
  | noProductIdentityProofInTerminalIdentityFieldExpose
  deriving DecidableEq, Repr

inductive SM3db4aUNoTwoSidedInvStatus where
  | noTwoSidedInvInTerminalIdentityFieldExpose
  deriving DecidableEq, Repr

inductive SM3db4aUNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInTerminalIdentityFieldExpose
  deriving DecidableEq, Repr

inductive SM3db4aUNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentityFieldExpose
  deriving DecidableEq, Repr

inductive SM3db4aUNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentityFieldExpose
  deriving DecidableEq, Repr

inductive SM3db4aUNextPhaseStatus where
  | sm3db4aVTerminalFoldResidualIdentityEquationSource
  | sm3eRr3c1dFullTerminalCoverageConsumer
  deriving DecidableEq, Repr

inductive SM3db4aULedgerStatus where
  | terminalIdentityFieldMissingSourceAuditClosed
  | terminalIdentityFieldCertificateReady
  deriving DecidableEq, Repr

structure GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  coverageAudit : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  tracePivotCoverage : GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T
  terminalFoldState : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  terminalResidualContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  terminalFoldUpdateOrderContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  exposureStatus : SM3db4aUTerminalIdentityFieldExposureStatus
  leftTerminalIdentityFieldSourceStatus : SM3db4aUTerminalIdentityFieldSourceStatus
  rightTerminalIdentityFieldSourceStatus : SM3db4aUTerminalIdentityFieldSourceStatus
  terminalFoldInductionEquationStatus : SM3db4aUTerminalFoldInductionEquationStatus
  residualClosureEquationStatus : SM3db4aUResidualClosureEquationStatus
  foldOrderCoverageEquationStatus : SM3db4aUFoldOrderCoverageEquationStatus
  leftRightTerminalIdentityStatus : SM3db4aULeftRightTerminalIdentityStatus
  terminalCoverageExportStatus : SM3db4aUTerminalCoverageExportStatus
  noAccumulatedEntryCancellationStatus : SM3db4aUNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3db4aUNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db4aUNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db4aUNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4aUNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4aUNoArithmeticTargetStatus
  nextPhaseStatus : SM3db4aUNextPhaseStatus
  invariance_eq_coverageAudit : invariance = coverageAudit.invariance
  tracePivotCoverage_eq_coverageAuditRequirement :
    tracePivotCoverage = coverageAudit.requirement.tracePivotCoverage
  terminalFoldState_eq_coverageAudit : terminalFoldState = coverageAudit.terminalFoldState
  terminalResidualContribution_eq_coverageAudit :
    ∀ i j : GeneratedInteriorIndex A,
      terminalResidualContribution i j = coverageAudit.terminalResidualContribution i j
  terminalResidualContribution_eq_trace :
    ∀ i j : GeneratedInteriorIndex A,
      terminalResidualContribution i j = generatedInteriorTraceResidualContribution T i j
  terminalFoldUpdateOrderContribution_eq_coverageAudit :
    ∀ i j : GeneratedInteriorIndex A,
      terminalFoldUpdateOrderContribution i j =
        coverageAudit.terminalFoldUpdateOrderContribution i j
  terminalFoldUpdateOrderContribution_eq_trace :
    ∀ i j : GeneratedInteriorIndex A,
      terminalFoldUpdateOrderContribution i j =
        generatedInteriorTraceFoldUpdateOrderContribution T i j
  coverageAuditLeftIdentityField_missing :
    coverageAudit.leftTerminalIdentityFieldStatus =
      SM3db4aTTerminalIdentityFieldStatus.terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  coverageAuditRightIdentityField_missing :
    coverageAudit.rightTerminalIdentityFieldStatus =
      SM3db4aTTerminalIdentityFieldStatus.terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  coverageAuditExport_blocked :
    coverageAudit.terminalCoverageExportStatus =
      SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  invarianceNoTerminalIdentity_eq :
    invariance.noTerminalIdentityStatus =
      SM3eRr3c1cNoTerminalIdentityStatus.noTerminalIdentityInFoldInvariance
  tracePivotCoverage_source_eq_SM3db3R :
    tracePivotCoverage.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    coverageAudit.accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    coverageAudit.accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  exposureStatus_eq :
    exposureStatus =
      SM3db4aUTerminalIdentityFieldExposureStatus.terminalIdentityFieldsNotYetDerivedFromCurrentSM3db4aRAPI
  leftTerminalIdentityFieldSourceStatus_eq :
    leftTerminalIdentityFieldSourceStatus =
      SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  rightTerminalIdentityFieldSourceStatus_eq :
    rightTerminalIdentityFieldSourceStatus =
      SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  terminalFoldInductionEquationStatus_eq :
    terminalFoldInductionEquationStatus =
      SM3db4aUTerminalFoldInductionEquationStatus.foldInvarianceAvailableButTerminalIdentityEquationMissing
  residualClosureEquationStatus_eq :
    residualClosureEquationStatus =
      SM3db4aUResidualClosureEquationStatus.residualContributionAvailableButNoIdentityClosureEquation
  foldOrderCoverageEquationStatus_eq :
    foldOrderCoverageEquationStatus =
      SM3db4aUFoldOrderCoverageEquationStatus.foldUpdateOrderAvailableButNoIdentityClosureEquation
  leftRightTerminalIdentityStatus_eq :
    leftRightTerminalIdentityStatus =
      SM3db4aULeftRightTerminalIdentityStatus.separateLeftAndRightTerminalIdentityFieldsRequired
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3db4aUNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentityFieldExpose
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db4aUNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentityFieldExpose
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4aUNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentityFieldExpose
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4aUNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentityFieldExpose
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db4aUNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentityFieldExpose
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4aUNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentityFieldExpose
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aUNextPhaseStatus.sm3db4aVTerminalFoldResidualIdentityEquationSource

namespace GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU

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

def fromTerminalFoldResidualCoverageAudit
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T where
  coverageAudit := C
  invariance := C.invariance
  tracePivotCoverage := C.requirement.tracePivotCoverage
  terminalFoldState := C.terminalFoldState
  terminalResidualContribution := C.terminalResidualContribution
  terminalFoldUpdateOrderContribution := C.terminalFoldUpdateOrderContribution
  exposureStatus :=
    SM3db4aUTerminalIdentityFieldExposureStatus.terminalIdentityFieldsNotYetDerivedFromCurrentSM3db4aRAPI
  leftTerminalIdentityFieldSourceStatus :=
    SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  rightTerminalIdentityFieldSourceStatus :=
    SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  terminalFoldInductionEquationStatus :=
    SM3db4aUTerminalFoldInductionEquationStatus.foldInvarianceAvailableButTerminalIdentityEquationMissing
  residualClosureEquationStatus :=
    SM3db4aUResidualClosureEquationStatus.residualContributionAvailableButNoIdentityClosureEquation
  foldOrderCoverageEquationStatus :=
    SM3db4aUFoldOrderCoverageEquationStatus.foldUpdateOrderAvailableButNoIdentityClosureEquation
  leftRightTerminalIdentityStatus :=
    SM3db4aULeftRightTerminalIdentityStatus.separateLeftAndRightTerminalIdentityFieldsRequired
  terminalCoverageExportStatus :=
    SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  noAccumulatedEntryCancellationStatus :=
    SM3db4aUNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentityFieldExpose
  noProductIdentityProofStatus :=
    SM3db4aUNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentityFieldExpose
  noTwoSidedInvStatus :=
    SM3db4aUNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentityFieldExpose
  noInteriorEliminationDataStatus :=
    SM3db4aUNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentityFieldExpose
  noDtnDataStatus :=
    SM3db4aUNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentityFieldExpose
  noArithmeticTargetStatus :=
    SM3db4aUNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentityFieldExpose
  nextPhaseStatus := SM3db4aUNextPhaseStatus.sm3db4aVTerminalFoldResidualIdentityEquationSource
  invariance_eq_coverageAudit := by
    rfl
  tracePivotCoverage_eq_coverageAuditRequirement := by
    rfl
  terminalFoldState_eq_coverageAudit := by
    rfl
  terminalResidualContribution_eq_coverageAudit := by
    intro i j
    rfl
  terminalResidualContribution_eq_trace :=
    C.terminalResidualContribution_eq_trace
  terminalFoldUpdateOrderContribution_eq_coverageAudit := by
    intro i j
    rfl
  terminalFoldUpdateOrderContribution_eq_trace :=
    C.terminalFoldUpdateOrderContribution_eq_trace
  coverageAuditLeftIdentityField_missing :=
    C.leftTerminalIdentityFieldStatus_eq
  coverageAuditRightIdentityField_missing :=
    C.rightTerminalIdentityFieldStatus_eq
  coverageAuditExport_blocked :=
    C.terminalCoverageExportStatus_eq
  invarianceNoTerminalIdentity_eq :=
    C.invariance.noTerminalIdentityStatus_eq
  tracePivotCoverage_source_eq_SM3db3R :=
    C.tracePivotCoverage_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    C.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    C.accumulatedFoldSource_eq_SM3db4aR
  exposureStatus_eq := by
    rfl
  leftTerminalIdentityFieldSourceStatus_eq := by
    rfl
  rightTerminalIdentityFieldSourceStatus_eq := by
    rfl
  terminalFoldInductionEquationStatus_eq := by
    rfl
  residualClosureEquationStatus_eq := by
    rfl
  foldOrderCoverageEquationStatus_eq := by
    rfl
  leftRightTerminalIdentityStatus_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
    rfl
  noAccumulatedEntryCancellationStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromInvariance
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T :=
  fromTerminalFoldResidualCoverageAudit
    (GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT.fromInvariance I)

theorem terminalCoverageSource_still_blocked
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T) :
    A0.terminalCoverageExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate :=
  A0.terminalCoverageExportStatus_eq

theorem nextPhase_is_terminalIdentityEquationSource
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T) :
    A0.nextPhaseStatus = SM3db4aUNextPhaseStatus.sm3db4aVTerminalFoldResidualIdentityEquationSource :=
  A0.nextPhaseStatus_eq

theorem leftIdentityField_source_missing
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T) :
    A0.leftTerminalIdentityFieldSourceStatus =
      SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI :=
  A0.leftTerminalIdentityFieldSourceStatus_eq

theorem rightIdentityField_source_missing
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T) :
    A0.rightTerminalIdentityFieldSourceStatus =
      SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI :=
  A0.rightTerminalIdentityFieldSourceStatus_eq

end GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU

structure GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  coverageAudit : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  exposureStatus : SM3db4aUTerminalIdentityFieldExposureStatus
  terminalCoverageExportStatus : SM3db4aUTerminalCoverageExportStatus
  noAccumulatedEntryCancellationStatus : SM3db4aUNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3db4aUNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db4aUNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db4aUNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4aUNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4aUNoArithmeticTargetStatus
  nextPhaseStatus : SM3db4aUNextPhaseStatus
  invariance_eq_coverageAudit : invariance = coverageAudit.invariance
  leftBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i i = 1
  leftBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorLeftBlockFold W T i j = 0
  rightBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i i = 1
  rightBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorRightBlockFold W T i j = 0
  invarianceStatus_eq :
    invariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  exposureStatus_eq :
    exposureStatus =
      SM3db4aUTerminalIdentityFieldExposureStatus.terminalIdentityFieldsProvidedByExplicitCertificate
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourcePreparedFromTerminalIdentityFieldCertificate
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3db4aUNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentityFieldExpose
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db4aUNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentityFieldExpose
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4aUNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentityFieldExpose
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4aUNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentityFieldExpose
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db4aUNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentityFieldExpose
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4aUNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentityFieldExpose
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aUNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer

namespace GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU

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

def fromCoverageAuditAndIdentityFields
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T)
    (leftIdentity :
      ∀ i j : GeneratedInteriorIndex A,
        generatedInteriorLeftBlockFold W T i j =
          (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j)
    (rightIdentity :
      ∀ i j : GeneratedInteriorIndex A,
        generatedInteriorRightBlockFold W T i j =
          (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j)
    (leftDiagonal :
      ∀ i : GeneratedInteriorIndex A,
        generatedInteriorLeftBlockFold W T i i = 1)
    (leftOffdiag :
      ∀ i j : GeneratedInteriorIndex A,
        i ≠ j → generatedInteriorLeftBlockFold W T i j = 0)
    (rightDiagonal :
      ∀ i : GeneratedInteriorIndex A,
        generatedInteriorRightBlockFold W T i i = 1)
    (rightOffdiag :
      ∀ i j : GeneratedInteriorIndex A,
        i ≠ j → generatedInteriorRightBlockFold W T i j = 0) :
    GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T where
  coverageAudit := C
  invariance := C.invariance
  exposureStatus :=
    SM3db4aUTerminalIdentityFieldExposureStatus.terminalIdentityFieldsProvidedByExplicitCertificate
  terminalCoverageExportStatus :=
    SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourcePreparedFromTerminalIdentityFieldCertificate
  noAccumulatedEntryCancellationStatus :=
    SM3db4aUNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentityFieldExpose
  noProductIdentityProofStatus :=
    SM3db4aUNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentityFieldExpose
  noTwoSidedInvStatus :=
    SM3db4aUNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentityFieldExpose
  noInteriorEliminationDataStatus :=
    SM3db4aUNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentityFieldExpose
  noDtnDataStatus :=
    SM3db4aUNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentityFieldExpose
  noArithmeticTargetStatus :=
    SM3db4aUNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentityFieldExpose
  nextPhaseStatus := SM3db4aUNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer
  invariance_eq_coverageAudit := by
    rfl
  leftBlockFold_eq_identity := leftIdentity
  rightBlockFold_eq_identity := rightIdentity
  leftBlockFold_diagonal := leftDiagonal
  leftBlockFold_offdiag := leftOffdiag
  rightBlockFold_diagonal := rightDiagonal
  rightBlockFold_offdiag := rightOffdiag
  invarianceStatus_eq :=
    C.invarianceStatus_eq
  trace_source_eq_SM3db3R :=
    C.invariance.trace_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    C.invariance.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    C.invariance.accumulatedFoldSource_eq_SM3db4aR
  exposureStatus_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
    rfl
  noAccumulatedEntryCancellationStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem noProductIdentityProof
    (C : GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T) :
    C.noProductIdentityProofStatus =
      SM3db4aUNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentityFieldExpose :=
  C.noProductIdentityProofStatus_eq

theorem noTwoSidedInv
    (C : GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T) :
    C.noTwoSidedInvStatus = SM3db4aUNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentityFieldExpose :=
  C.noTwoSidedInvStatus_eq

end GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU

abbrev RegularGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularTerminalFoldResidualIdentityFieldsAuditSM3db4aU
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : RegularGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT b p wp) :
    RegularGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU b p wp :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU.fromTerminalFoldResidualCoverageAudit C

def variableTerminalFoldResidualIdentityFieldsAuditSM3db4aU
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : VariableGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT β p wp) :
    VariableGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU β p wp :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU.fromTerminalFoldResidualCoverageAudit C

structure SM3db4aUTerminalFoldResidualIdentityFieldsLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAudit : RegularGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU b p regularWeight
  variableAudit : VariableGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU β p variableWeight
  ledgerStatus : SM3db4aULedgerStatus
  regularExportStatus : SM3db4aUTerminalCoverageExportStatus
  variableExportStatus : SM3db4aUTerminalCoverageExportStatus
  nextPhaseStatus : SM3db4aUNextPhaseStatus
  regularExportStatus_eq :
    regularAudit.terminalCoverageExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  variableExportStatus_eq :
    variableAudit.terminalCoverageExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  ledgerStatus_eq :
    ledgerStatus = SM3db4aULedgerStatus.terminalIdentityFieldMissingSourceAuditClosed
  regularExportStatusValue_eq :
    regularExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  variableExportStatusValue_eq :
    variableExportStatus =
      SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aUNextPhaseStatus.sm3db4aVTerminalFoldResidualIdentityEquationSource

namespace SM3db4aUTerminalFoldResidualIdentityFieldsLedger

def fromRegularAndVariableCoverageAudits
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularCoverageAudit : RegularGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT b p regularWeight)
    (variableCoverageAudit : VariableGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT β p variableWeight) :
    SM3db4aUTerminalFoldResidualIdentityFieldsLedger b β p regularWeight variableWeight where
  regularAudit := regularTerminalFoldResidualIdentityFieldsAuditSM3db4aU regularCoverageAudit
  variableAudit := variableTerminalFoldResidualIdentityFieldsAuditSM3db4aU variableCoverageAudit
  ledgerStatus := SM3db4aULedgerStatus.terminalIdentityFieldMissingSourceAuditClosed
  regularExportStatus :=
    SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  variableExportStatus :=
    SM3db4aUTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFieldCertificate
  nextPhaseStatus := SM3db4aUNextPhaseStatus.sm3db4aVTerminalFoldResidualIdentityEquationSource
  regularExportStatus_eq := by
    rfl
  variableExportStatus_eq := by
    rfl
  ledgerStatus_eq := by
    rfl
  regularExportStatusValue_eq := by
    rfl
  variableExportStatusValue_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3db4aUTerminalFoldResidualIdentityFieldsLedger

end Smoke

end CNNA.PillarA.Arithmetic
